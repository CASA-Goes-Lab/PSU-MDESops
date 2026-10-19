"""
Runtime check of the verified parallel core (DESops/verified/parallel.py) against
d.composition.parallel, on random automata (NFA, several initial states, shared and private
events, empty automata).

The core's contract statements must be stripped before it runs (Old(...) is None at runtime).
Until stripping at import exists in the library, `_load_stripped` below does it: the same
transform the library will use (drop statement-level contract calls, nothing else).
"""

import ast
import random
import types
from pathlib import Path

import DESops as d
import DESops.verified  # noqa: F401  (no-op contract functions)
from DESops.verified.encoding import Encoded, decode, encode, event_table

CORE = Path(DESops.verified.__file__).parent / "parallel.py"
CONTRACTS = {"Requires", "Ensures", "Invariant", "Assert", "Assume", "Fold", "Unfold", "Decreases"}


class _Strip(ast.NodeTransformer):
    """Drop statement-level contract calls; keep everything else."""

    def visit_Expr(self, node):
        call = node.value
        if (isinstance(call, ast.Call) and isinstance(call.func, ast.Name)
                and call.func.id in CONTRACTS):
            return None
        return node

    def generic_visit(self, node):
        super().generic_visit(node)
        body = getattr(node, "body", None)
        if isinstance(body, list) and not body:
            body.append(ast.Pass())
        return node


def _load_stripped():
    tree = ast.fix_missing_locations(_Strip().visit(ast.parse(CORE.read_text())))
    module = types.ModuleType("DESops.verified.parallel_stripped")
    exec(compile(tree, str(CORE), "exec"), module.__dict__)
    return module


core = _load_stripped()


def verified_parallel(g1, g2):
    table = event_table([g1, g2])
    a, b = encode(g1, table), encode(g2, table)
    p1, p2, index, ostart, oevt, odst = [], [], {}, [], [], []
    r = core.parallel_core(a.n, b.n, len(table), a.init, a.start, a.evt, a.dst, a.in_E,
                           b.init, b.start, b.evt, b.dst, b.in_E,
                           p1, p2, index, ostart, oevt, odst)
    assert r == 0
    n, m = len(p1), len(table)
    # Initial states and marking are not produced by the core yet (P2, P5): rebuilt here.
    n_init = sum(a.init) * sum(b.init)
    enc = Encoded(n, m, [a.in_E[e] or b.in_E[e] for e in range(m)], [False] * m, [False] * m,
                  [i < n_init for i in range(n)],
                  [a.marked[p1[i]] and b.marked[p2[i]] for i in range(n)],
                  ostart, oevt, odst)
    names = [(g1.states[p1[i]].name, g2.states[p2[i]].name) for i in range(n)]
    return decode(enc, list(table), names)


def _random(n, events, rng):
    g = d.Automaton(events=events)
    n_init = min(n, rng.randint(1, 2))
    for i in range(n):
        g.add_state(f"s{i}", rng.random() < 0.4, init=i < n_init)
    for x in range(n):
        for e in events:
            if rng.random() < 0.5:
                g.add_transition(x, e, rng.randrange(n))
                if rng.random() < 0.15:          # a second target: nondeterministic
                    g.add_transition(x, e, rng.randrange(n))
    return g


def _view(g):
    names = [s.name for s in g.states]
    return (
        {(names[s], e, names[t]) for s, e, t in g.transitions()},
        {names[x] for x in g.init},
        {s.name for s in g.states if s.marked},
        g.num_states,
    )


def test_core_matches_parallel_on_random_automata():
    rng = random.Random(7)
    E = d.Event
    for trial in range(150):
        g1 = _random(rng.randint(0, 6),
                     rng.sample([E("a"), E("b"), E("c"), E("s")], rng.randint(1, 4)), rng)
        g2 = _random(rng.randint(0, 6), rng.sample([E("c"), E("d"), E("s")], rng.randint(1, 3)),
                     rng)
        assert _view(verified_parallel(g1, g2)) == _view(d.composition.parallel(g1, g2)), trial


def test_stripping_removes_only_contract_statements():
    tree = _Strip().visit(ast.parse(CORE.read_text()))
    calls = {n.value.func.id for n in ast.walk(tree)
             if isinstance(n, ast.Expr) and isinstance(n.value, ast.Call)
             and isinstance(n.value.func, ast.Name)}
    assert not calls & CONTRACTS
    names = {n.name for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)}
    assert {"parallel_core", "expand", "get_or_add", "lookup", "add", "emit"} <= names
