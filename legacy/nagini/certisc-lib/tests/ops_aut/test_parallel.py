"""
Runtime check of the verified parallel core (src/ops_aut/verified_ops/parallel.py) on random automata (NFA,
several initial states, shared and private events, empty automata).

The check is local: each output state (x1, x2) has exactly the transitions of one synchronous
step from (x1, x2), and the initial pairs come first. This is the property the Nagini proof is
to establish (certisc-proof/spec/parallel.md); Lean lifts it to the languages.

The core's contract statements must be stripped before it runs (Old(...) is None at runtime).
Until stripping at import exists in the library, `_load_stripped` below does it: the same
transform the library will use (drop statement-level contract calls, nothing else).
"""

import ast
import random
import types
from pathlib import Path

import ops_aut.verified_ops
from core_aut import Automaton
from core_aut.trusted.encoding import encode, event_table

CORE = Path(ops_aut.verified_ops.__file__).parent / "parallel.py"
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
    module = types.ModuleType("ops_aut.parallel_stripped")
    exec(compile(tree, str(CORE), "exec"), module.__dict__)
    return module


core = _load_stripped()


def run_core(g1, g2):
    """Encode g1, g2 with one event table and run the stripped core."""
    table = event_table([g1, g2])
    a, b = encode(g1, table), encode(g2, table)
    p1, p2, index, ostart, oevt, odst = [], [], {}, [], [], []
    r = core.parallel_core(a.n, b.n, len(table), a.init, a.start, a.evt, a.dst, a.in_E,
                           b.init, b.start, b.evt, b.dst, b.in_E,
                           p1, p2, index, ostart, oevt, odst)
    assert r == 0
    return a, b, p1, p2, ostart, oevt, odst


def _moves(enc, x):
    """{(event, target)} of state x in an encoded automaton."""
    return {(enc.evt[k], enc.dst[k]) for k in range(enc.start[x], enc.start[x + 1])}


def sync_step(a, b, x1, x2):
    """{(event, (y1, y2))}: one synchronous step of G1 || G2 from (x1, x2)."""
    out = set()
    for e, y1 in _moves(a, x1):
        if b.in_E[e]:
            out |= {(e, (y1, y2)) for f, y2 in _moves(b, x2) if f == e}
        else:
            out.add((e, (y1, x2)))
    out |= {(f, (x1, y2)) for f, y2 in _moves(b, x2) if not a.in_E[f]}
    return out


def _random(n, events, rng):
    g = Automaton(events=events)
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


def test_core_is_one_sync_step_per_state():
    rng = random.Random(7)
    for trial in range(300):
        g1 = _random(rng.randint(0, 6), rng.sample(["a", "b", "c", "s"], rng.randint(1, 4)), rng)
        g2 = _random(rng.randint(0, 6), rng.sample(["c", "d", "s"], rng.randint(1, 3)), rng)
        a, b, p1, p2, ostart, oevt, odst = run_core(g1, g2)
        pairs = list(zip(p1, p2))
        assert len(set(pairs)) == len(pairs), trial                     # no duplicate states
        inits = [(x1, x2) for x1 in range(a.n) if a.init[x1] for x2 in range(b.n) if b.init[x2]]
        assert pairs[:len(inits)] == inits, trial                       # initial pairs first
        for i, (x1, x2) in enumerate(pairs):
            got = {(oevt[k], pairs[odst[k]]) for k in range(ostart[i], ostart[i + 1])}
            assert got == sync_step(a, b, x1, x2), (trial, i)


def test_stripping_removes_only_contract_statements():
    tree = _Strip().visit(ast.parse(CORE.read_text()))
    calls = {n.value.func.id for n in ast.walk(tree)
             if isinstance(n, ast.Expr) and isinstance(n.value, ast.Call)
             and isinstance(n.value.func, ast.Name)}
    assert not calls & CONTRACTS
    names = {n.name for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)}
    assert {"parallel_core", "expand", "get_or_add", "lookup", "add", "emit"} <= names
