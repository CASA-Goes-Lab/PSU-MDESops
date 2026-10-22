"""
Runtime check of the verified basic operations (src/ops_aut/verified_ops/basic_ops.py) on random automata,
against a direct computation over the Automaton class. Contracts are stripped before running
(see test_parallel.py).
"""

import ast
import random
import types
from pathlib import Path

import ops_aut.verified_ops
from core_aut.encoding import encode, event_table

from tests.ops_aut.test_parallel import _random, _Strip

BASIC = Path(ops_aut.verified_ops.__file__).parent / "basic_ops.py"


def _load_stripped(path, name):
    tree = ast.fix_missing_locations(_Strip().visit(ast.parse(path.read_text())))
    module = types.ModuleType(name)
    exec(compile(tree, str(path), "exec"), module.__dict__)
    return module


ops = _load_stripped(BASIC, "ops_aut.basic_ops_stripped")


def test_next_states_is_the_union_with_witnesses():
    rng = random.Random(5)
    for trial in range(300):
        events = rng.sample(["a", "b", "c"], rng.randint(1, 3))
        g = _random(rng.randint(1, 8), events, rng)
        table = event_table([g])
        enc = encode(g, table)
        S = [rng.randrange(enc.n) for _ in range(rng.randint(0, enc.n + 2))]   # may repeat
        for ev, e in table.items():
            out, src, via, pos = [], [], [], {}
            ops.next_states(enc.n, enc.m, enc.start, enc.evt, enc.dst, enc.in_E, S, e,
                            out, src, via, pos)
            expected = {y for x in S for y in g.states[x].out.get(ev, [])}
            assert set(out) == expected and len(out) == len(expected), (trial, ev)
            assert set(pos) == expected
            for i, y in enumerate(out):           # witnesses and positions
                x, k = S[src[i]], via[i]
                assert enc.start[x] <= k < enc.start[x + 1]
                assert enc.evt[k] == e and enc.dst[k] == y and pos[y] == i


def test_public_next_states():
    from core_aut import Automaton
    from ops_aut import next_states
    rng = random.Random(6)
    for trial in range(200):
        events = rng.sample(["a", "b", "c"], rng.randint(1, 3))
        g = _random(rng.randint(1, 8), events, rng)
        S = [rng.randrange(g.num_states) for _ in range(rng.randint(0, 5))]
        for ev in events + ["z"]:                       # "z": an event with no transition
            expected = {y for x in S for y in g.states[x].out.get(ev, [])}
            out = next_states(g, S, ev)
            assert set(out) == expected and len(out) == len(expected), (trial, ev)
            out2, sources = next_states(g, S, ev, witnesses=True)
            assert out2 == out and all(x in S and y in g.states[x].out[ev]
                                       for x, y in zip(sources, out))
    g = Automaton(events=["a"])
    g.add_state("x0", init=True)
    try:
        next_states(g, [3], "a")
        assert False, "state out of range must raise"
    except ValueError:
        pass


def test_library_runs_without_nagini_installed():
    """The whole public API imports and runs when nagini_contracts is missing (as on CI, which
    installs only the `dev` extra). Guards the runtime stand-ins in verified_core/_contracts.py,
    e.g. PSeq, which verified code uses in type annotations."""
    import subprocess
    import sys
    code = (
        "import sys; sys.modules['nagini_contracts'] = None; "
        "sys.modules['nagini_contracts.contracts'] = None; "
        "sys.modules['nagini_contracts.obligations'] = None\n"
        "from core_aut import Automaton\n"
        "from ops_aut import next_states\n"
        "g = Automaton(events=['a']); g.add_state('x', init=True); g.add_state('y')\n"
        "g.add_transition(0, 'a', 1)\n"
        "print(next_states(g, [0], 'a'))\n"
    )
    out = subprocess.run([sys.executable, "-c", code], capture_output=True, text=True)
    assert out.returncode == 0, out.stderr
    assert out.stdout.strip() == "[1]"
