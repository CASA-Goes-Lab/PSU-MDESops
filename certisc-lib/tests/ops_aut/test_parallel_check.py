"""
Runtime check of the verified soundness checker (src/ops_aut/verified_ops/parallel_check.py): it accepts the
output of the parallel core, and rejects outputs with a corrupted transition target.

Both modules run with their contract statements stripped (see test_parallel.py).
"""

import ast
import random
import types
from pathlib import Path

import ops_aut.verified_ops
from core_aut.trusted.encoding import event_table

from tests.ops_aut.test_parallel import _random, _Strip, run_core

CHECK = Path(ops_aut.verified_ops.__file__).parent / "parallel_check.py"


def _load_stripped(path, name):
    tree = ast.fix_missing_locations(_Strip().visit(ast.parse(path.read_text())))
    module = types.ModuleType(name)
    exec(compile(tree, str(path), "exec"), module.__dict__)
    return module


chk = _load_stripped(CHECK, "ops_aut.parallel_check_stripped")


def check(a, b, m, p1, p2, ostart, oevt, odst):
    ostate, osrc1, osrc2 = [], [], []
    ok = chk.check_sound(a.n, b.n, m, a.start, a.evt, a.dst, a.in_E, b.start, b.evt, b.dst,
                         b.in_E, p1, p2, ostart, oevt, odst, ostate, osrc1, osrc2)
    return ok, ostate, osrc1, osrc2


def test_accepts_core_output_and_records_witnesses():
    rng = random.Random(3)
    for trial in range(300):
        g1 = _random(rng.randint(0, 6), rng.sample(["a", "b", "c", "s"], rng.randint(1, 4)), rng)
        g2 = _random(rng.randint(0, 6), rng.sample(["c", "d", "s"], rng.randint(1, 3)), rng)
        a, b, p1, p2, ostart, oevt, odst = run_core(g1, g2)
        ok, ostate, osrc1, osrc2 = check(a, b, len(event_table([g1, g2])), p1, p2, ostart,
                                         oevt, odst)
        assert ok, trial
        assert len(ostate) == len(osrc1) == len(osrc2) == len(oevt)
        for k in range(len(oevt)):                       # the witnesses describe the move
            i = ostate[k]
            assert ostart[i] <= k < ostart[i + 1]
            if osrc1[k] >= 0:
                assert a.evt[osrc1[k]] == oevt[k] and a.dst[osrc1[k]] == p1[odst[k]]
            else:
                assert p1[odst[k]] == p1[i] and not a.in_E[oevt[k]]


def test_rejects_corrupted_target():
    rng = random.Random(4)
    tried = rejected = 0
    for trial in range(300):
        g1 = _random(rng.randint(1, 6), rng.sample(["a", "b", "c", "s"], rng.randint(1, 4)), rng)
        g2 = _random(rng.randint(1, 6), rng.sample(["c", "d", "s"], rng.randint(1, 3)), rng)
        a, b, p1, p2, ostart, oevt, odst = run_core(g1, g2)
        if not odst:
            continue
        k = rng.randrange(len(odst))
        bad = list(odst)
        bad[k] = (bad[k] + 1) % len(p1)
        if (p1[bad[k]], p2[bad[k]]) == (p1[odst[k]], p2[odst[k]]):
            continue
        tried += 1
        rejected += not check(a, b, len(event_table([g1, g2])), p1, p2, ostart, oevt, bad)[0]
    assert tried > 50 and rejected == tried
