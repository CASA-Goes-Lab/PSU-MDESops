"""
The reverse index: the trusted builder (core_aut/trusted/reverse_index.py) and the verified
checker check_reverse (core_aut/verified_core/reverse_index.py, run stripped of its contracts).
"""

import random

from core_aut import validate
from core_aut.trusted.reverse_index import _verified, build_reverse_index

from tests.ops_aut.test_parallel import _random


def _correct(enc, rstart, rk, rsrc, pos):
    """The four facts and the block structure, computed directly."""
    n, T = enc.n, len(enc.dst)
    if len(rstart) != n + 1 or rstart[0] != 0 or rstart[-1] != T:
        return False
    if not (len(rk) == len(rsrc) == len(pos) == T):
        return False
    owner = {k: x for x in range(n) for k in range(enc.start[x], enc.start[x + 1])}
    for y in range(n):
        if not 0 <= rstart[y] <= rstart[y + 1] <= T:
            return False
        for j in range(rstart[y], rstart[y + 1]):
            k = rk[j]
            if not (0 <= k < T and owner[k] == rsrc[j] and enc.dst[k] == y):
                return False
    return all(0 <= pos[k] < T and rk[pos[k]] == k for k in range(T))


def test_builder_is_accepted_and_correct():
    rng = random.Random(40)
    for trial in range(300):
        g = _random(rng.randint(1, 8), rng.sample(["a", "b", "c", "d"], rng.randint(1, 4)), rng)
        V = validate(g)
        enc = V._encoding()
        idx = V._reverse_index()                       # built and checked on first use
        assert V._reverse_index() is idx               # then kept
        assert _correct(enc, *idx), trial
        rstart, rk, rsrc, _ = idx
        for y in range(enc.n):                         # rblock(y) = the transitions into y
            into = sorted(k for k in range(len(enc.dst)) if enc.dst[k] == y)
            assert sorted(rk[rstart[y]:rstart[y + 1]]) == into


def test_checker_rejects_wrong_indices():
    rng = random.Random(41)
    rejected = 0
    for trial in range(400):
        g = _random(rng.randint(1, 8), rng.sample(["a", "b", "c", "d"], rng.randint(1, 4)), rng)
        enc = validate(g)._encoding()
        bad = [list(a) for a in build_reverse_index(enc.n, enc.start, enc.dst)]
        T = len(enc.dst)
        r = rng.random()
        if T and r < 0.25:
            bad[1][rng.randrange(T)] = rng.randrange(T)          # wrong transition in rk
        elif T and r < 0.5:
            bad[2][rng.randrange(T)] = rng.randrange(enc.n)      # wrong source in rsrc
        elif T and r < 0.75:
            bad[3][rng.randrange(T)] = rng.randrange(T)          # wrong inverse in pos
        else:
            bad[0][rng.randrange(len(bad[0]))] += rng.choice([-1, 1])   # move a boundary
        ok = _verified.check_reverse(enc.n, list(enc.start), list(enc.dst), *bad)
        assert ok == _correct(enc, *bad), trial        # accepts exactly the correct ones
        rejected += not ok
    assert rejected > 100                              # the mutations were mostly real
