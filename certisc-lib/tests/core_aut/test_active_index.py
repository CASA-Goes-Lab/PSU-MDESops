"""
The active-event index: the trusted builder (core_aut/trusted/active_index.py) and the verified
checker check_index (core_aut/verified_core/active_index.py, run stripped of its contracts).
"""

import random

from core_aut import validate
from core_aut.trusted.active_index import _verified, build_active_index

from tests.ops_aut.test_parallel import _random


def _correct(enc, A, H):
    """index_ok, computed directly: the heads of x give its events, increasing, once each."""
    if len(A) != enc.n + 1 or A[0] != 0 or A[-1] != len(H):
        return False
    for x in range(enc.n):
        if not 0 <= A[x] <= A[x + 1] <= len(H):
            return False
        lo, hi = enc.start[x], enc.start[x + 1]
        heads = H[A[x]:A[x + 1]]
        runs = [k for k in range(lo, hi) if k == lo or enc.evt[k] != enc.evt[k - 1]]
        if heads != runs:
            return False
    return True


def test_builder_is_accepted_and_correct():
    rng = random.Random(20)
    for trial in range(300):
        g = _random(rng.randint(1, 8), rng.sample(["a", "b", "c", "d"], rng.randint(1, 4)), rng)
        V = validate(g)
        enc = V._encoding()
        A, H = V._active_index()                     # built and checked on first use
        assert V._active_index() is V._active_index()   # then kept
        assert _correct(enc, list(A), list(H)), trial
        for x in range(enc.n):
            got = [enc.evt[H[i]] for i in range(A[x], A[x + 1])]
            assert got == sorted({enc.evt[k] for k in range(enc.start[x], enc.start[x + 1])})


def test_checker_rejects_wrong_indices():
    rng = random.Random(21)
    rejected = 0
    for trial in range(300):
        g = _random(rng.randint(1, 8), rng.sample(["a", "b", "c", "d"], rng.randint(1, 4)), rng)
        enc = validate(g)._encoding()
        A, H = build_active_index(enc.n, enc.start, enc.evt)
        A2, H2 = list(A), list(H)
        r = rng.random()
        if H2 and r < 0.4:
            H2[rng.randrange(len(H2))] += rng.choice([-1, 1])       # move a head
        elif H2 and r < 0.6:
            H2.pop(rng.randrange(len(H2)))                          # drop a head (A now off)
        elif r < 0.8:
            H2.append(rng.randrange(len(enc.evt) + 1))              # extra head
        else:
            A2[rng.randrange(len(A2))] += rng.choice([-1, 1])       # move a state boundary
        ok = _verified.check_index(enc.n, list(enc.start), list(enc.evt), A2, H2)
        assert ok == _correct(enc, A2, H2), trial                  # accepted exactly if correct
        rejected += not ok
    assert rejected > 200
