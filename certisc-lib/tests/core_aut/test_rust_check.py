"""The Verus-verified Rust checker (core_aut._rs, check_code) on random valid encodings and
random corruptions of them, against `reference_code` below: the conditions of the spec
(certisc-proof/spec/automaton.md section 3) written directly in Python, in the checker's order.

(Until 2026-11-10 it was compared with the Nagini-verified checker, now in legacy/nagini/: the
codes were equal on 20 000 corrupted encodings.)"""

import pytest

from core_aut import Automaton, InvalidAutomatonError, check_or_raise, validate
from core_aut._rs import RsAut
from core_aut.trusted.encoding import Encoded
from core_aut.trusted.wrapper import to_rust
from tests.random_automata import lists, random_valid

SEEDS = range(300)


def reference_code(t, deterministic):
    """The checker's code for the lists t, computed directly (not verified): 0 if valid, else
    the first failing condition in the order sizes (1), blocks (2), sorted (8), transitions (3),
    events (4), initial states (5), then, if deterministic, one initial state (6) and one
    transition per event (7)."""
    n, m, in_e, in_euc, in_euo, init, marked, start, evt, dst = t
    T = len(evt)
    if not (len(in_e) == len(in_euc) == len(in_euo) == m and len(init) == len(marked) == n
            and len(start) == n + 1 and len(dst) == T):
        return 1
    if start[0] != 0 or start[n] != T or any(start[x] > start[x + 1] for x in range(n)):
        return 2
    blocks = [evt[start[x]:start[x + 1]] for x in range(n)]
    if any(b != sorted(b) for b in blocks):
        return 8
    if any(not (evt[k] < m and in_e[evt[k]] and dst[k] < n) for k in range(T)):
        return 3
    if any((in_euc[e] or in_euo[e]) and not in_e[e] for e in range(m)):
        return 4
    if (n > 0) != any(init):
        return 5
    if deterministic:
        if sum(init) > 1:
            return 6
        if any(len(set(b)) < len(b) for b in blocks):
            return 7
    return 0


def corrupt(rng, t):
    """One random change to valid lists (it may or may not keep them valid)."""
    n, m, in_e, in_euc, in_euo, init, marked, start, evt, dst = [
        list(x) if isinstance(x, list) else x for x in t]
    kind = rng.randrange(9)
    if kind == 0 and evt:
        evt[rng.randrange(len(evt))] = rng.randrange(m + 2)
    elif kind == 1 and dst:
        dst[rng.randrange(len(dst))] = rng.randrange(n + 2)
    elif kind == 2 and len(start) > 1:
        start[rng.randrange(len(start))] = rng.randrange(len(evt) + 2)
    elif kind == 3 and init:
        init = [False] * n if rng.random() < 0.5 else [True] * n
    elif kind == 4 and m:
        k = rng.randrange(m)
        in_e[k] = not in_e[k]
    elif kind == 5 and m:
        k = rng.randrange(m)
        in_euc[k] = not in_euc[k]
    elif kind == 6:
        marked = marked + [False]
    elif kind == 7 and len(evt) > 1:
        i = rng.randrange(len(evt) - 1)
        evt[i], evt[i + 1] = evt[i + 1], evt[i]
    elif kind == 8:
        n = n + 1
    return (n, m, in_e, in_euc, in_euo, init, marked, start, evt, dst)


def test_round_trip():
    """Lists -> Rust -> lists gives the same lists."""
    for seed in SEEDS:
        _, V = random_valid(seed)
        t = lists(V._encoding())
        assert RsAut.from_lists(*t).to_lists() == t, seed


def test_checker_agrees_with_reference():
    """3000 corrupted encodings (10 per seed): the same code as the reference, every time."""
    for seed in SEEDS:
        rng, V = random_valid(seed)
        base = lists(V._encoding())
        for _ in range(10):
            t = corrupt(rng, base)
            R, code = to_rust(Encoded(*t))
            assert code == reference_code(t, False), (seed, t)
            if code == 0:
                assert R.det_code == reference_code(t, True), (seed, t)
                assert R.is_deterministic == (R.det_code == 0)


def test_messages():
    G = Automaton(events=["a"])
    G.add_state("x")                         # states but no initial state (W3): code 5
    with pytest.raises(InvalidAutomatonError, match="initial"):
        validate(G)
    G.init = {0}
    G.add_state("y")
    G.add_transition(0, "a", 0)
    G.add_transition(0, "a", 1)              # two moves on "a": valid, not deterministic
    check_or_raise(G)
    with pytest.raises(InvalidAutomatonError, match="same event"):
        check_or_raise(G, deterministic=True)
    with pytest.raises(InvalidAutomatonError, match="same event"):
        validate(G, deterministic=True)


def test_bad_state_index():
    _, V = random_valid(3)
    with pytest.raises(ValueError):
        V._rs.reachable([V.num_states])
    with pytest.raises(ValueError):
        V._rs.delete_states([False] * (V.num_states + 1))
