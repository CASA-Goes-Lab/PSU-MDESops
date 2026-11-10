"""
Deleting states: the trusted builder (core_aut/trusted/delete_states.py), the verified checker
(src/ops_aut/verified_ops/delete.py, run stripped of its contracts), and the public
delete_states, accessible, coaccessible and trim, against direct constructions over the
Automaton class.
"""

import random
import warnings

import pytest

from core_aut import Automaton, validate
from core_aut.trusted.delete_states import build_delete
from ops_aut import (EmptyAutomatonWarning, accessible, coaccessible, coreachable,
                     delete_states, reachable, trim)
from ops_aut.basic_ops import _verified_delete

from tests.ops_aut.test_parallel import _random


def _expected(g, D):
    """G with the states D deleted, directly: (names, init, marked, transitions as name
    triples), or None when no initial state is kept (the empty automaton)."""
    keep = [x for x in range(g.num_states) if x not in D]
    if not any(x in g.init for x in keep):
        return None
    kept = set(keep)
    names = [g.states[x].name for x in keep]
    init = {g.states[x].name for x in keep if x in g.init}
    marked = {g.states[x].name for x in keep if g.states[x].marked}
    trans = {(g.states[x].name, e, g.states[y].name)
             for x in keep for e, ys in g.states[x].out.items() for y in ys if y in kept}
    return names, init, marked, trans


def _summary(V):
    names = list(V.names)
    return (names, {names[x] for x in V.init}, {names[x] for x in V.marked},
            {(names[x], e, names[y]) for x, e, y in V.transitions()})


def _check(V, dele):
    enc = V._encoding()
    out = build_delete(enc, dele)
    return out, _verified_delete.check_delete(enc.n, enc.start, enc.evt, enc.dst, enc.init,
                                              enc.marked, dele, *out)


def test_delete_states_matches_direct():
    rng = random.Random(60)
    for trial in range(300):
        g = _random(rng.randint(1, 9), rng.sample(["a", "b", "c"], rng.randint(1, 3)), rng)
        V = validate(g)
        D = {rng.randrange(g.num_states) for _ in range(rng.randint(0, 4))}
        exp = _expected(g, D)
        with warnings.catch_warnings(record=True) as w:
            warnings.simplefilter("always")
            R = delete_states(V, sorted(D) + sorted(D))          # repeats are fine
        if exp is None:
            assert R.num_states == 0 and any(x.category is EmptyAutomatonWarning for x in w)
        else:
            assert not w, trial
            assert _summary(R) == exp, trial
            assert R.events == V.events and R.Euc == V.Euc and R.Euo == V.Euo
            if V.is_deterministic:
                assert R.is_deterministic


def test_checker_accepts_builder_and_rejects_mutations():
    rng = random.Random(61)
    rejected = 0
    for trial in range(150):
        g = _random(rng.randint(1, 7), rng.sample(["a", "b", "c"], rng.randint(1, 3)), rng)
        V = validate(g)
        dele = [rng.random() < 0.3 for _ in range(g.num_states)]
        out, ok = _check(V, dele)
        assert ok, trial
        enc = V._encoding()
        # Change one entry of one output list: the checker must reject (each entry is pinned).
        for li, lst in enumerate(out):
            for p in range(len(lst)):
                bad = [list(l) for l in out]
                bad[li][p] = (not lst[p]) if isinstance(lst[p], bool) else lst[p] + 1
                assert not _verified_delete.check_delete(
                    enc.n, enc.start, enc.evt, enc.dst, enc.init, enc.marked, dele, *bad), \
                    (trial, li, p)
                rejected += 1
    assert rejected > 500


def test_accessible_coaccessible_trim():
    rng = random.Random(62)
    for trial in range(300):
        g = _random(rng.randint(1, 9), rng.sample(["a", "b", "c"], rng.randint(1, 3)), rng)
        V = validate(g)
        R, C = set(reachable(V)), set(coreachable(V))
        everything = set(range(g.num_states))
        with warnings.catch_warnings():
            warnings.simplefilter("ignore", EmptyAutomatonWarning)
            for op, keep in ((accessible, R), (coaccessible, C), (trim, R & C)):
                got = op(V)
                exp = _expected(g, everything - keep)
                if exp is None:
                    assert got.num_states == 0, (trial, op.__name__)
                else:
                    assert _summary(got) == exp, (trial, op.__name__)
            # trim really is trim: everything in it is accessible and coaccessible.
            T = trim(V)
            if T.num_states:
                assert set(reachable(T)) == set(range(T.num_states))
                assert set(coreachable(T)) == set(range(T.num_states))


def _machine():
    G = Automaton(events=["start", "finish", "break", "repair", "discard", "install"])
    idle = G.add_state("Idle", marked=True, init=True)
    work = G.add_state("Working")
    down = G.add_state("Down")
    G.add_state("Scrap")
    G.add_state("Spare")
    G.add_transition(idle, "start", work)
    G.add_transition(work, "finish", idle)
    G.add_transition(work, "break", down)
    G.add_transition(down, "repair", idle)
    G.add_transition(down, "discard", 3)
    G.add_transition(4, "install", idle)
    return G


def test_public_examples_and_plain_automaton():
    G = _machine()
    assert accessible(G).names == ("Idle", "Working", "Down", "Scrap")
    assert coaccessible(G).names == ("Idle", "Working", "Down", "Spare")
    assert trim(G).names == ("Idle", "Working", "Down")
    assert G.num_states == 5                             # G is not changed
    assert delete_states(G, [2]).names == ("Idle", "Working", "Scrap", "Spare")


def test_empty_results_warn():
    G = _machine()
    with pytest.warns(EmptyAutomatonWarning):
        assert delete_states(G, [0]).num_states == 0     # the only initial state
    with pytest.warns(EmptyAutomatonWarning):
        assert delete_states(G, range(5)).num_states == 0
    H = Automaton(events=["a"])                          # the initial state is blocking
    H.add_state("x", init=True)
    H.add_state("y", marked=True)
    H.add_transition(1, "a", 1)
    with pytest.warns(EmptyAutomatonWarning):
        assert coaccessible(H).num_states == 0
    with pytest.warns(EmptyAutomatonWarning):
        assert trim(H).num_states == 0
    assert accessible(H).names == ("x",)


def test_errors():
    G = _machine()
    with pytest.raises(ValueError):
        delete_states(G, [5])
    with pytest.raises(ValueError):
        delete_states(G, [-1])
    with pytest.raises(ValueError):
        trim(G, backend="numpy")
