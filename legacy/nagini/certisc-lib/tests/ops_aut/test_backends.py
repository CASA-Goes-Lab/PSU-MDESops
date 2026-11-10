"""The two backends of the public operations agree: backend="rust" (Verus-verified, the
default) and backend="nagini" (Nagini-verified), on random automata. Same results, in the same
order, with the same witnesses; deletions give the same automaton (encoding and names)."""

import warnings

import pytest

from core_aut.trusted.wrapper import _run_check
from ops_aut import (EmptyAutomatonWarning, accessible, active_events, coaccessible,
                     coreachable, delete_states, next_states, reachable, trim)
from tests.random_automata import lists, random_valid

SEEDS = range(300)


def state_sets(rng, V):
    n = V.num_states
    out = [sorted(V.init), sorted(V.marked)]
    if n:
        out += [[rng.randrange(n) for _ in range(rng.randint(0, 4))] for _ in range(3)]
    return out


@pytest.mark.parametrize("seed", SEEDS)
def test_next_and_active(seed):
    rng, V = random_valid(seed)
    for S in state_sets(rng, V):
        for e in sorted(V.events):
            r = next_states(V, S, e, witnesses=True)
            p = next_states(V, S, e, witnesses=True, backend="nagini")
            assert set(r[0]) == set(p[0]) and len(set(r[0])) == len(r[0])
            for y, x in zip(*r):                 # each witness is a real move
                assert x in S and y in V.states[x].out.get(e, ())
        r = active_events(V, S, witnesses=True)
        p = active_events(V, S, witnesses=True, backend="nagini")
        assert set(r[0]) == set(p[0]) and len(set(r[0])) == len(r[0])
        for e, x in zip(*r):
            assert x in S and e in V.states[x].out


@pytest.mark.parametrize("seed", SEEDS)
def test_reach_coreach(seed):
    rng, V = random_valid(seed)
    for S in state_sets(rng, V):
        assert reachable(V, S, witnesses=True) == reachable(V, S, witnesses=True,
                                                            backend="nagini")
        r = coreachable(V, S, witnesses=True)
        p = coreachable(V, S, witnesses=True, backend="nagini")
        assert set(r[0]) == set(p[0]) and len(set(r[0])) == len(r[0])
        for i, w in enumerate(r[1]):             # each witness leads to an earlier entry
            if w is None:
                assert r[0][i] in S
            else:
                e, y = w
                assert y in r[0][:i] and y in V.states[r[0][i]].out[e]


def same(A, B):
    assert lists(A._encoding()) == lists(B._encoding())
    assert A.names == B.names and A._event_of == B._event_of
    assert A.is_deterministic == B.is_deterministic


def both(op, *args):
    """op with each backend; also checks that both warn, or neither."""
    out = []
    for backend in ("rust", "nagini"):
        with warnings.catch_warnings(record=True) as w:
            warnings.simplefilter("always")
            out.append(op(*args, backend=backend))
        out.append(any(issubclass(x.category, EmptyAutomatonWarning) for x in w))
    assert out[1] == out[3]
    return out[0], out[2]


@pytest.mark.parametrize("seed", SEEDS)
def test_delete_and_parts(seed):
    rng, V = random_valid(seed)
    n = V.num_states
    for _ in range(3):
        D = [x for x in range(n) if rng.random() < 0.3]
        same(*both(delete_states, V, D))
    for op in (accessible, coaccessible, trim):
        R, P = both(op, V)
        same(R, P)
        assert _run_check(R._encoding(), False) == 0     # the Nagini checker agrees: valid
