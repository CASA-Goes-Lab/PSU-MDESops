"""
Coreachability: the public ops_aut.coreachable (Rust, rust/verified/src/ops_aut/reach.rs), against
a direct backward search over the Automaton class.
"""

import random
from collections import deque

import pytest

from core_aut import validate
from ops_aut import coreachable

from tests.random_automata import random_aut as _random


def _dist_to(g, X):
    """Distance from each coreachable state to X (backward BFS over the Automaton class)."""
    pred = {}
    for x in range(g.num_states):
        for targets in g.states[x].out.values():
            for y in targets:
                pred.setdefault(y, set()).add(x)
    dist, queue = {x: 0 for x in X}, deque(X)
    while queue:
        y = queue.popleft()
        for x in pred.get(y, ()):
            if x not in dist:
                dist[x] = dist[y] + 1
                queue.append(x)
    return dist


def test_public_coreachable():
    rng = random.Random(51)
    for trial in range(200):
        g = _random(rng.randint(1, 9), rng.sample(["a", "b", "c"], rng.randint(1, 3)), rng)
        marked = [x for x in range(g.num_states) if g.states[x].marked]
        assert set(coreachable(g)) == set(_dist_to(g, marked)), trial     # default: marked
        V = validate(g)
        X = [rng.randrange(g.num_states) for _ in range(rng.randint(0, 3))]
        got, nexts = coreachable(V, X, witnesses=True)
        assert set(got) == set(_dist_to(g, X)) and len(got) == len(set(got)), trial
        at = {x: i for i, x in enumerate(got)}
        for x, w in zip(got, nexts):                # each witness is a real transition onward
            if w is None:
                assert x in X
            else:
                e, y = w
                assert at[y] < at[x] and y in g.states[x].out[e]


def test_witness_words_are_shortest():
    """Breadth-first from the targets: following the nexts gives a shortest word to a target."""
    rng = random.Random(52)
    for trial in range(200):
        g = _random(rng.randint(1, 9), rng.sample(["a", "b", "c"], rng.randint(1, 3)), rng)
        X = [rng.randrange(g.num_states) for _ in range(rng.randint(1, 3))]
        dist = _dist_to(g, X)
        states, nexts = coreachable(g, X, witnesses=True)
        nxt = dict(zip(states, nexts))
        for x in states:
            word, z = [], x
            while nxt[z] is not None:
                e, z = nxt[z]
                word.append(e)
            assert z in X and len(word) == dist[x], trial


def test_coreachable_errors():
    g = _random(3, ["a"], random.Random(0))
    with pytest.raises(ValueError):
        coreachable(g, [5])
    with pytest.raises(ValueError):
        coreachable(g, backend="numpy")
