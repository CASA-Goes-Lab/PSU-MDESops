"""
Reachability: the verified core (src/ops_aut/verified_ops/reach.py, run stripped of its
contracts) and the public ops_aut.reachable, against a direct search over the Automaton class.
"""

import random
from collections import deque

import pytest

from core_aut import validate
from ops_aut import reachable
from ops_aut.reach import _verified

from tests.ops_aut.test_parallel import _random


def _bfs(g, S):
    """Reachable states, directly over the Automaton class."""
    seen, queue = set(S), deque(S)
    while queue:
        x = queue.popleft()
        for targets in g.states[x].out.values():
            for y in targets:
                if y not in seen:
                    seen.add(y)
                    queue.append(y)
    return seen


def test_core_is_reach_with_witnesses():
    rng = random.Random(30)
    for trial in range(300):
        g = _random(rng.randint(1, 9), rng.sample(["a", "b", "c"], rng.randint(1, 3)), rng)
        enc = validate(g)._encoding()
        S = [rng.randrange(enc.n) for _ in range(rng.randint(0, 3))]       # may repeat
        mark, out, par, via = [-1] * enc.n, [], [], []
        _verified.reachable(enc.n, enc.start, enc.dst, S, mark, out, par, via)
        expected = _bfs(g, S)
        assert set(out) == expected and len(out) == len(expected), trial
        for i, y in enumerate(out):                 # the four proved properties, at runtime
            assert mark[y] == i
            if par[i] == -1:
                assert S[via[i]] == y
            else:
                x = out[par[i]]
                assert par[i] < i and enc.start[x] <= via[i] < enc.start[x + 1]
                assert enc.dst[via[i]] == y
        assert all(mark[y] == -1 for y in range(enc.n) if y not in expected)


def test_public_reachable():
    rng = random.Random(31)
    for trial in range(200):
        g = _random(rng.randint(1, 9), rng.sample(["a", "b", "c"], rng.randint(1, 3)), rng)
        init = [x for x in range(g.num_states) if x in g.init]
        assert set(reachable(g)) == _bfs(g, init), trial                  # default: initial
        V = validate(g)
        S = [rng.randrange(g.num_states) for _ in range(rng.randint(0, 3))]
        got, parents = reachable(V, S, witnesses=True)
        assert set(got) == _bfs(g, S) and len(got) == len(set(got)), trial
        pos = {y: i for i, y in enumerate(got)}
        for y, par in zip(got, parents):            # each parent is a real, earlier transition
            if par is None:
                assert y in S
            else:
                x, e = par
                assert pos[x] < pos[y] and y in g.states[x].out[e]


def test_witness_words_are_shortest():
    """Breadth-first: following the parents back gives a word of the shortest length."""
    rng = random.Random(32)
    for trial in range(200):
        g = _random(rng.randint(1, 9), rng.sample(["a", "b", "c"], rng.randint(1, 3)), rng)
        S = [rng.randrange(g.num_states) for _ in range(rng.randint(1, 3))]
        dist, queue = {x: 0 for x in S}, deque(S)            # BFS distances
        while queue:
            x = queue.popleft()
            for targets in g.states[x].out.values():
                for y in targets:
                    if y not in dist:
                        dist[y] = dist[x] + 1
                        queue.append(y)
        states, parents = reachable(g, S, witnesses=True)
        parent = dict(zip(states, parents))
        for y in states:
            word, z = [], y
            while parent[z] is not None:
                z, e = parent[z]
                word.append(e)
            assert z in S and len(word) == dist[y], trial


def test_reachable_errors():
    g = _random(3, ["a"], random.Random(0))
    with pytest.raises(ValueError):
        reachable(g, [5])
    with pytest.raises(ValueError):
        reachable(g, backend="numpy")
