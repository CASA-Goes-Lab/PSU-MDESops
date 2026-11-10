"""Random automata for the tests."""

import random

from core_aut import Automaton, validate


def rand_aut(rng, n, events, density, p_init=0.3, p_mark=0.4, det=False):
    """A random Automaton: n states, transitions on each event with probability `density`
    (one or two targets unless det), random Euc, Euo, initial and marked states."""
    G = Automaton(events=events, Euc=[e for e in events if rng.random() < 0.3],
                  Euo=[e for e in events if rng.random() < 0.3])
    for i in range(n):
        G.add_state(str(i), rng.random() < p_mark, init=False)
    if n:
        inits = [i for i in range(n) if rng.random() < p_init] or [0]
        G.init = {inits[0]} if det else set(inits)
    for x in range(n):
        for e in events:
            if rng.random() < density:
                for _ in range(1 if det else rng.choice([1, 1, 2])):
                    G.add_transition(x, e, rng.randrange(n))
    return G


def random_aut(n, events, rng):
    """A random Automaton: states s0..s{n-1}, one or two initial states, each state marked with
    probability 0.4, a transition on each event with probability 0.5 (sometimes two targets)."""
    G = Automaton(events=events)
    n_init = min(n, rng.randint(1, 2))
    for i in range(n):
        G.add_state(f"s{i}", rng.random() < 0.4, init=i < n_init)
    for x in range(n):
        for e in events:
            if rng.random() < 0.5:
                G.add_transition(x, e, rng.randrange(n))
                if rng.random() < 0.15:          # a second target: nondeterministic
                    G.add_transition(x, e, rng.randrange(n))
    return G


def random_valid(seed):
    """(rng, V): a random ValidAutomaton with 0-12 states, and the generator for more choices."""
    rng = random.Random(seed)
    events = rng.sample(list("abcdefgh"), rng.randint(1, 6))
    det = rng.random() < 0.3
    G = rand_aut(rng, rng.randint(0, 12), events, rng.random() * 0.5, det=det)
    return rng, validate(G)


def lists(enc):
    """The encoding as the argument tuple of RsAut.from_lists (and of Encoded)."""
    return (enc.n, enc.m, list(enc.in_E), list(enc.in_Euc), list(enc.in_Euo), list(enc.init),
            list(enc.marked), list(enc.start), list(enc.evt), list(enc.dst))
