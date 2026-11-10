"""
The public next_states, active_events and active_events_at (Rust,
rust/verified/src/ops_aut/basic_ops.rs) on random automata, against a direct computation over
the Automaton class.
"""

import random

from tests.random_automata import random_aut as _random


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


def test_public_active_events():
    from ops_aut import active_events
    rng = random.Random(11)
    for trial in range(200):
        events = rng.sample(["a", "b", "c"], rng.randint(1, 3))
        g = _random(rng.randint(1, 8), events, rng)
        S = [rng.randrange(g.num_states) for _ in range(rng.randint(0, 5))]
        expected = {e for x in S for e in g.states[x].out}
        got = active_events(g, S)
        assert set(got) == expected and len(got) == len(expected), trial
        got2, sources = active_events(g, S, witnesses=True)
        assert got2 == got and all(x in S and e in g.states[x].out for e, x in zip(got, sources))


def test_active_events_valid_automaton_and_at():
    """The same results for a ValidAutomaton and for the plain Automaton; active_events_at."""
    from core_aut import validate
    from ops_aut import active_events, active_events_at
    rng = random.Random(12)
    for trial in range(200):
        events = rng.sample(["a", "b", "c", "d"], rng.randint(1, 4))
        g = _random(rng.randint(1, 8), events, rng)
        V = validate(g)
        S = [rng.randrange(g.num_states) for _ in range(rng.randint(0, 5))]
        expected = {e for x in S for e in g.states[x].out}
        got, sources = active_events(V, S, witnesses=True)
        assert set(got) == expected and len(got) == len(expected), trial
        assert all(x in S and e in g.states[x].out for e, x in zip(got, sources))
        x = rng.randrange(g.num_states)
        assert sorted(active_events_at(V, x)) == sorted(g.states[x].out), trial
        assert sorted(active_events_at(g, x)) == sorted(g.states[x].out), trial
