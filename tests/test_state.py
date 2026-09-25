"""
Tests for DESops.core.state: the State/Transition working representation
used inside native (pure Python, no igraph) operation implementations.
See DESops/core/state.py's module docstring and
doc/logs/v2-igraph-decoupling.md for what this is (and isn't) for.
"""

import DESops as d
from DESops.core.state import State, Transition, populate_incoming, states_from_data


# --- State / Transition, standalone --------------------------------------


def test_add_transition_updates_both_endpoints():
    s0 = State(0, "s0")
    s1 = State(1, "s1")

    t = s0.add_transition(s1, d.Event("a"))

    assert s0.out == [Transition(1, d.Event("a"))]
    assert s1.incoming == [Transition(0, d.Event("a"))]
    assert t.index == 1 and t.label == d.Event("a")


def test_add_transition_with_prob():
    s0 = State(0, "s0")
    s1 = State(1, "s1")
    s0.add_transition(s1, d.Event("a"), prob=0.5)
    assert s0.out[0].prob == 0.5
    assert s1.incoming[0].prob == 0.5


def test_transition_unpacks_like_a_tuple():
    s0 = State(0, "s0")
    s1 = State(1, "s1")
    s0.add_transition(s1, d.Event("a"))
    target, label = s0.out[0]
    assert (target, label) == (1, d.Event("a"))


def test_transition_indexes_like_a_tuple():
    # DESops.core.automata.UnobservableReach does t[0]/t[1], not
    # unpacking, on adjacency entries -- Transition must support both.
    s0 = State(0, "s0")
    s1 = State(1, "s1")
    t = s0.add_transition(s1, d.Event("a"))
    assert t[0] == 1
    assert t[1] == d.Event("a")


def test_is_deterministic_true_by_default_and_after_distinct_labels():
    s0 = State(0, "s0")
    s1 = State(1, "s1")
    s2 = State(2, "s2")
    assert s0.is_deterministic
    s0.add_transition(s1, d.Event("a"))
    assert s0.is_deterministic
    s0.add_transition(s2, d.Event("b"))
    assert s0.is_deterministic


def test_is_deterministic_false_after_duplicate_label():
    s0 = State(0, "s0")
    s1 = State(1, "s1")
    s2 = State(2, "s2")
    s0.add_transition(s1, d.Event("a"))
    assert s0.is_deterministic
    s0.add_transition(s2, d.Event("a"))
    assert not s0.is_deterministic


def test_is_deterministic_recovers_after_removing_duplicate():
    s0 = State(0, "s0")
    s1 = State(1, "s1")
    s2 = State(2, "s2")
    s0.add_transition(s1, d.Event("a"))
    s0.add_transition(s2, d.Event("a"))
    assert not s0.is_deterministic

    s0.remove_transitions_to(s2, d.Event("a"))
    assert s0.is_deterministic
    assert s0.out == [Transition(1, d.Event("a"))]
    assert s2.incoming == []


def test_remove_transitions_to_without_label_removes_all():
    s0 = State(0, "s0")
    s1 = State(1, "s1")
    s0.add_transition(s1, d.Event("a"))
    s0.add_transition(s1, d.Event("b"))
    # (a, b) are distinct labels to the same target: that's deterministic
    # (no duplicate label), just two edges to one state.
    assert s0.is_deterministic

    s0.remove_transitions_to(s1)
    assert s0.out == []
    assert s1.incoming == []


def test_marked_and_init_flags():
    s = State(0, "s0", marked=True, init=True)
    assert s.marked is True
    assert s.init is True


def test_marked_defaults_to_none_not_false():
    s = State(0, "s0")
    assert s.marked is None


def test_extra_attrs():
    s = State(0, "s0", forbidden=True, proposition="p1")
    assert s.attrs == {"forbidden": True, "proposition": "p1"}


# --- states_from_data -------------------------------------------------------


def test_states_from_data_matches_automaton_structure():
    g = d.DFA()
    g.add_vertices(3, marked=[False, True, False])
    g.add_edges([(0, 1), (1, 2), (2, 0)], [d.Event("a"), d.Event("b"), d.Event("c")])

    states = states_from_data(g.to_data())

    assert len(states) == 3
    assert [s.name for s in states] == ["0", "1", "2"]
    assert [s.marked for s in states] == [False, True, False]
    assert states[0].out == [Transition(1, d.Event("a"))]
    assert states[2].out == [Transition(0, d.Event("c"))]


def test_states_from_data_leaves_incoming_empty_by_default():
    # Building .incoming costs ~3x the outgoing-only build (see
    # doc/logs/v2-igraph-decoupling.md), and most operations never read
    # it, so states_from_data() doesn't build it unless asked.
    g = d.DFA()
    g.add_vertices(2)
    g.add_edge(0, 1, d.Event("a"))
    states = states_from_data(g.to_data())
    assert states[0].incoming == []
    assert states[1].incoming == []


def test_states_from_data_build_incoming_true():
    g = d.DFA()
    g.add_vertices(3)
    g.add_edges([(0, 1), (1, 2), (2, 0)], [d.Event("a"), d.Event("b"), d.Event("c")])

    states = states_from_data(g.to_data(), build_incoming=True)

    assert states[1].incoming == [Transition(0, d.Event("a"))]
    assert states[0].incoming == [Transition(2, d.Event("c"))]


def test_populate_incoming_after_the_fact():
    g = d.DFA()
    g.add_vertices(3)
    g.add_edges([(0, 1), (1, 2), (2, 0)], [d.Event("a"), d.Event("b"), d.Event("c")])

    states = states_from_data(g.to_data())
    assert all(s.incoming == [] for s in states)

    populate_incoming(states)

    assert states[1].incoming == [Transition(0, d.Event("a"))]
    assert states[2].incoming == [Transition(1, d.Event("b"))]
    assert states[0].incoming == [Transition(2, d.Event("c"))]
    # .out is untouched by populate_incoming
    assert states[0].out == [Transition(1, d.Event("a"))]


def test_states_from_data_all_deterministic_for_a_dfa():
    g = d.DFA()
    g.add_vertices(2)
    g.add_edges([(0, 1), (0, 0)], [d.Event("a"), d.Event("b")])
    states = states_from_data(g.to_data())
    assert all(s.is_deterministic for s in states)


def test_states_from_data_detects_nondeterminism_for_an_nfa():
    g = d.NFA()
    g.add_vertices(3)
    g.add_edges([(0, 1), (0, 2)], [d.Event("a"), d.Event("a")])
    states = states_from_data(g.to_data())
    assert not states[0].is_deterministic
    assert states[1].is_deterministic
    assert states[2].is_deterministic


def test_states_from_data_reads_init_from_nfa():
    dfa = d.DFA()
    dfa.add_vertices(2)
    # Constructing an NFA from a non-NFA source sets vertex 0's "init" True,
    # the rest False (see NFA.__init__).
    g = d.NFA(dfa)
    states = states_from_data(g.to_data())
    assert states[0].init is True
    assert states[1].init is False


def test_states_from_data_init_false_when_never_set():
    g = d.NFA()
    g.add_vertices(3)  # init=None at construction; add_vertices pads with None
    states = states_from_data(g.to_data())
    assert all(s.init is False for s in states)


def test_states_from_data_defaults_init_false_for_dfa():
    g = d.DFA()
    g.add_vertices(2)
    states = states_from_data(g.to_data())
    assert states[0].init is False
    assert states[1].init is False


def test_states_from_data_captures_probs_for_pfa():
    g = d.PFA()
    g.add_vertices(2)
    g.add_edges([(0, 1)], [d.Event("a")], [0.5])
    states = states_from_data(g.to_data())
    assert states[0].out[0].prob == 0.5


def test_states_from_data_captures_extra_vertex_attrs():
    g = d.DFA()
    g.add_vertex(name="s0", forbidden=True)
    g.add_vertex(name="s1", forbidden=False)
    states = states_from_data(g.to_data())
    assert states[0].attrs == {"forbidden": True}
    assert states[1].attrs == {"forbidden": False}


def test_states_from_data_empty_automaton():
    g = d.DFA()
    assert states_from_data(g.to_data()) == []


# --- assume_deterministic ---------------------------------------------------


def test_assume_deterministic_sets_flag_without_tracking():
    g = d.NFA()
    g.add_vertices(3)
    # This would be nondeterministic if actually tracked (duplicate "a" out
    # of state 0) -- assume_deterministic skips the check and trusts the
    # caller instead.
    g.add_edges([(0, 1), (0, 2)], [d.Event("a"), d.Event("a")])

    states = states_from_data(g.to_data(), assume_deterministic=True)

    assert all(s.is_deterministic for s in states)


def test_assume_deterministic_true_for_a_real_dfa():
    g = d.DFA()
    g.add_vertices(3)
    g.add_edges([(0, 1), (1, 2), (2, 0)], [d.Event("a"), d.Event("b"), d.Event("c")])

    states = states_from_data(g.to_data(), assume_deterministic=True)

    assert all(s.is_deterministic for s in states)
    # No per-label bookkeeping was done -- nothing to compare against, but
    # confirm the states are otherwise structurally identical to the
    # tracked build.
    tracked = states_from_data(g.to_data())
    assert [s.out for s in states] == [s.out for s in tracked]


def test_remove_transitions_to_is_a_safe_noop_when_determinism_was_not_tracked():
    s0 = State(0, "s0")
    s1 = State(1, "s1")
    s2 = State(2, "s2")
    s0.add_transition(s1, d.Event("a"), track_determinism=False)
    s0.add_transition(s2, d.Event("a"), track_determinism=False)
    s0.is_deterministic = True  # caller's own assertion, e.g. from a DFA source

    # Removing one of the (untracked) duplicate-labeled edges must not
    # raise, and must leave is_deterministic exactly as the caller set it.
    s0.remove_transitions_to(s2, d.Event("a"))
    assert s0.is_deterministic
    assert s0.out == [Transition(1, d.Event("a"))]
