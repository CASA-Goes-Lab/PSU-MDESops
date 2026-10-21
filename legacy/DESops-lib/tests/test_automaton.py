"""
Tests for DESops.core.automaton.Automaton, the single DFA/NFA/PFA class
replacing DESops.core.automata.Automata and its subclasses. See
doc/logs/v2-automata-redesign.md.
"""

from pathlib import Path

import pytest

import DESops as d
from DESops.core.automaton import Automaton

a, b, c = d.Event("a"), d.Event("b"), d.Event("c")
cwd = Path(__file__).parent.resolve()


def chain():
    """0 -a-> 1 -b-> 2, state 0 initial, state 2 marked."""
    g = Automaton()
    g.add_state("x0", init=True)
    g.add_state("x1")
    g.add_state("x2", marked=True)
    g.add_transitions([(0, a, 1), (1, b, 2)])
    return g


# --- construction ------------------------------------------------------------


def test_add_state_returns_index_and_defaults_name():
    g = Automaton()
    assert g.add_state() == 0
    assert g.add_state("s1") == 1
    assert [s.name for s in g.states] == ["0", "s1"]


def test_add_states_with_marking():
    g = Automaton()
    assert g.add_states(["p", "q"], marked=[False, True]) == [0, 1]
    assert [s.marked for s in g.states] == [False, True]


def test_out_is_event_to_targets():
    g = chain()
    assert g.states[0].out == {a: [1]}
    assert g.states[1].out == {b: [2]}
    assert g.states[2].out == {}


def test_add_transition_registers_event():
    g = chain()
    assert g.events == {a, b}


def test_euc_euo_join_the_alphabet():
    g = Automaton(Euc={a}, Euo={c})
    assert g.events == {a, c}


def test_duplicate_transition_warns_and_is_skipped():
    g = chain()
    with pytest.warns(UserWarning, match="duplicate transition"):
        assert g.add_transition(0, a, 1) is False
    assert g.states[0].out == {a: [1]}
    assert g.num_transitions == 2


def test_transition_to_missing_state_raises():
    g = chain()
    with pytest.raises(IndexError):
        g.add_transition(0, c, 7)


def test_transition_from_missing_state_raises():
    g = chain()
    # -1 must not wrap around to the last state
    for source in (-1, 7):
        with pytest.raises(IndexError, match=f"no state {source}"):
            g.add_transition(source, c, 0)
    assert g.num_transitions == 2
    assert c not in g.events


def test_index_of():
    g = chain()
    assert g.index_of("x1") == 1
    with pytest.raises(KeyError):
        g.index_of("nope")


# --- kind ------------------------------------------------------------------


def test_chain_is_dfa():
    g = chain()
    assert g.is_deterministic
    assert g.kind == "DFA"


def test_duplicate_event_makes_nfa_and_removal_restores_dfa():
    g = chain()
    g.add_transition(0, a, 2)
    assert g.states[0].out == {a: [1, 2]}
    assert g.kind == "NFA"

    g.remove_transition(0, a, 2)
    assert g.kind == "DFA"


def test_multiple_initial_states_makes_nfa():
    g = chain()
    g.init.add(1)
    assert g.kind == "NFA"


def test_pfa_requires_prob_and_keeps_out_shape():
    g = Automaton(probabilistic=True)
    g.add_states(["x0", "x1", "x2"])
    g.init.add(0)
    g.add_transition(0, a, 1, 0.3)
    g.add_transition(0, a, 2, 0.7)
    assert g.kind == "PFA"
    assert g.states[0].out == {a: [1, 2]}
    assert g.states[0].prob == {(a, 1): 0.3, (a, 2): 0.7}

    with pytest.raises(ValueError):
        g.add_transition(1, b, 2)


def test_non_probabilistic_rejects_prob():
    g = chain()
    with pytest.raises(ValueError):
        g.add_transition(2, c, 0, 0.5)


# --- queries ---------------------------------------------------------------


def test_active_events_and_next_states():
    g = chain()
    g.add_transition(0, c, 2)
    assert g.active_events(0) == {a, c}
    assert g.next_states(0, a) == [1]
    assert g.next_states(0, b) == []
    assert sorted(g.next_states(0)) == [1, 2]


def test_transitions_iterates_every_triple():
    assert set(chain().transitions()) == {(0, a, 1), (1, b, 2)}


def test_incoming_is_lazy_and_invalidated_on_change():
    g = chain()
    assert g._incoming is None
    assert g.incoming(2) == {b: [1]}
    assert g._incoming is not None

    g.add_transition(0, b, 2)
    assert g._incoming is None
    assert sorted(g.incoming(2)[b]) == [0, 1]


# --- remove_states ---------------------------------------------------------


def test_remove_states_reindexes_transitions_and_init():
    g = chain()
    g.add_transition(2, c, 0)
    g.remove_states([1])

    assert [s.name for s in g.states] == ["x0", "x2"]
    assert set(g.transitions()) == {(1, c, 0)}
    assert g.init == {0}


def test_remove_states_recounts_nondeterminism():
    g = chain()
    g.add_transition(0, a, 2)
    assert g.kind == "NFA"
    g.remove_states([2])
    assert g.kind == "DFA"


def test_remove_initial_state_drops_it_from_init():
    g = chain()
    g.remove_states([0])
    assert g.init == set()


# --- copy ------------------------------------------------------------------


def test_copy_is_independent():
    g = chain()
    h = g.copy()
    h.add_transition(2, c, 0)
    h.states[0].marked = True
    assert g.num_transitions == 2
    assert not g.states[0].marked
    assert h.kind == g.kind == "DFA"


# --- bridge to the old classes ----------------------------------------------


def test_from_automata_dfa_fixture():
    old = d.read_fsm(str(cwd / "models" / "textbook" / "fig_2-1.fsm"), backend="native")
    g = Automaton.from_automata(old)

    assert g.kind == "DFA"
    assert g.num_states == old.vcount()
    assert g.num_transitions == old.ecount()
    assert g.init == {0}
    assert g.events == old.events
    assert g.Euc == old.Euc and g.Euo == old.Euo


def test_from_automata_nfa_reads_init_flags():
    old = d.NFA()
    old.add_vertices(3, init=[False, True, True])
    old.add_edges([(1, 0)], [a])
    g = Automaton.from_automata(old)
    assert g.init == {1, 2}
    assert g.kind == "NFA"


def test_round_trip_through_old_classes_preserves_language():
    from DESops.core.operations.language_equivalence import compare_language

    old = d.read_fsm(str(cwd / "models" / "textbook" / "fig_2-1.fsm"), backend="native")
    back = Automaton.from_automata(old).to_automata()
    assert isinstance(back, d.DFA)
    assert compare_language(old, back, type="both")


def test_to_automata_moves_initial_state_to_index_0():
    g = Automaton()
    g.add_states(["p", "q"])
    g.init.add(1)
    g.add_transition(1, a, 0)
    old = g.to_automata()
    assert old.vs["name"] == ["q", "p"]
    assert old.vs[0]["out"] == [(1, a)]


def test_to_automata_keeps_ur_in_sync_with_euo():
    g = chain()
    g.Euo.add(a)
    old = g.to_automata()
    assert old.UR.from_set({0}, freeze_result=True) == frozenset({0, 1})


def test_parallel_via_bridge_matches_old_parallel():
    m1 = d.read_fsm(str(cwd / "models" / "textbook" / "fig_2-1.fsm"), backend="native")
    m2 = d.read_fsm(str(cwd / "models" / "textbook" / "fig_2-2.fsm"), backend="native")
    expected = d.composition.parallel(m1, m2, backend="native")

    g1, g2 = Automaton.from_automata(m1), Automaton.from_automata(m2)
    got = Automaton.from_automata(
        d.composition.parallel(g1.to_automata(), g2.to_automata(), backend="native")
    )
    assert got.num_states == expected.vcount()
    assert got.num_transitions == expected.ecount()
