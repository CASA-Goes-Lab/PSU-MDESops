"""
read_automaton (DESops.io.fsm) and parallel() on DESops.core.automaton.Automaton,
each checked against the existing implementations they replace.
"""

import warnings
from pathlib import Path

import pytest

import DESops as d
from DESops.core.automaton import Automaton
from DESops.core.operations.language_equivalence import compare_language

cwd = Path(__file__).parent.resolve()
ALL_FSM_FILES = sorted(cwd.joinpath("models").rglob("*.fsm"))
a, b, c = d.Event("a"), d.Event("b"), d.Event("c")


def _snapshot(g: Automaton):
    return {
        "names": [s.name for s in g.states],
        "marked": [s.marked for s in g.states],
        "transitions": set(g.transitions()),
        "events": g.events,
        "Euc": g.Euc,
        "Euo": g.Euo,
        "init": g.init,
        "kind": g.kind,
    }


# --- read_automaton -----------------------------------------------------------


def test_read_automaton_matches_old_reader_for_every_model():
    checked, mismatches = 0, []
    for path in ALL_FSM_FILES:
        try:
            with warnings.catch_warnings():
                warnings.simplefilter("ignore")
                old = d.read_fsm(str(path), backend="native")
        except Exception:
            continue  # not a standalone .fsm the old reader can parse either
        if not hasattr(old, "to_data") or old.vcount() == 0:
            continue  # empty file: the old reader returns a bare ig.Graph
        expected = _snapshot(Automaton.from_automata(old))
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            got = _snapshot(d.read_automaton(str(path)))
        checked += 1
        if got != expected:
            diff = {k: (expected[k], got[k]) for k in expected if expected[k] != got[k]}
            mismatches.append((path.name, diff))

    assert checked > 50
    assert not mismatches, "\n".join(f"{p}: {diff}" for p, diff in mismatches)


def test_read_automaton_m1_shape():
    g = d.read_automaton(str(cwd / "models" / "textbook" / "fig_2-1.fsm"))
    assert g.kind == "DFA"
    assert g.init == {0}
    assert "_graph" not in vars(g)


def test_read_automaton_empty_file_gives_empty_automaton():
    g = d.read_automaton(str(cwd / "models" / "sc_tests" / "book_ex_3_11_C.fsm"))
    assert g.num_states == 0 and g.init == set()


def test_read_automaton_pfa():
    g = d.read_automaton(str(cwd / "models" / "prob_model.fsm"))
    assert g.kind == "PFA"
    assert all(s.prob for s in g.states if s.out)


# --- parallel on Automaton ----------------------------------------------------


def _pairs():
    names = ["fig_2-1.fsm", "fig_2-2.fsm", "fig_2-21_G1.fsm"]
    paths = [str(cwd / "models" / "textbook" / n) for n in names]
    return paths


def test_parallel_automaton_matches_old_parallel():
    p1, p2, _ = _pairs()
    old = d.composition.parallel(
        d.read_fsm(p1, backend="native"), d.read_fsm(p2, backend="native"), backend="native"
    )
    new = d.composition.parallel(d.read_automaton(p1), d.read_automaton(p2))

    assert isinstance(new, Automaton)
    assert new.num_states == old.vcount()
    assert new.num_transitions == old.ecount()
    assert compare_language(new.to_automata(), old, type="both")


def test_parallel_automaton_three_inputs_matches_old_parallel():
    paths = _pairs()
    old = d.composition.parallel(*(d.read_fsm(p, backend="native") for p in paths), backend="native")
    new = d.composition.parallel(*(d.read_automaton(p) for p in paths))

    assert new.num_states == old.vcount()
    assert new.num_transitions == old.ecount()
    assert compare_language(new.to_automata(), old, type="both")


def test_parallel_shared_event_synchronizes_private_interleaves():
    g1 = Automaton()
    g1.add_states(["p0", "p1"])
    g1.init.add(0)
    g1.add_transitions([(0, a, 1), (1, b, 0)])  # a shared, b private

    g2 = Automaton()
    g2.add_states(["q0", "q1"])
    g2.init.add(0)
    g2.add_transitions([(0, c, 1), (1, a, 0)])  # a shared, c private

    p = d.composition.parallel(g1, g2)
    start = next(iter(p.init))
    assert p.states[start].name == ("p0", "q0")
    # a is blocked at (p0, q0) because q0 has no a; only c is possible
    assert p.active_events(start) == {c}
    assert p.events == {a, b, c}


def test_parallel_nfa_with_two_initial_states():
    g1 = Automaton()
    g1.add_states(["p0", "p1"])
    g1.init.update({0, 1})
    g2 = Automaton()
    g2.add_states(["q0"])
    g2.init.add(0)

    p = d.composition.parallel(g1, g2)
    assert {p.states[i].name for i in p.init} == {("p0", "q0"), ("p1", "q0")}


def test_parallel_rejects_probabilistic():
    g = Automaton(probabilistic=True)
    g.add_state(init=True)
    with pytest.raises(ValueError):
        d.composition.parallel(g, g)
