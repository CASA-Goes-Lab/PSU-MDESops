"""
Tests for io_aut (JSON format, .fsm import) and for ValidAutomaton.
"""

import json
import random

import pytest

from core_aut import Automaton, InvalidAutomatonError, ValidAutomaton, validate
from io_aut import from_dict, read_aut, read_fsm, to_dict, write_aut
from io_aut.aut_json import AutFormatError
from io_aut.fsm import FsmFormatError
from ops_aut import next_states

MACHINE = {
    "events": ["start", "finish", "break", "repair"],
    "uncontrollable": ["break"],
    "unobservable": [],
    "states": ["Idle", "Working", "Down"],
    "initial": ["Idle"],
    "marked": ["Idle"],
    "transitions": {
        "Idle": {"start": "Working"},
        "Working": {"finish": "Idle", "break": "Down"},
        "Down": {"repair": "Idle"},
    },
}


def write_json(tmp_path, d, name="m.json"):
    p = tmp_path / name
    p.write_text(json.dumps(d))
    return p


def same(V, W):
    return (V.names == W.names and V.events == W.events and V.Euc == W.Euc
            and V.Euo == W.Euo and V.init == W.init and V.marked == W.marked
            and sorted(V.transitions()) == sorted(W.transitions()))


def random_automaton(rng):
    n = rng.randint(1, 8)
    events = rng.sample(["a", "b", "c", "d"], rng.randint(1, 4))
    G = Automaton(events=events, Euc=rng.sample(events, rng.randint(0, len(events))),
                  Euo=rng.sample(events, rng.randint(0, len(events))))
    for i in range(n):
        G.add_state(f"s{i}", rng.random() < 0.4, init=(i == 0 or rng.random() < 0.2))
    for x in range(n):
        for e in events:
            for _ in range(rng.choice([0, 0, 1, 1, 2])):
                G.add_transition(x, e, rng.randrange(n))
    return G


def test_read_machine(tmp_path):
    V = read_aut(write_json(tmp_path, MACHINE))
    assert isinstance(V, ValidAutomaton) and V.is_deterministic
    assert V.names == ("Idle", "Working", "Down")
    assert V.Euc == {"break"} and V.init == {0} and V.marked == {0}
    assert sorted(V.transitions()) == [(0, "start", 1), (1, "break", 2), (1, "finish", 0),
                                       (2, "repair", 0)]
    assert next_states(V, [V.index_of("Working")], "break") == [V.index_of("Down")]


def test_round_trip_write_read(tmp_path):
    rng = random.Random(8)
    for trial in range(100):
        V = validate(random_automaton(rng))
        p = tmp_path / f"r{trial}.json"
        write_aut(V, p)
        W = read_aut(p)
        assert same(V, W), trial
        assert to_dict(W) == to_dict(V)


def test_nondeterministic_targets_list(tmp_path):
    d = dict(MACHINE, transitions={"Idle": {"start": ["Working", "Down"]}})
    V = read_aut(write_json(tmp_path, d))
    assert not V.is_deterministic
    assert sorted(next_states(V, [0], "start")) == [1, 2]
    assert to_dict(V)["transitions"] == {"Idle": {"start": ["Working", "Down"]}}


def test_events_default_from_transitions(tmp_path):
    d = {k: v for k, v in MACHINE.items() if k != "events"}
    assert read_aut(write_json(tmp_path, d)).events == {"start", "finish", "break", "repair"}


def test_validity_errors_come_from_the_verified_checker(tmp_path):
    no_init = dict(MACHINE, initial=[])
    with pytest.raises(InvalidAutomatonError, match="W3"):
        read_aut(write_json(tmp_path, no_init))
    # "finish" is used by a transition but left out of "events" (W1). ("break" would not do:
    # it is uncontrollable, and Automaton(...) puts Euc and Euo into E.)
    event_not_in_E = dict(MACHINE, events=["start", "break", "repair"])
    with pytest.raises(InvalidAutomatonError, match="W1"):
        read_aut(write_json(tmp_path, event_not_in_E))


@pytest.mark.parametrize("bad, message", [
    ({"states": ["a"], "initial": ["a"]}, "missing"),
    (dict(MACHINE, extra=1), "unknown keys"),
    (dict(MACHINE, states=["Idle", "Idle", "Down"]), "repeated"),
    (dict(MACHINE, initial=["Nowhere"]), "not in"),
    (dict(MACHINE, transitions={"Idle": {"start": "Nowhere"}}), "not in"),
    (dict(MACHINE, transitions={"Idle": {"start": []}}), "non-empty"),
])
def test_format_errors(tmp_path, bad, message):
    with pytest.raises(AutFormatError, match=message):
        read_aut(write_json(tmp_path, bad))


def test_valid_automaton_is_read_only():
    V = validate(from_dict(MACHINE))
    with pytest.raises(AttributeError):
        V.foo = 1
    with pytest.raises(TypeError):
        ValidAutomaton()
    G = V.to_automaton()                      # editable copy, validated again after edits
    G.add_state("Extra")
    assert validate(G).num_states == 4 and V.num_states == 3


def test_read_fsm(tmp_path):
    p = tmp_path / "m1.fsm"
    p.write_text("3\n\nI1\t0\t2\nin_M1\tW1\tc\to\nto_M1\tW1\tc\to\n\n"
                 "W1\t0\t1\nf_M1\tD1\tuc\to\n\nD1\t0\t1\nout_B1\tI1\tc\to\n")
    V = read_fsm(p)
    assert V.names == ("I1", "W1", "D1") and V.init == {0} and V.Euc == {"f_M1"}
    assert next_states(V, [0], "in_M1") == [1]
    bad = tmp_path / "bad.fsm"
    bad.write_text("2\n\nA\t0\t1\na\tB\tc\to\n")         # state B announced but missing
    with pytest.raises(FsmFormatError):
        read_fsm(bad)


def test_valid_automaton_reads_like_an_automaton():
    rng = random.Random(9)
    for trial in range(100):
        G = random_automaton(rng)
        V = validate(G)
        assert V.num_states == G.num_states and len(V.states) == len(G.states)
        assert V.events == G.events and V.Euc == G.Euc and V.Euo == G.Euo and V.init == G.init
        for i, (vs, gs) in enumerate(zip(V.states, G.states)):
            assert vs.name == gs.name and vs.marked == gs.marked, (trial, i)
            assert {e: sorted(t) for e, t in vs.out.items()} == \
                   {e: sorted(t) for e, t in gs.out.items()}, (trial, i)
        assert sorted(V.transitions()) == sorted(G.transitions())
    V = validate(from_dict(MACHINE))
    with pytest.raises(AttributeError):
        V.states[0].name = "x"
    with pytest.raises(TypeError):
        V.states[0].out["start"] = (2,)
    assert V.states[-1].name == "Down"


def test_show_and_print():
    import io
    V = validate(from_dict(dict(MACHINE, transitions={
        "Idle": {"start": ["Working", "Down"]}, "Working": {"finish": "Idle"}})))
    text = str(V)
    assert text.splitlines()[0] == repr(V)
    assert "  uncontrollable: break" in text and "  initial:        Idle" in text
    assert "Idle    : start -> {Working, Down}" in text
    assert "Down    : (none)" in text
    out = io.StringIO()
    V.show(max_states=1, file=out)
    assert "... 2 more states" in out.getvalue()
    G = Automaton(events=["a"])
    for i in range(30):
        G.add_state(f"q{i}", init=(i == 0))
    lines = str(validate(G)).splitlines()
    assert lines[-1].strip() == "... 10 more states (V.show() prints all)"
    out = io.StringIO()
    validate(G).show(file=out)
    assert "q29" in out.getvalue() and "more states" not in out.getvalue()
