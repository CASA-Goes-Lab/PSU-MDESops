"""
read_cif / parse_cif (DESops.io.cif), EFSM unfolding (DESops.core.efsm), and
write_automaton (DESops.io.fsm).
"""

from pathlib import Path

import pytest

import DESops as d
from DESops import error
from DESops.core.operations.language_equivalence import compare_language

MODELS = Path(__file__).parent.resolve() / "models" / "cif"
E = d.Event


def same_language(g1, g2):
    return compare_language(g1.to_automata(), g2.to_automata(), type="both")


def by_name(g):
    """Transitions as (source name, event label, target name)."""
    return {
        (g.states[s].name, e.label, g.states[t].name) for s, e, t in g.transitions()
    }


# --- the data-center example, against its hand-written .fsm version ------------


def test_datacenter_matches_hand_written_fsm_plant():
    system = d.read_cif(str(MODELS / "datacenter.cif"))
    parts = [
        d.read_automaton(str(MODELS / "datacenter_fsm" / f"{n}.fsm"))
        for n in ["Load", "CRAC1", "CRAC2", "Room", "HeatBalance"]
    ]
    expected = d.composition.parallel(*parts)

    flat = system.unfold(flat=True)
    assert (flat.num_states, flat.num_transitions) == (24, 88)
    assert (expected.num_states, expected.num_transitions) == (24, 88)
    assert flat.events == expected.events
    assert flat.Euc == expected.Euc
    assert same_language(flat, expected)


def test_datacenter_guards_link_every_automaton():
    system = d.read_cif(str(MODELS / "datacenter.cif"))
    assert system.groups() == [["Load", "CRAC1", "CRAC2", "Room"]]
    parts = system.unfold()
    assert list(parts) == ["Load+CRAC1+CRAC2+Room"]
    assert parts["Load+CRAC1+CRAC2+Room"].num_states == 24


def test_definition_instances_get_their_own_events_and_initial_location():
    system = d.read_cif(str(MODELS / "datacenter.cif"))
    crac1 = system.automaton("CRAC1")
    crac2 = system.automaton("CRAC2")
    assert crac1.alphabet == {"on_1", "off_1"}
    assert crac2.alphabet == {"on_2", "off_2"}
    flat = system.unfold(flat=True)
    (x0,) = flat.init
    assert flat.states[x0].name == ("Low", "Active", "Min", "T=0")


# --- grouping ------------------------------------------------------------------

TWO_MACHINES = """
controllable start1, start2; uncontrollable finish, reset;
plant M1:
  location Idle: initial; marked; edge start1 goto Busy;
  location Busy: edge finish goto Idle;
end
plant M2:
  location Idle: initial; marked; edge start2 goto Busy;
  location Busy: edge finish goto Idle;
end
plant Counter:
  disc int[0..2] n = 0;
  location: initial; marked;
    edge finish when n < 2 do n := n + 1;
    edge reset when n = 2 do n := 0;
end
"""


def test_shared_events_alone_do_not_link_automata():
    system = d.parse_cif(TWO_MACHINES)
    assert system.groups() == [["M1"], ["M2"], ["Counter"]]
    parts = system.unfold()
    assert list(parts) == ["M1", "M2", "Counter"]
    assert parts["Counter"].num_states == 3


def test_components_compose_to_the_flat_unfolding():
    system = d.parse_cif(TWO_MACHINES)
    parts = system.unfold()
    composed = d.composition.parallel(*parts.values())
    flat = system.unfold(flat=True)
    assert flat.num_states == composed.num_states
    assert same_language(flat, composed)


def test_guard_reading_another_automaton_links_them():
    system = d.parse_cif(TWO_MACHINES.replace(
        "edge start2 goto Busy", "edge start2 when M1.Idle goto Busy"))
    assert system.groups() == [["M1", "M2"], ["Counter"]]
    assert list(system.unfold()) == ["M1+M2", "Counter"]


def test_alg_reading_another_automaton_links_them():
    system = d.parse_cif(TWO_MACHINES.replace(
        "plant M2:", "alg bool free = M1.Idle;\nplant M2:").replace(
        "edge start2 goto Busy", "edge start2 when free goto Busy"))
    assert system.groups() == [["M1", "M2"], ["Counter"]]


# --- semantics -------------------------------------------------------------------


def test_variable_edges_names_and_marking():
    g = d.parse_cif("""
        uncontrollable up, down;
        plant P:
          disc int[0..2] x = 0;
          marked x = 0;
          location: initial; marked;
            edge up when x < 2 do x := x + 1;
            edge down when x > 0 do x := x - 1;
        end
    """).unfold(flat=True)
    assert [s.name for s in g.states] == ["x=0", "x=1", "x=2"]
    assert [s.marked for s in g.states] == [True, False, False]
    assert by_name(g) == {
        ("x=0", "up", "x=1"), ("x=1", "up", "x=2"),
        ("x=2", "down", "x=1"), ("x=1", "down", "x=0"),
    }
    assert g.Euc == {E("up"), E("down")}


def test_events_are_event_objects():
    g = d.parse_cif(TWO_MACHINES).unfold(flat=True)
    assert all(isinstance(e, d.Event) for e in g.events)
    assert g.Euc == {E("finish"), E("reset")}


def test_several_events_on_one_edge_and_self_loop():
    g = d.parse_cif("""
        controllable a, b;
        plant P:
          location L: initial; marked; edge a, b;
        end
    """).unfold(flat=True)
    assert by_name(g) == {("L", "a", "L"), ("L", "b", "L")}


def test_alphabet_without_edges_blocks_the_event():
    system = d.parse_cif("""
        controllable a, b;
        plant P:
          location: initial; marked; edge a; edge b;
        end
        plant Q:
          alphabet a;
          location: initial; marked;
        end
    """)
    g = system.unfold(flat=True)
    assert {e for _, e, _ in by_name(g)} == {"b"}
    assert E("a") in g.events


def test_enum_variable_and_location_guard():
    g = d.parse_cif("""
        enum Mode = Off, Low, High;
        controllable step;
        plant P:
          disc Mode m;
          location A: initial; marked;
            edge step when m != High do m := if m = Off: Low else High end;
        end
    """).unfold(flat=True)
    assert [s.name for s in g.states] == ["A(m=Off)", "A(m=Low)", "A(m=High)"]


def test_initial_predicates_can_give_several_initial_states():
    g = d.parse_cif("""
        controllable a;
        const bool BOTH = true;
        plant P:
          location X: initial; edge a goto Y;
          location Y: initial BOTH; marked;
        end
    """).unfold(flat=True)
    assert {g.states[x].name for x in g.init} == {"X", "Y"}
    assert g.kind == "NFA"


def test_nondeterministic_edges():
    g = d.parse_cif("""
        uncontrollable a;
        plant P:
          location X: initial; edge a goto Y; edge a goto Z;
          location Y; location Z;
        end
    """).unfold(flat=True)
    assert g.kind == "NFA"
    assert by_name(g) == {("X", "a", "Y"), ("X", "a", "Z")}


def test_constants_and_arithmetic():
    g = d.parse_cif("""
        controllable inc;
        const int N = 2 * 3 - 4;
        plant P:
          disc int[0..N] x;
          location: initial; marked; edge inc when x + 1 <= N do x := min(x + 1, N);
        end
    """).unfold(flat=True)
    assert g.num_states == 3


def test_kind_filter_and_requirements():
    system = d.parse_cif("""
        controllable a;
        plant P: location: initial; marked; edge a; end
        requirement R: location: initial; marked; edge a; end
    """)
    assert [a.kind for a in system.automata] == ["plant", "requirement"]
    assert list(system.unfold(kind="plant")) == ["P"]
    assert list(system.unfold(kind="requirement")) == ["R"]


def test_linking_a_plant_and_a_requirement_is_an_error():
    system = d.parse_cif("""
        controllable a;
        plant P: location X: initial; marked; edge a; end
        requirement R: location: initial; marked; edge a when P.X; end
    """)
    with pytest.raises(error.EfsmError, match="different kinds"):
        system.unfold()


# --- errors ----------------------------------------------------------------------


def test_update_out_of_range_raises():
    system = d.parse_cif("""
        controllable inc;
        plant P:
          disc int[0..1] x;
          location: initial; marked; edge inc do x := x + 1;
        end
    """)
    with pytest.raises(error.EfsmError, match="outside its range"):
        system.unfold(flat=True)


@pytest.mark.parametrize("text, what", [
    ("input bool b;", "input"),
    ("controllable a; plant P: location: initial; urgent; end", "urgent"),
    ("controllable a; plant P: location: initial; invariant true; end", "invariant"),
    ("plant P: disc int x; location: initial; end", "needs a range"),
    ("plant P: disc real x = 0.0; location: initial; end", "real"),
    ("group G: end", "group"),
    ("controllable a; plant P: disc int[0..1] x; location: initial; "
     "edge a do if x = 0: x := 1 end; end", "if-update"),
])
def test_unsupported_constructs_raise(text, what):
    with pytest.raises(error.UnsupportedFeatureError, match=what):
        d.parse_cif(text)


@pytest.mark.parametrize("text, what", [
    ("plant P: location: initial; edge a; end", "not a declared event"),
    ("controllable a; plant P: location: initial; edge a when y; end", "unknown name y"),
    ("controllable a; plant P: location L: initial; edge a goto M; end", "no location M"),
    ("controllable a; plant P: location: initial; end\nplant P: location: initial; end",
     "declared twice"),
    ("uncontrollable u; plant def D(controllable c): location: initial; edge c; end\n"
     "X: D(u);", "must be controllable"),
    ("alg bool a = b; alg bool b = a; controllable e;\n"
     "plant P: location: initial; edge e when a; end", "in terms of itself"),
    ("controllable a; plant P: location: initial; edge a; ", "missing 'end'"),
])
def test_model_errors_raise(text, what):
    with pytest.raises(error.FileFormatError, match=what):
        d.parse_cif(text)


# --- write_automaton -------------------------------------------------------------


def test_write_automaton_round_trip(tmp_path):
    system = d.read_cif(str(MODELS / "datacenter.cif"))
    g = system.unfold(flat=True)
    path = tmp_path / "plant.fsm"
    d.write_automaton(g, str(path))
    back = d.read_automaton(str(path))
    assert by_name(back) == by_name(g)
    assert {s.name: s.marked for s in back.states} == {s.name: s.marked for s in g.states}
    assert back.states[min(back.init)].name == g.states[min(g.init)].name
    assert back.Euc == g.Euc


def test_write_automaton_puts_the_initial_state_first(tmp_path):
    g = d.Automaton()
    g.add_state("a")
    g.add_state("b", init=True)
    g.add_transition(1, E("x"), 0)
    path = tmp_path / "g.fsm"
    d.write_automaton(g, str(path))
    assert d.read_automaton(str(path)).states[0].name == "b"


def test_write_automaton_rejects_what_fsm_cannot_hold(tmp_path):
    g = d.Automaton()
    g.add_state("a", init=True)
    g.add_state("b", init=True)
    with pytest.raises(error.FileFormatError, match="exactly one initial"):
        d.write_automaton(g, str(tmp_path / "g.fsm"))
    h = d.Automaton()
    h.add_state("(x)", init=True)
    with pytest.raises(error.FileFormatError, match="starts with"):
        d.write_automaton(h, str(tmp_path / "h.fsm"))
