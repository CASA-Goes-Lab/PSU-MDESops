"""
Tests for core_aut.efsm: the EFSM syntax classes and EfsmSystem.check().

The meaning (states, transitions) is not computed here; it is defined in
certisc-proof/DESopsProof/Efsm.lean and will be computed by the Rust unfolder.
"""

import pytest

from core_aut import (
    AtLoc,
    Bin,
    Edge,
    Efsm,
    EfsmError,
    EfsmSystem,
    Ite,
    Lit,
    Un,
    Var,
    Variable,
)
from core_aut.efsm import FALSE, TRUE, conj, disj, reads, text


def counter():
    """Spec Example 2: x in [0, 2], inc guarded by x < 2, reset back to 0."""
    x = Var("x")
    return EfsmSystem(
        events=["inc", "reset"],
        variables=[Variable("x", 0, 2, 0)],
        automata=[Efsm(
            "C", ["L"], {"L"}, {"inc", "reset"},
            edges=[Edge("L", "inc", [Bin("lt", x, Lit(2))], {"x": Bin("add", x, Lit(1))}),
                   Edge("L", "reset", updates={"x": Lit(0)})],
            marked=Bin("eq", x, Lit(0)))],
        Euc={"reset"})


# --- expressions --------------------------------------------------------------------------

def test_bool_literals_are_integers():
    assert Lit(True) == Lit(1) == TRUE
    assert Lit(False) == FALSE
    assert type(Lit(True).value) is int


@pytest.mark.parametrize("bad", ["3", 1.5, None])
def test_a_literal_must_be_an_integer(bad):
    with pytest.raises(EfsmError, match="integer"):
        Lit(bad)


def test_unknown_operators_are_refused():
    with pytest.raises(EfsmError, match="unary"):
        Un("sqrt", Lit(4))
    with pytest.raises(EfsmError, match="binary"):
        Bin("pow", Lit(2), Lit(3))


def test_expressions_are_hashable_values():
    a = Bin("add", Var("x"), Lit(1))
    assert a == Bin("add", Var("x"), Lit(1))
    assert len({a, Bin("add", Var("x"), Lit(1))}) == 1


def test_conj_and_disj():
    assert conj([]) == TRUE
    assert disj([]) == FALSE
    assert conj([Var("a")]) == Var("a")
    assert conj([Var("a"), Var("b"), Var("c")]) == \
        Bin("and", Bin("and", Var("a"), Var("b")), Var("c"))
    assert disj([Var("a"), Var("b")]) == Bin("or", Var("a"), Var("b"))


def test_text_is_cif_like():
    e = Ite(AtLoc("Load", "Low"), Lit(110), Bin("max", Var("x"), Un("neg", Lit(2))))
    assert text(e) == "(if Load.Low: 110 else max(x, -2) end)"
    assert text(Un("not", Bin("le", Var("x"), Un("abs", Var("y"))))) == "not (x <= abs(y))"


def test_reads_collects_variables_and_location_tests():
    e = Bin("and", Bin("lt", Var("Room.T"), Lit(2)),
            Ite(AtLoc("CRAC1", "Active"), Var("q"), Un("neg", AtLoc("Load", "Low"))))
    assert reads(e) == ({"Room.T", "q"}, {"CRAC1", "Load"})
    assert reads(Lit(0)) == (set(), set())


# --- variables, edges, systems ----------------------------------------------------------

def test_variable_show():
    assert Variable("b", 0, 1, 0, kind="bool").show(1) == "true"
    assert Variable("m", 0, 1, 0, kind="enum", literals=("Off", "On")).show(1) == "On"
    assert Variable("x", -2, 2, 0).show(-2) == "-2"


def test_an_edge_without_target_stays():
    e = Edge("L", "a")
    assert e.target == "L"
    assert e.guard == () and e.updates == {}
    assert Edge("L", "a", [TRUE]).guard == (TRUE,)


def test_check_returns_the_system():
    m = counter()
    assert m.check() is m
    assert m.variable("x").hi == 2
    assert m.automaton("C").initial == {"L"}
    assert m.writers("x") == ["C"]


def test_writers_lists_every_writer():
    # Not allowed in CIF, allowed in an EFSM (spec Example 3).
    m = EfsmSystem(
        ["e"], [Variable("x", 0, 2, 0)],
        [Efsm("A", ["a"], {"a"}, {"e"}, [Edge("a", "e", updates={"x": Lit(1)})]),
         Efsm("B", ["b"], {"b"}, {"e"}, [Edge("b", "e", updates={"x": Lit(2)})]),
         Efsm("R", ["r"], {"r"}, {"e"}, [Edge("r", "e", [Bin("eq", Var("x"), Lit(0))])])])
    assert m.check().writers("x") == ["A", "B"]


def broken(change):
    m = counter()
    change(m)
    return m


@pytest.mark.parametrize("change, what", [
    (lambda m: m.events.append("inc"), "event 'inc' declared twice"),
    (lambda m: m.variables.append(Variable("x", 0, 1, 0)), "variable 'x' declared twice"),
    (lambda m: m.automata.append(m.automata[0]), "EFSM 'C' declared twice"),
    (lambda m: m.Euc.add("tick"), "uncontrollable events not declared"),
    (lambda m: m.Euo.add("tick"), "unobservable events not declared"),
    (lambda m: setattr(m.variables[0], "init", 3), "outside"),
    (lambda m: setattr(m.variables[0], "hi", 2 ** 31), "32-bit"),
    (lambda m: setattr(m.variables[0], "lo", 3), "empty"),
    (lambda m: setattr(m.automata[0], "kind", "monitor"), "unknown kind"),
    (lambda m: setattr(m.automata[0], "locations", []), "no locations"),
    (lambda m: m.automata[0].locations.append("L"), "location 'L' declared twice"),
    (lambda m: setattr(m.automata[0], "initial", set()), "no initial location"),
    (lambda m: m.automata[0].initial.add("M"), "unknown initial location"),
    (lambda m: m.automata[0].alphabet.add("tick"), "alphabet events not declared"),
    (lambda m: setattr(m.automata[0], "marked", Var("y")), "marked: unknown variable"),
    (lambda m: m.automata[0].edges.append(Edge("L", "inc", target="M")), "unknown location"),
    (lambda m: m.automata[0].alphabet.discard("reset"), "not in the alphabet"),
    (lambda m: m.automata[0].edges.append(Edge("L", "inc", updates={"y": Lit(0)})),
     "writes unknown variable"),
    (lambda m: m.automata[0].edges.append(Edge("L", "inc", [Var("y")])), "unknown variable"),
    (lambda m: m.automata[0].edges.append(Edge("L", "inc", updates={"x": Var("y")})),
     "unknown variable"),
    (lambda m: m.automata[0].edges.append(Edge("L", "inc", [AtLoc("D", "L")])), "unknown EFSM D"),
    (lambda m: m.automata[0].edges.append(Edge("L", "inc", [AtLoc("C", "M")])),
     "C has no location M"),
])
def test_check_errors(change, what):
    with pytest.raises(EfsmError, match=what):
        broken(change).check()


def test_an_alphabet_event_without_edges_is_allowed():
    # It blocks the event (spec §3): well formed as syntax.
    m = counter()
    m.events.append("stop")
    m.automata[0].alphabet.add("stop")
    m.check()


def test_efsm_error_is_a_value_error():
    assert issubclass(EfsmError, ValueError)
