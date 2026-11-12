"""
Tests for io_aut.cif: reading CIF 3 models into an EfsmSystem (spec certisc-proof/spec/efsm.md
§7.1). Only the translation is tested here; the flat automaton comes with the Rust unfolder.
"""

from pathlib import Path

import pytest

from core_aut import AtLoc, Bin, EfsmSystem, Lit, Var, Variable
from core_aut.efsm import TRUE, reads, text
from io_aut import CifFormatError, UnsupportedCifError, parse_cif, read_cif

MODELS = Path(__file__).parent / "models"


def edges(a):
    return [(e.source, e.event, e.target) for e in a.edges]


# --- the datacenter model (Examples/v2/datacenter) ---------------------------------------

def test_datacenter_events_and_variables():
    m = read_cif(MODELS / "datacenter.cif")
    assert isinstance(m, EfsmSystem)
    assert m.events == ["on_1", "off_1", "on_2", "off_2", "load_up", "load_dn", "heat", "cool"]
    assert m.Euc == {"load_up", "load_dn", "heat", "cool"}
    assert m.Euo == set()
    assert m.variables == [Variable("Room.T", 0, 2, 0)]
    assert [a.name for a in m.automata] == ["Load", "CRAC1", "CRAC2", "Room"]
    assert all(a.kind == "plant" for a in m.automata)


def test_datacenter_definition_instances():
    m = read_cif(MODELS / "datacenter.cif")
    c1, c2 = m.automaton("CRAC1"), m.automaton("CRAC2")
    # Each instance gets its own events, and `initial lead` / `initial not lead` resolve
    # with its argument.
    assert c1.alphabet == {"on_1", "off_1"} and c2.alphabet == {"on_2", "off_2"}
    assert c1.initial == {"Active"} and c2.initial == {"Min"}
    assert edges(c1) == [("Min", "on_1", "Active"), ("Active", "off_1", "Min")]
    assert c1.marked == Bin("or", AtLoc("CRAC1", "Min"), AtLoc("CRAC1", "Active"))


def test_datacenter_room_guards_read_the_other_automata():
    m = read_cif(MODELS / "datacenter.cif")
    room = m.automaton("Room")
    assert room.locations == [""] and room.initial == {""}
    assert room.marked == TRUE
    heat, cool = room.edges
    assert (heat.event, cool.event) == ("heat", "cool")
    # The alg declarations are inlined; the coupling is visible in what the guards read.
    assert reads(Bin("and", *heat.guard)) == ({"Room.T"}, {"Load", "CRAC1", "CRAC2"})
    assert text(heat.guard[0]) == (
        "((if Load.Low: 110 else 142 end) > ((if CRAC1.Active: 100 else 10 end) + "
        "(if CRAC2.Active: 100 else 10 end)))")
    assert heat.guard[1] == Bin("lt", Var("Room.T"), Lit(2))
    assert heat.updates == {"Room.T": Bin("add", Var("Room.T"), Lit(1))}
    assert m.writers("Room.T") == ["Room"]


def test_read_cif_takes_str_or_path(tmp_path):
    p = tmp_path / "m.cif"
    p.write_text("controllable a; plant P: location: initial; marked; edge a; end")
    assert read_cif(str(p)).events == read_cif(p).events == ["a"]


# --- translation choices ------------------------------------------------------------------

def test_variable_kinds_and_default_values():
    m = parse_cif("""
        enum Mode = Off, On;
        plant P:
          disc bool f; disc Mode m; disc int[2..5] x; disc int[-3..3] y; disc bool g = true;
          location: initial;
        end""")
    assert m.variables == [
        Variable("P.f", 0, 1, 0, "bool"),
        Variable("P.m", 0, 1, 0, "enum", ("Off", "On")),
        Variable("P.x", 2, 5, 2),        # 0 is outside the range: the lower bound
        Variable("P.y", -3, 3, 0),
        Variable("P.g", 0, 1, 1, "bool"),
    ]


def test_several_events_on_one_edge_and_self_loops():
    m = parse_cif("""
        controllable a, b;
        plant P:
          location L1: initial; edge a, b;
          location L2: initial; edge a goto L1;
        end""")
    p = m.automaton("P")
    assert edges(p) == [("L1", "a", "L1"), ("L1", "b", "L1"), ("L2", "a", "L1")]
    assert p.initial == {"L1", "L2"}
    assert p.marked.value == 0          # no location is marked


def test_initial_predicates_choose_the_initial_locations():
    m = parse_cif("""
        const int N = 2;
        plant P:
          disc int[0..3] x = N;
          location A: initial x = 0;
          location B: initial x = N;
          location C: initial x >= 1, x <= 2;
        end""")
    assert m.automaton("P").initial == {"B", "C"}


def test_marking_combines_location_and_predicates():
    m = parse_cif("""
        enum Mode = Off, On;
        plant P:
          disc Mode m;
          marked m = Off;
          location L1: initial; marked;
          location L2: marked m = On;
          location L3;
        end""")
    assert text(m.automaton("P").marked) == "((P.m = 0) and (P.L1 or (P.L2 and (P.m = 1))))"


def test_bool_updates_and_alphabet_without_edges():
    m = parse_cif("""
        controllable a, stop;
        plant P:
          alphabet a, stop;
          disc bool f;
          location: initial; edge a when not f do f := true;
        end""")
    p = m.automaton("P")
    assert p.alphabet == {"a", "stop"}          # stop: in the alphabet, no edge (blocked)
    assert p.edges[0].updates == {"P.f": Lit(1)}


def test_kinds_and_constants():
    m = parse_cif("""
        controllable a; uncontrollable u;
        const int K = 7 div 2 + 3 mod 2;
        plant P: disc int[0..9] x; location: initial; edge a do x := K; edge u; end
        requirement R: location: initial; marked; edge a when P.x < max(K, 2); end""")
    assert m.automaton("P").kind == "plant" and m.automaton("R").kind == "requirement"
    assert m.automaton("P").edges[0].updates == {"P.x": Lit(4)}
    assert m.Euc == {"u"}


@pytest.mark.parametrize("a, b, q, r", [
    # ESCET CifMathTest.testDiv / testMod: div rounds toward zero, mod has the sign of a.
    (7, 4, 1, 3), (7, -4, -1, 3), (-7, 4, -1, -3), (-7, -4, 1, -3),
    (9, 4, 2, 1), (-8, 4, -2, 0), (0, -3, 0, 0),
])
def test_div_and_mod_as_cif(a, b, q, r):
    m = parse_cif(f"const int Q = {a} div {b}; const int R = {a} mod {b};\n"
                  "plant P: disc int[-9..9] x = Q; disc int[-9..9] y = R; location: initial; end")
    assert [v.init for v in m.variables] == [q, r]
    assert a == b * q + r


def test_32_bit_values_at_the_limits_are_fine():
    m = parse_cif("const int A = 2147483647; const int B = -2147483647 - 1;\n"
                  "const int C = 65536 * 16384; const int D = B mod -1;\n"
                  "plant P: disc int[-2147483647 - 1..2147483647] x = A;\n"
                  "disc int[0..1073741824] y = C; disc int[-9..9] z = D; location: initial; end")
    assert [(v.lo, v.hi, v.init) for v in m.variables] == [
        (-2 ** 31, 2 ** 31 - 1, 2 ** 31 - 1), (0, 2 ** 30, 2 ** 30), (-9, 9, 0)]


def test_div_and_mod_agree_with_the_identity():
    # ESCET CifMathTest.testDiv2 / testMod2, over the same range.
    from io_aut.cif import _static
    for a in range(-10, 10):
        for b in range(-10, 10):
            if b == 0:
                continue
            q = _static(Bin("div", Lit(a), Lit(b)), {})
            r = _static(Bin("mod", Lit(a), Lit(b)), {})
            assert q == int(a / b)                  # truncation toward zero
            assert r == a - b * q


def test_events_declared_without_a_kind_are_controllable():
    m = parse_cif("event e; plant P: location: initial; edge e; end")
    assert m.Euc == set()


# --- refusals -----------------------------------------------------------------------------

@pytest.mark.parametrize("text_, what", [
    ("input bool b;", "input"),
    ("controllable a; plant P: location: initial; urgent; end", "urgent"),
    ("controllable a; plant P: location: initial; invariant true; end", "invariant"),
    ("plant P: disc int x; location: initial; end", "needs a range"),
    ("plant P: disc real x = 0.0; location: initial; end", "real"),
    ("group G: end", "group"),
    ("controllable a; plant P: disc int[0..1] x; location: initial; "
     "edge a do if x = 0: x := 1 end; end", "if inside 'do'"),
    ("controllable a; plant P: disc int[0..4] x; location: initial; edge a do x := x / 2; end",
     "real division"),
    ("controllable a; plant P: disc int[0..4] x, y; location: initial; "
     "edge a do (x, y) := (y, x); end", "multi-assignment"),
])
def test_unsupported_constructs_raise(text_, what):
    with pytest.raises(UnsupportedCifError, match=what):
        parse_cif(text_)


@pytest.mark.parametrize("text_, what", [
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
    ("controllable a; plant P: location L; end", "no initial location"),
    ("controllable a; plant P: disc int[0..2] x = 5; location: initial; end", "outside"),
    ("controllable a; plant P: alphabet a; location: initial; end\n"
     "plant Q: location: initial; edge a do P.x := 1; end", "only update its own"),
    ("controllable a, b; plant P: alphabet a; location: initial; edge b; end",
     "not in its alphabet"),
    ("controllable a; plant P: location: initial; edge a when abs(1, 2); end", "argument"),
    ("controllable a; plant P: location: initial; edge a; @ end", "unexpected '@'"),
    ("plant P: disc int[0..3] x; disc int[0..3] y = x; location: initial; end",
     "not a constant"),
    ("const int N = 3 mod 0;", "division by zero"),
    ("const int N = 3 div (2 - 2);", "division by zero"),
    ("plant P: disc int[0..3] x; location: initial x = 1 div 0; end", "division by zero"),
    # CIF integers are 32-bit (ESCET CifMath: "Integer overflow").
    ("const int N = 2147483647 + 1;", "integer overflow"),
    ("const int N = 65536 * 32768;", "integer overflow"),
    ("const int N = 2147483648;", "integer overflow"),
    # No literal 2147483648, so not even -2147483648; CIF itself writes -(2147483647) - 1
    # (CIF manual v13.0, "Integer value ... -2147483648 is represented as -(2147483647) - 1").
    ("const int N = -2147483648;", "integer overflow"),
    ("const int N = -2147483647 - 2;", "integer overflow"),
    ("plant P: disc int[0..3000000000] x; location: initial; end", "integer overflow"),
])
def test_model_errors_raise(text_, what):
    with pytest.raises(CifFormatError, match=what):
        parse_cif(text_)


def test_unsupported_is_a_format_error():
    assert issubclass(UnsupportedCifError, CifFormatError)
    assert issubclass(CifFormatError, ValueError)
