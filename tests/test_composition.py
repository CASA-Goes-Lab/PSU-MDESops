import DESops as d
import tests.util as util


def test_product():
    G1 = util.load_model("models/textbook/fig_2-1.fsm")
    G2 = util.load_model("models/textbook/fig_2-2.fsm")

    G = d.composition.product(G1, G2)

    states = {s["name"] for s in G.vs}
    marked_states = {ms["name"] for ms in G.vs.select(marked_eq=True)}
    assert states == {("x", "0"), ("x", "1")}
    assert marked_states == {("x", "1")}
    assert G.Euc == {d.Event("a")}


def test_parallel():
    G1, G2 = util.load_basic_models(1, 2)
    G3 = G2.copy()

    G = d.composition.parallel(G1, G2, G3)
    assert {ms["name"] for ms in G.vs.select(marked_eq=True)} == {
        (("mark1", "mark2"), "mark2"),
        (("mark1", "state2"), "state2"),
    }
