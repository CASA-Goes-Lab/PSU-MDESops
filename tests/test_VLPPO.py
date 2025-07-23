import DESops as d
from tests.util import load_model


def test_VLPPO_basic():
    """
    Test using models "plant1.fsm" and "spec1.fsm"
    """
    G = load_model("models/vlppo_tests/plant1.fsm")
    H = load_model("models/vlppo_tests/spec1.fsm")

    X_crit = set()
    X_crit.add("5")
    C = d.supervisor.offline_VLPPO(G, X_crit)
    assert C.vcount() == 7
    assert C.ecount() == 18


def test_VLPPO_empty():
    g = d.DFA()
    C = d.supervisor.offline_VLPPO(g, g)
    assert C.vcount() == 0

    g.add_vertices(3)
    h = d.DFA()
    C2 = d.supervisor.offline_VLPPO(g, h)
    assert C2.vcount() == 0
