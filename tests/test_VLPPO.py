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
    C = d.offline_VLPPO(G, X_crit)
    assert C.vcount() == 7
    assert C.ecount() == 18
