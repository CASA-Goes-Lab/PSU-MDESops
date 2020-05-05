import DESops as d
from tests.util import load_model


def test_newfct():
    G = load_model("models/ex3AES.fsm")
    P = d.parallel_comp([G, G])
    P.plot()
