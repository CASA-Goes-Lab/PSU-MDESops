import DESops as d
from tests.util import load_model


def test_AES():
    G = load_model("models/ex3AES.fsm")

    # G.plot()
    d.write_AES_SMV_model(G, "modelsSMV/ex3AES.smv")
