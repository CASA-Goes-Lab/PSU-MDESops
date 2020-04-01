from pathlib import Path

from DESops.Automata import Automata

cwd = Path(__file__).parent.resolve()


def load_basic_models(*model):
    g1 = g2 = g3 = None
    load_all = len(model) == 0
    automata = []
    if 1 in model or load_all:
        g1 = Automata(str(cwd.joinpath("models", "model1.fsm")))
        assert g1.vs[1]["marked"]
        automata.append(g1)
    if 2 in model or load_all:
        g2 = Automata(str(cwd.joinpath("models", "model2.fsm")))
        assert g2.vs[1]["marked"]
        automata.append(g2)
    if 3 in model or load_all:
        g3 = Automata(str(cwd.joinpath("models", "model3.fsm")))
        assert g3.vs[0]["marked"]
        automata.append(g3)

    return automata


def load_cn_models() -> (Automata, Automata):
    H_t = Automata(str(cwd.joinpath("models", "H_t.fsm")))
    G_t = Automata(str(cwd.joinpath("models", "G_t.fsm")))
    H2 = Automata(str(cwd.joinpath("models", "H2.fsm")))

    return (H_t, G_t, H2)
