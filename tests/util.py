from pathlib import Path

import DESops as d

cwd = Path(__file__).parent.resolve()


def load_basic_models(*model):
    g1 = g2 = g3 = None
    load_all = len(model) == 0
    automata = []
    if 1 in model or load_all:
        g1 = d.Automata(str(cwd.joinpath("models", "model1.fsm")))
        assert g1.vs[1]["marked"]
        automata.append(g1)
    if 2 in model or load_all:
        g2 = d.Automata(str(cwd.joinpath("models", "model2.fsm")))
        assert g2.vs[1]["marked"]
        automata.append(g2)
    if 3 in model or load_all:
        g3 = d.Automata(str(cwd.joinpath("models", "model3.fsm")))
        assert g3.vs[0]["marked"]
        automata.append(g3)

    return automata
