from pathlib import Path

import DESops as d

cwd = Path(__file__).parent.resolve()


def load_model(path):
    return d.read_fsm(str(cwd.joinpath(path)))


def load_nfa_dfa_models():
    dfa1 = load_model("models/dfa_test1.fsm")
    nfa1 = load_model("models/nfa_test1.fsm")
    nfa2 = load_model("models/nfa_test2.fsm")
    return dfa1, nfa1, nfa2

def load_basic_models(*model):
    g1 = g2 = g3 = None
    load_all = len(model) == 0
    automata = []
    if 1 in model or load_all:
        g1 = d.DFA()
        d.read_fsm(str(cwd.joinpath("models", "model1.fsm")), g1)
        assert g1.vs[1]["marked"]
        automata.append(g1)
    if 2 in model or load_all:
        g2 = d.DFA()
        d.read_fsm(str(cwd.joinpath("models", "model2.fsm")), g2)
        assert g2.vs[1]["marked"]
        automata.append(g2)
    if 3 in model or load_all:
        g3 = d.DFA()
        d.read_fsm(str(cwd.joinpath("models", "model3.fsm")), g3)
        automata.append(g3)

    return automata


def load_cn_models() -> (d.DFA, d.DFA):
    H_t = d.DFA()
    G_t = d.DFA()
    H2 = d.DFA()
    d.read_fsm(str(cwd.joinpath("models", "H_t.fsm")), H_t)
    d.read_fsm(str(cwd.joinpath("models", "G_t.fsm")), G_t)
    d.read_fsm(str(cwd.joinpath("models", "H2.fsm")), H2)

    return (H_t, G_t, H2)
