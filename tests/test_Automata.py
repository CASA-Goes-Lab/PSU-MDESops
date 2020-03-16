from pathlib import Path

import DESops as d

cwd = Path(__file__).parent.resolve()


def test_parallel_comp_3():
    g1 = d.Automata(str(cwd.joinpath("models", "model1.fsm")))
    assert g1.vs[1]["marked"]

    g2 = d.Automata(str(cwd.joinpath("models", "model2.fsm")))
    assert g2.vs[1]["marked"]

    g3 = d.Automata(str(cwd.joinpath("models", "model3.fsm")))
    assert g3.vs[0]["marked"]

    g = d.parallel_comp([g1, g2, g3], save_marked_states=True)

    assert g.vs.find(marked=True)["name"] == [1, 1, 0]


def test_parallel_comp_same():
    g1 = d.Automata(str(cwd.joinpath("models", "model1.fsm")))
    g2 = d.Automata(str(cwd.joinpath("models", "model2.fsm")))
    g3 = g2.copy()

    g = d.parallel_comp([g1, g2, g3], save_marked_states=True)

    # FIXME: This assertion fails
    assert g.vs.find(marked=True)["name"] == [1, 1, 1]
