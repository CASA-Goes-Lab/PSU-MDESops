from pathlib import Path

import DESops as d

cwd = Path(__file__).parent.resolve()


def test_par_comp():
    g1 = d.Automata(str(cwd.joinpath("models", "model1.fsm")))
    assert len(g1.vs.select(marked_eq=True)) > 0

    g2 = d.Automata(str(cwd.joinpath("models", "model2.fsm")))
    assert len(g2.vs.select(marked_eq=True)) > 0

    g = d.parallel_comp([g1, g2], save_marked_states=True)

    assert len(g.vs.select(marked_eq=True)) > 0
