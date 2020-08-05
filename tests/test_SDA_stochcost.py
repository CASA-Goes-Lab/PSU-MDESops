import DESops as d
from tests.util import load_model


def test_SCA():
    G = load_model("models/SDA_tests/stochCostAttack/test_p_g.fsm")
    H = load_model("models/SDA_tests/stochCostAttack/test_p_h.fsm")

    Ea = set()
    Ea.add(d.Event("rE"))

    X_crit = set()
    X_crit.add("4")

    cost_table = dict()
    cost_table[d.SDA.inserted_event("rE")] = 1
    cost_table[d.SDA.deleted_event("rE")] = 1

    A = d.SDA.construct_MDP(G, H, Ea, X_crit, cost_table, 30)
