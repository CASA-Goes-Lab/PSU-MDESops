import pathlib

import DESops as d
from tests.util import load_model


def test_SCA():
    G = load_model("models/SDA_tests/stochCostAttack/test_p_g.fsm")
    H = load_model("models/SDA_tests/stochCostAttack/test_p_h.fsm")
    tt = G.vs["out"]
    Ea = set()
    Ea.add(d.Event("rE"))

    X_crit = set()
    X_crit.add("4")

    A = d.SDA.construct_MDP(G, H, Ea, X_crit)

    prism_path = pathlib.Path("prism-4.6-linux64/bin/")
    vertex_val, max_prob, att = d.SDA.MDP_max_reachability(A, X_crit, prism_path)

    assert max_prob == 0.5

    assert vertex_val[0] == 0.5
    assert all(v == 1 for k, v in vertex_val.items() if k != 0)

    assert ("1", "A", "eps") in att.vs["name"]
    assert ("2", "B", d.Event("rN")) in att.vs["name"]
    assert ("3", "A", d.Event("rE")) in att.vs["name"]
    assert ("3", "A", "eps") in att.vs["name"]
    assert ("4", "B", d.Event("rN")) in att.vs["name"]


def test_SCA_empty():
    G = d.PFA()
    A = d.SDA.construct_MDP(G, G, set(), set())
    assert A.vcount() == 0
    prism_path = pathlib.Path("prism-4.6-linux64/bin/")
    vertex_val, max_prob, att = d.SDA.MDP_max_reachability(A, set(), prism_path)
    assert len(vertex_val) == 0
    assert max_prob is None
    assert att.vcount() == 0
