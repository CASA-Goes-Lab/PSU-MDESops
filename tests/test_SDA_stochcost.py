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
    A_sum = [(A.vs["name"][e.source], e["label"], A.vs["name"][e.target]) for e in A.es]
    ttt = [(e.source, e["label"], e.target) for e in A.es]
    tttt = A.vs["name"]
    prism_path = pathlib.Path("prism-games-3.0-linux64/bin/")
    vertex_val, max_prob, att = d.SDA.MDP_max_reachability(A, X_crit, prism_path)
    print(vertex_val, max_prob)
    sss = att.vs["name"]
    ssss = att.vs["out"]
    print(",,,")
    att.summary()
    print(",,,")
    d.write_fsm
