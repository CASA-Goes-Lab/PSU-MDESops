import DESops as d
from tests.util import load_model


def test_2x2():
    G = load_model("models/SDA_tests/robust/ex_2_by_2_g.fsm")
    X_crit = set()
    X_crit.add("21")
    Ea = set()
    Ea.add(d.Event("rE"))
    Ea.add(d.Event("rN"))
    Ea.add(d.Event("rW"))
    Ea.add(d.Event("rS"))
    # euc, euo, arena = d.SDA.construct_robust_arena(G, X_crit, Ea)
    # assert arena.vcount() == 1437

    euc, euo, arena_red = d.SDA.construct_robust_arena(G, X_crit, Ea, reduced=True)

    assert arena_red.vcount() == 118
    arena_red.Euo = euo
    arena_red.Euc = euc
    ttttt = arena_red.vs["out"]
    arena_red_spec = d.offline_VLPPO(arena_red, X_crit=arena_red.X_crit)
    # arena_red_AES, _ = d.construct_AES(arena_red, arena_red.X_crit, True)
    # arena_red_sup = d.extract_AES_super(arena_red_AES)
    # Need to || compose to get realization of supervisor (since using VLPPO, same would go for AES)
    tt = arena_red_spec.vs["out"]
    arena_sup = d.parallel_comp([arena_red, arena_red_spec])
    ttt = arena_sup.vs["out"]
    super = d.SDA.select_robust_supervisor(arena_sup)

    ttt = super.vs["out"]

    G = load_model("models/SDA_tests/robust/ex_3_by_3_g.fsm")
    X_crit.remove("21")
    X_crit.add("33")
    euc, euo, arena3 = d.SDA.construct_robust_arena(G, X_crit, Ea)
    assert arena3.vcount() == 15876

    euc, euo, arena3_red = d.SDA.construct_robust_arena(G, X_crit, Ea, reduced=True)
    assert arena3_Red.vcount() == 1521


def test_2x2_2r():
    G = load_model("models/SDA_tests/robust/ex_2_by_2_2r_g.fsm")
    X_crit = set()
    X_crit.add("11,11")
    X_crit.add("12,12")
    X_crit.add("21,21")
    X_crit.add("22,22")
    Ea = set()
    Ea.add(d.Event("rE"))
    Ea.add(d.Event("rS"))
    Ea.add(d.Event("rW"))
    Ea.add(d.Event("rN"))
    euc, euo, arena_red = d.SDA.construct_robust_arena(G, X_crit, Ea, reduced=True)
    print(arena_red.vcount())
    assert arena_red.vcount() == 1856

    euc, euo, arena = d.SDA.construct_robust_arena(G, X_crit, Ea)
    print(arena.vcount())
    assert arena.vcount() == 442944


def test_maxrobust():
    G = load_model("models/SDA_tests/maxrobust/car_intersection_obs.fsm")
    X_crit = set()
    X_crit.add("5")
    Ea = set()
    Ea.add(d.Event("Rint"))
    order = [d.Event("Rout"), d.Event("Rint"), d.Event("Bout"), d.Event("Bint")]
    Rm = d.SDA.construct_maxrobust(G, X_crit, Ea, event_ordering=order)
    # Multiple (2?) possible supervisors returned from this construction (b/c VLPPO)
    # But both have 4 vertices; only transitions are different
    assert Rm.vcount() == 4
    v0_out = Rm.vs["out"][0]
    v0_Rout = [t[0] for t in v0_out if t[1] == d.Event("Rout")]
    # For this order, Rout should be the only non-self-loop at the initial state
    assert v0_Rout[0] != 0

    v1 = v0_Rout[0]
    v1_Bint = [t[0] for t in Rm.vs["out"][v1] if t[1] == d.Event("Bint")]
    assert v1_Bint[0] != v1

    v2 = v1_Bint[0]
    v2_Bout = [t[0] for t in Rm.vs["out"][v2] if t[1] == d.Event("Bout")]
    assert v2_Bout != v2

    v3 = v2_Bout[0]
    v3_self = [t[0] for t in Rm.vs["out"][v3] if t[0] == 3]
    assert len(v3_self) == 6
