import DESops as d
from tests.util import load_model


def test_robust_2x2():
    G = load_model("models/SDA_tests/robust/rob_arena_ex1.fsm")
    X_crit = set()
    X_crit.add("4")
    Ea = set()
    Ea.add(d.Event("b"))

    # Should also work with explicit attack strategy. A here is the all-out strategy.
    # A = d.DFA()
    # A.add_vertex()
    # A.vs["name"] = ["A0"]
    # A.add_edges([(0,0),(0,0),(0,0),(0,0)], [d.Event("a"), d.Event("b"), d.SDA.inserted_event("b"), d.SDA.deleted_event("b")])

    arena = d.SDA.construct_robust_arena(G, X_crit, Ea)

    assert arena.vcount() == 26
    arena_spec = d.offline_VLPPO(arena, X_crit=arena.X_crit)
    arena_sup = d.parallel_comp([arena, arena_spec])

    assert arena_sup.vcount() == 13
    super = d.SDA.select_robust_supervisor(arena_sup)
    assert super.vcount() == 2 or super.vcount() == 3


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
