import DESops as d
import tests.util as util


def test_type():
    # test if correctly recognize NFA vs DFA vs PFA

    dfa1, nfa1, nfa2 = util.load_nfa_dfa_models()

    assert isinstance(dfa1, d.DFA)
    assert isinstance(nfa1, d.NFA)
    assert isinstance(nfa2, d.NFA)

    # TODO: test copies and type-specific operations,
    # like parallel_comp


def test_parallel_comp():
    g1, g2, g3 = util.load_basic_models()

    g = d.parallel_comp([g1, g2, g3], save_marked_states=True)
    assert all(v["marked"] if v["name"] == ['mark1', 'mark2', 'init3'] else True for v in g.vs )
    assert all(v["marked"] if v["name"] == ['mark1', 'mark2', 'state3'] else True for v in g.vs )


def test_parallel_comp_same():
    g1, g2 = util.load_basic_models(1, 2)
    g3 = g2.copy()

    g = d.parallel_comp([g1, g2, g3], save_marked_states=True)

    # FIXME: This assertion fails
    assert g.vs.find(marked=True)["name"] == [1, 1, 1]


def test_product_comp():
    g2, g3 = util.load_basic_models(2, 3)

    g = d.product_comp([g2, g3], save_marked_states=True)

    assert g.vs.find(marked=True)["name"] == (2, 2)


def test_observer():
    G_t = util.load_model("models/G_t.fsm")
    obs = d.observer_comp(G_t)
    #G_t_obs = util.load_model("models/G_t_obs.fsm")
    return obs

def test_sup_controllable_normal():
    H_given, G_given, _ = util.load_cn_models()
    sup = d.supremal_cn_supervisor(G_given, H_given)

    sup._graph.write("sup.dot")
