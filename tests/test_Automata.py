import DESops as d
import tests.util as util


def test_type():
    # test if correctly recognize NFA vs DFA vs PFA

    dfa1, nfa1, nfa2 = util.load_nfa_dfa_models()

    assert isinstance(dfa1, d.DFA)
    assert isinstance(nfa1, d.NFA)
    assert isinstance(nfa2, d.NFA)

    # test error checking for NFA/DFA:
    dfa = d.DFA()
    dfa.add_vertices(2)
    dfa.add_edges([(0, 0), (0, 1)], ["a", "b"])
    error_caught = False

    dfa.add_edges([(1, 0)], ["a"])
    try:
        dfa.add_edges([(0, 0)], ["a"])
    except d.error.DeterminismError:
        error_caught = True

    assert error_caught
    error_caught = False
    try:
        dfa.add_edges([(1, 1), (1, 1)], ["c", "c"])
    except d.error.DeterminismError:
        error_caught = True

    assert error_caught

    assert dfa.ecount() == 3

    dfa.add_edges([(1, 1), (1, 0)], ["c", "d"])
    # TODO: test copies and type-specific operations,
    # like parallel_comp


def test_observer():
    G_t = util.load_model("models/G_t.fsm")
    obs = d.composition.observer(G_t)
    assert obs.vcount() == 5
    assert obs.ecount() == 6
    assert d.Event("a") in (v[1] for v in obs.vs["out"][0])

    for out in obs.vs["out"][0]:
        names = obs.vs["name"][out[0]]
        if out[1] == d.Event("a"):
            assert sorted(names) == ['3', '4', '5']
        if out[1] == d.Event("b"):
            assert sorted(names) == ['2','5']


def test_observer_empty():
    G = d.DFA()
    obs = d.composition.observer(G)
    assert obs.vcount() == 0


def test_trim():
    G = util.load_model("models/textbook/exmp_2-16_modified.fsm")
    inacc_states = {G.vs[i]["name"] for i in d.unary.find_inacc(G)}
    assert inacc_states == {"6", "7", "8"}

    incoacc_states = {G.vs[i]["name"] for i in d.unary.find_incoacc(G)}
    assert incoacc_states == {"3", "4", "5"}

    bad_states = {G.vs[i]["name"] for i in d.unary.trim(G)}
    assert bad_states == inacc_states | incoacc_states


def test_trim_empty():
    G = d.DFA()
    inacc_states = d.unary.find_inacc(G)
    assert inacc_states == set()


def test_reverse():
    g = util.load_model("models/textbook/fig_2-2.fsm")

    g = d.NFA(g)
    # should d.replace(g, inplace=True) ensure that g is an NFA (or convert?)

    # reverse transition tuples (source, target, label):
    a = d.Event("a")
    b = d.Event("b")
    transitions = {(1, 0, a), (0, 0, b), (1, 1, a), (0, 1, b)}

    g_r = d.reverse(g)
    assert {(t.source, t.target, t["label"]) for t in g_r.es} == transitions
    assert g_r.vs["init"] == [False, True]
    assert g_r.vs["marked"] == [True, False]

    d.reverse(g, inplace=True)
    assert {(t.source, t.target, t["label"]) for t in g.es} == transitions
    assert g.vs["init"] == [False, True]
    assert g.vs["marked"] == [True, False]


def test_complement():
    g = util.load_model("models/textbook/fig_2-1.fsm")

    g_c = d.complement(g)
    assert g_c.vcount() == 4
    assert g_c.ecount() == 12
    assert (3, d.Event("b")) in g_c.vs[0]["out"]
    assert g_c.vs["marked"] == [False, True, False, True]

    d.complement(g, inplace=True)
    assert g.vcount() == 4
    assert g.ecount() == 12
    assert (3, d.Event("b")) in g.vs[0]["out"]
    assert g.vs["marked"] == [False, True, False, True]
