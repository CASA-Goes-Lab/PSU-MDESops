import DESops.supervisory_control.supervisor as sup
import tests.util as util


def test_supc():
    G = util.load_model("models/sc_tests/book_ex_3_11_G.fsm")
    H = util.load_model("models/sc_tests/book_ex_3_11_H.fsm")

    C = sup.supremal_sublanguage(G, H, mode=sup.Mode.CONTROLLABLE)
    assert C is None


def test_preprocessing_mark():
    H_given, G_given, _ = util.load_cn_models()

    Euc = H_given.Euc | G_given.Euc
    Euo = H_given.Euo | G_given.Euo
    G_given.Euc, G_given.Euo, H_given.Euc, H_given.Euo = Euc, Euo, Euc, Euo

    G, H = sup.preprocessing(G_given, H_given)
    assert len(G.vs.select(marked_eq=True)) == 3
    assert len(H.vs.select(marked_eq=True)) == 2


def test_supremal_controllable_normal_sublanguage():
    g1 = util.load_model("models/scn_tests/cn_test1_g.fsm")
    g1_pp = util.load_model("models/scn_tests/cn_test1_g_pp.fsm")

    h1 = util.load_model("models/scn_tests/cn_test1_h.fsm")

    h_n = util.load_model("models/scn_tests/cn_test1_h_n.fsm")

    Euc = g1.Euc | h1.Euc
    Euo = g1.Euo | h1.Euo
    g1.Euc, g1.Euo, h1.Euc, h1.Euo = Euc, Euo, Euc, Euo
    g1_pp_test, h1_pp_test = sup.preprocessing(g1, h1)

    assert util.same_size(g1_pp, g1_pp_test)

    h1 = util.load_model("models/scn_tests/cn_test1_h.fsm")

    h1_n_test = sup.supremal_sublanguage(g1, h1, mode=sup.Mode.CONTROLLABLE_NORMAL)

    assert util.same_size(h_n, h1_n_test)


def test_preprocess():
    G = util.load_model("models/textbook/fig_3-21_G.fsm")
    H = util.load_model("models/textbook/fig_3-21_H.fsm")

    Gpp, Hpp = sup.preprocessing(G, H)
    pass


def test_supcn_paper():
    G = util.load_model("models/cho-marcus-1989/fig_1-G.fsm")
    H = util.load_model("models/cho-marcus-1989/fig_1-H.fsm")

    S = sup.supremal_sublanguage(G, H, G.Euc, G.Euo)

    assert S is not None
