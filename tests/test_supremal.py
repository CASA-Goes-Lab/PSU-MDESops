import DESops as d
from DESops.supervisory_control.cn_pp import cn_preprocessing
from tests.util import load_cn_models, same_size


"""
def test_preprocessing_mark():
    H_given, G_given, _ = load_cn_models()

    Euc = H_given.Euc | G_given.Euc
    Euo = H_given.Euo | G_given.Euo

    H, G, deleted = cn_preprocessing(H_given, G_given, Euc, Euo)
    assert len(G.vs.select(marked_eq=True)) == 3
    assert len(H.vs.select(marked_eq=True)) == 2
"""


def test_scn_all():
    g1 = d.read_fsm("tests/models/scn_tests/cn_test1_g.fsm")
    g1_pp = d.read_fsm("tests/models/scn_tests/cn_test1_g_pp.fsm")

    h1 = d.read_fsm("tests/models/scn_tests/cn_test1_h.fsm")
    h1_pp = d.read_fsm("tests/models/scn_tests/cn_test1_h_pp.fsm")

    h_n = d.read_fsm("tests/models/scn_tests/cn_test1_h_n.fsm")

    Euc = g1.Euc | h1.Euc
    Euo = g1.Euo | h1.Euo
    h1_pp_test, g1_pp_test, _ = cn_preprocessing(h1, g1, Euc, Euo)

    assert same_size(g1_pp, g1_pp_test)

    h1 = d.DFA()
    d.read_fsm("tests/models/scn_tests/cn_test1_h.fsm", h1)

    h1_n_test = d.supr_contr_norm(g1, h1)

    assert same_size(h_n, h1_n_test)


def test_supr_contr_1():
    g1 = d.read_fsm("tests/models/sc_tests/book_ex_3_11_G.fsm")
    h1 = d.read_fsm("tests/models/sc_tests/book_ex_3_11_H.fsm")

    C_test = d.supr_contr(g1, h1, preprocess=True)
    assert C_test.vcount() == 0


def test_supr_contr_2():
    g1 = d.read_fsm("tests/models/sc_tests/G2.fsm")
    h1 = d.read_fsm("tests/models/sc_tests/H2.fsm")

    C_test = d.supr_contr(g1, h1, preprocess=True)
    assert C_test.vcount() == 4
    assert C_test.ecount() == 5
