from DESops.supervisory_control.cn_pp import cn_preprocessing
from tests.util import load_cn_models


def test_preprocessing_mark():
    H_given, G_given, _ = load_cn_models()

    Euc = H_given.Euc | G_given.Euc
    Euo = H_given.Euo | G_given.Euo

    H, G, deleted = cn_preprocessing(H_given, G_given, Euc, Euo)

    assert (
        len(G.vs.select(marked_eq=True)) == 3 and len(H.vs.select(marked_eq=True)) == 2
    )
