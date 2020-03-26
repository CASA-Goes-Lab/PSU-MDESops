import DESops as d
from tests.util import load_basic_models


def test_parallel_comp():
    g1, g2, g3 = load_basic_models()

    g = d.parallel_comp([g1, g2, g3], save_marked_states=True)

    assert g.vs.find(marked=True)["name"] == [1, 1, 0]


def test_parallel_comp_same():
    g1, g2 = load_basic_models(1, 2)
    g3 = g2.copy()

    g = d.parallel_comp([g1, g2, g3], save_marked_states=True)

    # FIXME: This assertion fails
    assert g.vs.find(marked=True)["name"] == [1, 1, 1]


def test_product_comp():
    g2, g3 = load_basic_models(2, 3)

    g = d.product_comp([g2, g3], save_marked_states=True)

    assert g.vs.find(marked=True)["name"] == (2, 2)
