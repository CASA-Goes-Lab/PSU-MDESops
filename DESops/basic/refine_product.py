# pylint: disable=C0103
"""
Refine Automata by product.
"""
from ..basic.parallel_comp import parallel_comp as parallel_comp
from ..basic.product_comp import product_comp as product_comp


def refine_product(G_out, G1, G2):
    """
    Perform refinement by product
    G1 x G2 = Gout
    Assuming L(G1) is a subset of L(G2)...
    or L(G2) is a subset of L(G1)
    """
    product_comp(G_out, [G1, G2], True)


def refine_product_SCS(G_out, H, G):
    """
    First, parallel compose H,G
    Then refine by product H_p, G
    Written as G_out, but that should be H_out?
    """
    H_p = ig.Graph(directed=True)
    parallel_comp(H_p, [H, G], True)
    # map names of H_p from (h,g) to h, where h,g are states of H,G
    H_p.vs["name"] = [pair[0] for pair in H_p.vs["name"]]

    refine_product(G_out, H_p, G)
    # Change names of G_out vertices to be (old_name, G_index)
    G_out.vs["name"] = [(name, i) for i, name in enumerate(G_out.vs["name"])]
