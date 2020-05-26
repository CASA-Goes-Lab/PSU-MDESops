# pylint: disable=C0103
"""
Refine Automata by product.
"""
from DESops import automata
from DESops.basic_operations.parallel_comp import parallel_comp as parallel_comp
from DESops.basic_operations.product_comp import product_comp as product_comp


def refine_product(G_out, G1, G2):
    """
    Perform refinement by product
    G1 x G2 = Gout
    Assuming L(G1) is a subset of L(G2)...
    or L(G2) is a subset of L(G1)
    """
    product_comp([G1, G2], G_out, True)


def refine_product_SCS(G_out, H, G):
    """
    First, parallel compose H,G
    Then refine by product H_p, G
    Written as G_out, but that should be H_out?
    """
    #H_p = ig.Graph(directed=True)
    H_p = automata.DFA()
    parallel_comp([H, G], H_p, True)
    # map names of H_p from (h,g) to h, where h,g are states of H,G
    H_p.vs["name"] = [pair[0] for pair in H_p.vs["name"]]

    refine_product(G_out, H_p, G)
    # Change names of G_out vertices to be (old_name, G_index)
    G_out.vs["name"] = [(name, i) for i, name in enumerate(G_out.vs["name"])]
