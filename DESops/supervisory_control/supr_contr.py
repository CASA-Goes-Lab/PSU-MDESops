"""
Functions relevant to computing the supremal controllable supervisor of given
system and specification automata.

Largely relevent are the supremal_controllable_supervisor() and
supremal_controllable_supervisor_pp() functions which both will
return an igraph Graph as the SCS. supremal_controllable_supervisor_pp()
will perform preprocessing on the specification, and then immediately call
supremal_controllable_supervisor(), which does the actual construction.

Preprocessing is required if the specification does not meet the following
assumption:

K is a sublanguage of M (where the language of H is K, and the language of G is M,
i.e. L(H) = K, & L(G) = M).

The other functions are used in supremal_controllable_supervisor()

"""

import DESops.automata as a

from ..basic_operations.product_comp import product_comp
from ..basic_operations.refine_product import refine_product_SCS
from ..basic_operations.unary import find_inacc


def supr_contr(G, H, Euc=None, mark_states=False, preprocess=False):
    """
    Actual function to compute the SCS.
    Assumes K is a sublanguage of M (where L(H) = K, L(G) = M)
    (If this isn't the case, use supremal_controllable_supervisor_pp,
    as the processing ensures this assumption holds).

    Parameters:
    G: igraph Graph representing the system as an automaton
    H: igraph Graph representing the specification as an automaton

    Euc: set of uncontrollable events
    Find the supremal controllable supervisor, given a plant G and specification H
    """

    if not Euc:
        Euc = G.Euc.union(H.Euc)

    if preprocess:
        # Default False
        H_pp = a.automata_ctor.construct_automata(H)
        refine_product_SCS(H_pp, H, G)
        H = H_pp

    # Compose G,H to find the supervisor H_o (which may have controllability-condition violations)
    H_o = a.automata_ctor.construct_automata(H)
    # THIS PRODUCT IS NOT NECESSARY IF THE PREPROCESSING IS DONE OR IF H IS A STRICT SUBAUTOMATON OF G
    # product_comp([G, H], H_o, save_state_names=True)

    # Check each state to see if the supervisor improperly disables uncontrollable events;
    # those states must be removed.
    # print(G.Euc)
    badstates = {1}
    while len(badstates) > 0:
        badstates = set()
        for vH in H.vs:
            vG = G.vs.find(name=vH["name"])

            evG = {x[1] for x in vG["out"]}
            evH = {x[1] for x in vH["out"]}
            if evG != evH:
                for e in evG - evH:
                    if e in G.Euc:
                        badstates.add(vH.index)
                        print(vH["name"])

        H.delete_vertices(badstates)
    return H
    # states_to_remove = [
    #     i for i in range(0, H_o.vcount()) if invalid_state(G, H_o, Euc, i)
    # ]
    # states_removed = set()
    # # All other states that transition to the ones just removed via an uncontrollable event
    # # must also be removed (i.e. the control decision at those states would require disabling
    # # and uncontrollable event).
    # while states_to_remove:
    #     # Iterative search; completes when there are no new states to check (exhausted the
    #     # uncontrollable traces).
    #     # trim() to remove inaccessible states; potentially saves some computation.
    #     inacc_states = find_inacc(H_o, states_removed)
    #     states_removed.update(states_to_remove)
    #     states_removed.update(inacc_states)
    #     states_to_check = {
    #         e.source
    #         for e in H_o.es(_target_in=states_to_remove)
    #         if e["label"] in Euc and e.source not in states_removed
    #     }
    #     states_to_remove = states_to_check

    # H_o.delete_vertices(states_removed)

    # # if G has observable transitions noted, set those edges in H_o to also be un/observable
    # if "obs" in G.es.attributes():
    #     if G.es["obs"]:
    #         set_obs_attr(G.es(), H_o.es())

    # # if G has states marked, set those states in H_o to also be marked
    # if "marked" in G.vs.attributes() and mark_states:
    #     if G.vs["marked"]:
    #         set_marked_attr(G.vs(), H_o.vs())

    # return H_o


def set_obs_attr(G_es, H_o_es):
    """
    Find Eo
    """
    Eo = set(edge["label"] for edge in G_es if edge["obs"])

    # For events in H_o with Eo, set o/uo
    obs_list = list()
    for edge in H_o_es:
        if edge["label"] in Eo:
            obs_list.append(True)
        else:
            obs_list.append(False)

    H_o_es["obs"] = obs_list
    return


def set_marked_attr(G_vs, H_vs):
    """
    Mark states in H that are marked in G
    Does nothing it looks like
    """
    marked_list = list()
    for state in H_vs:
        G_assoc = state["name"][1]
        marked_list.append(G_vs[G_assoc]["marked"])
    return


def invalid_state(G, H, Euc, H_state):
    """
    Determines if the given state is invalid; that is, violates the
    controllability condition.

    Parameters:
    G: system automaton
    H: specification automaton
    Euc: set of uncontrollable events
    H_state: index of the state H in question

    Returns True if H_state violates the controllability condition. That is,
    if meeting the specification requires the controller H disable an uncontrollable
    transition present in the associated state in G.
    Returns False if H_state does not violate the controllability condition.

    This is checked by counting the number of uncontrollable transitions in
    H_state and the associated state in G; if the H state has less uncontrollable
    transitions leaving the state than the associated state, then it violates controllability
    and returns True.
    """
    H_uc_count = len([e for e in H.es(_source=H_state) if e["label"] in Euc])
    G_assoc_state = H.vs["name"][H_state][0]
    G_uc_count = len([e for e in G.es(_source=G_assoc_state) if e["label"] in Euc])
    return H_uc_count < G_uc_count
