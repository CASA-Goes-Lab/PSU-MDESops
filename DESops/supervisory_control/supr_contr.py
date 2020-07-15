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
from DESops.automata.DFA import DFA

from ..basic_operations.construct_subautomata import strict_subautomata
from ..basic_operations.product_comp import product_comp
from ..basic_operations.refine_product import refine_product_SCS
from ..basic_operations.unary import find_inacc


def supr_contr(G, H, Euc=None, mark_states=True, preprocess=True):
    """
    Parameters:
    G: igraph Graph representing the system as an automaton
    H: igraph Graph representing the specification as an automaton

    Euc: set of uncontrollable events
    Find the supremal controllable supervisor, given a plant G and specification H
    """

    if not Euc:
        Euc = G.Euc.union(H.Euc)

    if preprocess:
        (preH, preG) = strict_subautomata(H, G)
        # print(len(preH.vs))
        # print(preG.vs["out"])

        # H_pp = a.automata_ctor.construct_automata(H)
        # refine_product_SCS(H_pp, H, G)
        # H = H_pp
    else:
        import warnings

        warnings.warn(
            "\nComputing the supremal controllable sublanguage without strict subautomaton preprocessing\nAssuming that given H is a strict subautomaton of G"
        )
        preG = DFA(G)
        preH = DFA(H)
    # Compose G,H to find the supervisor H_o (which may have controllability-condition violations)

    # Check each state to see if the supervisor improperly disables uncontrollable events;
    # those states must be removed.

    # generate "in" attribute
    if "in" not in preH.vs.attributes():
        incoming_adj = [[] for _ in range(preH.vcount())]
        for e in preH.es():
            incoming_adj[e.target].append((e.source, e["label"]))
        preH.vs["in"] = incoming_adj

    # map alternative to vs.find()
    preG_name_dict = {v["name"]: v for v in preG.vs()}

    badstates = set()
    for vH in preH.vs:
        # state was removed from spec:
        if vH["name"] not in preG_name_dict:
            badstates.add(vH.index)
            continue
        vG = preG_name_dict[vH["name"]]

        # state violates controllability:
        evG = {x[1] for x in vG["out"]}
        evH = {x[1] for x in vH["out"]}
        if len(evG) != len(evH):
            for e in evG - evH:
                if e in preG.Euc:
                    badstates.add(vH.index)
                    break

    states_to_remove = set()
    while badstates:
        next_badstates = set()
        for x in badstates:
            for prev_state in preH.vs["in"][x]:
                if prev_state[1] in Euc and prev_state[0] not in states_to_remove:
                    next_badstates.add(prev_state[0])

        states_to_remove.update(badstates)
        badstates = next_badstates

    # remove inaccessible states:
    preH.delete_vertices(states_to_remove)
    inacc_states = find_inacc(preH)
    preH.delete_vertices(inacc_states)

    preH.generate_out()

    return preH


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
