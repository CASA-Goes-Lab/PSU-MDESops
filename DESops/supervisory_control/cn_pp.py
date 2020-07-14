"""
Preprocessing functions for computing the supremal controllable
& normal supervisor.

"""

import copy

import igraph as ig
from pydash import flatten_deep

# Need to figure out what types for this still:
from DESops.automata.DFA import DFA
from DESops.basic_operations.construct_spa import construct_spa as construct_spa
from DESops.basic_operations.construct_subautomata import construct_subautomata
from DESops.basic_operations.generic_functions import write_transition_attributes


def cn_preprocessing(G_given, H_given, Euc, Euo, construct_SA=True, X_crit=None):
    """
    Function handling preprocessing for the SCNS.

    Ensures that the assumptions on the given specification and system automata
    in the SCNS algorithm are met.

    Generates H, G satisfying:

    1. H (the specification) is a strict subautomata of G
    2. G is an SPA (state partitioned automaton)

    Returns list of states that must be removed from G (these states will
    get removed in supremal_cn_supervisor, but not here). The
    states in G_states_to_delete are indices of vertices in G.

    Returns tuple of [spec Graph, system Graph, list of states]

    Parameters:
    H_given: given specification automaton, as an igraph Graph
    G_given: given system automaton, as an igraph Graph
    Euc: set of uncontrollable events
    Euo: set of unobservable events

    (Note that Euc, Euo cannot be optionally provided here, as it is
    assumed they were found in the supremal_cn_supervisor module).

    """

    # Save marked states of H
    # marked_H_given = [v.attributes().get("marked", False) for v in H_given.vs]

    if construct_SA:
        dead_state_index, H_t, G_t = construct_subautomata(
            H_given, G_given, False, True
        )
    else:
        G_t = G_given.copy()

    # rename states of G_t s.t. observer can be found
    sa_names = list(G_t.vs["name"])
    G_t.vs["name"] = [str(i) for i in range(G_t.vcount())]

    G = construct_spa(G_t, sa_names, Euo)

    # After constructing SPA equivalent of G, H can be found by deleting dead states in G
    G_states_to_delete = list()

    ttt = G.vs["name"]
    H = extract_H_from_G(G.copy(), G_states_to_delete, X_crit=X_crit)

    # Mark state in H accordingly to H_given
    # NOTE: cannot mark H by just looking at marked_H_given because the states in G_states_to_delete are not yet deleted from H here
    """
    H_given_states_in_H = [flatten_deep(v["name"])[0] for v in H.vs]

    H.vs["marked"] = [
        marked_H_given[int(index)-1] if index != "dead" else False
        for index in H_given_states_in_H
    ]
    """
    # Rewrite controllable/observable attributes to H, G
    add_event_attributes(H, G, Euo, Euc)

    return [H, G, G_states_to_delete]


def extract_H_from_G(G, states_to_delete, X_crit=None):
    """
    Find H from G by deleting 'dead' states in G
    G has names ((x,y), z) where:
        (x,y) is a pair of states from G_t, z is a set of states from Obs(G_t)
        dead states are those with the largest x in set of states in G
    G is a copy of original G, return value is H
    """
    sdfasdf = G.vs["name"]
    if X_crit:
        states_to_delete.extend(v.index for v in G.vs if v["name"][0] in X_crit)
    else:
        states_to_delete.extend(v.index for v in G.vs if v["name"][0] == "dead")

    G.vs["name"] = [(v, i) for i, v in enumerate(G.vs["name"])]
    # G.delete_vertices(states_to_delete)
    return G


def add_event_attributes(H, G, Euo, Euc):
    """
    NOTE: Might be outdated if attributes no longer get stored
    in list form (instead only storing labels as a Graph attribute,
    and using Euo/Euc sets). BUT, supremal_cn_supervisor might
    make use of the parallel lists, resulting in marginally faster
    computation at the expense of memory (but of course it's highly
    unlikely these are obviously impactful).

    Writes Euo, Euc attributes to H, G (the new automata).
    """
    if not Euc and Euo:
        H.es["contr"] = [True]
        G.es["contr"] = [True]
        H.es["obs"] = [True]
        G.es["obs"] = [True]
    else:
        write_transition_attributes(G, Euc, Euo)
        write_transition_attributes(H, Euc, Euo)

    return
