# pylint: disable=C0103

"""
Contains helpful functions used in various operations.
"""
from collections.abc import Iterable

from dd.autoref import BDD


def find_obs_contr(S, Euc=set(), Euo=set(), E=set()):
    """
    For set of graphs S, find Euc and Euo if not provided.
    This way, checks for Euc, Euo as empty sets are done
    here, rather than at the place this function gets called
    (slight convenience).
    """
    if not isinstance(S, Iterable):
        S = [S]

    if not Euc:
        find_Euc(S, Euc)
    if not Euo:
        find_Euo(S, Euo)
    if not E:
        find_E(S, E)

    return (Euc, Euo, E)


def find_Euc(S, Euc):
    """
    Check set of graphs S to find uncontrollable events.
    """
    if not S:
        return set()
    if Euc:
        return
    try:
        for graph in S:
            if "contr" not in graph.es.attributes():
                continue
            G_uc = [trans["label"] for trans in graph.es if not trans["contr"]]
            Euc.update(G_uc)
    except TypeError:
        if "contr" not in S.es.attributes():
            return
        G_uc = [trans["label"] for trans in S.es if not trans["contr"]]
        Euc.update(G_uc)


def find_Euo(S, Euo):
    """
    Check set of graphs S to find unobservable events.
    """
    if not S:
        return set()
    if Euo:
        return
    try:
        for graph in S:
            if "obs" not in graph.es.attributes():
                continue
            G_uo = [trans["label"] for trans in graph.es if not trans["obs"]]
            Euo.update(G_uo)
    except TypeError:
        if "obs" not in S.es.attributes():
            return
        G_uo = [trans["label"] for trans in S.es if not trans["obs"]]
        Euo.update(G_uo)


def find_E(S, E):
    """
    Check set of graphs S to find all events.
    """
    if not S:
        return set()
    if E:
        return
    for graph in S:
        events = [trans["label"] for trans in graph.es]
        E.update(events)


def write_transition_attributes(G, Euc=set(), Euo=set()):
    """
    Given a graph G, and set of events Euc, Euo:
    Write obs/contr attributes to transitions of G
    Only writes Euc/Euo if provided (can optionally not be provided)
    """
    contr_list = list()
    obs_list = list()
    for edge in G.es:
        if Euc:
            if edge["label"] in Euc:
                contr_list.append(False)
            else:
                contr_list.append(True)
        if Euo:
            if edge["label"] in Euo:
                obs_list.append(False)
            else:
                obs_list.append(True)
    if Euc:
        G.es["contr"] = contr_list
    if Euo:
        G.es["obs"] = obs_list


def next_state_symbolic(state, event, G):
    # computes next state given set of state and set of event and DFA G
    # this is a symbolic operator: state is a formula over variables s0,...,sn (source variables) and event is a formula over variables e0,...,em (event variables)
    # returns a formula over source variables again

    next_state = G.symbolic["transitions"] & state & event
    bvar = {"s0", "s1", "e0"}
    next_state = G.symbolic["bdd"].quantify(next_state, bvar, forall=False)
    G.symbolic["bdd"].collect_garbage()
    print(next_state.to_expr())
    print(list(G.symbolic["bdd"].pick_iter(next_state)))
    return next_state
