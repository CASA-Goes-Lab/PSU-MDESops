# pylint: disable=C0103

"""
Contains helpful functions used in various operations.
"""
from collections.abc import Iterable

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


def copy_event_sets(this, other):
    """
    Useful function to copy event sets from 'this' to 'other'.
    Event sets being the set of unobservable events Euo, the set
    of uncontrollable events Euc, and the set of compromised
    events Ea.

    Used for example in the parallel_comp function to handle
    copying attributes from an input set of automata to the
    automata resulting from the composition.

    this: either an automata or iteratable collection of automata,
        from which event sets will be copied.
    other: automata, target of the copying.

    If 'this' is an interable, the event sets copied to 'other'
    will be the set union of the automata in 'this'.

    """
    if isinstance(this, _Automata):
        other.Euo = this.Euo
        other.Euc = this.Euc
        other.Ea = this.Ea
    else:
        other.Euo = set.union(*[a.Euo for a in this])
        other.Euc = set.union(*[a.Euc for a in this])
        other.Ea = set.union(*[a.Ea for a in this])
