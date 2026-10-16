# pylint: disable=C0103
"""
Functions related to finding unobservable
and extended ubobservable reaches.
"""
import warnings
from abc import ABC, abstractmethod
from collections import deque
from collections.abc import Iterable
from typing import Set, Union


### TODO: remove these
# replace with UR class functionality instead?
# Benefits being caching results, which is repetititve code
# and readability (G.UR.from_set instead of G.ureach_from_set, etc.)
# Extended_ureach and ureach_ignore_states might be exceptions,
# but for the sake of readability might be better to move all these to a UR class
def unobservable_reach(x_set, state, g, e):
    """
    x_set: set of states to be expanded upon
    state: index of current vertex
    g: graph
    "label": keyword for edge label
    e: keys associated with unobserved
    """
    warnings.warn(
        "Deprecated: use automata UR class instead (e.g.  g.UR.from_set(states, events, freeze_result=False)"
    )
    x_set.add(state)
    if not e:
        return
    uc_neighbors = {
        t.target
        for t in g.es(_source=state)
        if t["label"] in e and t.target not in x_set
    }
    while uc_neighbors:
        x_set.update(uc_neighbors)
        uc_neighbors = {
            t.target
            for t in g.es(_source_in=uc_neighbors)
            if t["label"] in e and t.target not in x_set
        }

    return


def ureach_from_set(x_set, S, g, e):
    """
    Find the collected unobservable reach for all states in S
    x_set: where resultant UR set is stored
    S: set of states to search from (graph indicies)
    g: graph to search
    e: set of unobservable events to consider
    """
    warnings.warn(
        "Deprecated: use automata UR class instead (e.g.  g.UR.from_set(states, events, freeze_result=False)"
    )
    x_set.update(S)
    if not e:
        return

    uc_neighbors = {
        t.target
        for t in g.es(_source_in=S)
        if t["label"] in e and t.target not in x_set
    }
    while uc_neighbors:
        x_set.update(uc_neighbors)
        uc_neighbors = {
            t.target
            for t in g.es(_source_in=uc_neighbors)
            if t["label"] in e and t.target not in x_set
        }

    return


# def ureach_from_set_adj(S, g, e):
#         """
#         Finds the set of states in the unobservable reach from the given state.
#         """
#         if isinstance(S, set) or isinstance(S, frozenset):
#             states = set()
#             for x in S:
#                 states |= ureach_from_set_adj(x,g,e)

#             return states

#         visited = {S}
#         states_stack = deque(visited)
#         while len(states_stack) > 0:
#             state = states_stack.pop()
#             dests_by_unobs = {
#                 out[0]
#                 for out in g.vs[state]["out"]
#                 if out[1] in e and out[0] not in visited
#             }
#             visited |= dests_by_unobs
#             states_stack.extend(dests_by_unobs)

#         return visited


def ureach_from_set_adj(S, g, e):
    """
    Find the collected unobservable reach for all states in S
    S: set of states to search from (graph indicies)
    g: graph to search
    e: set of unobservable events to consider
    """
    warnings.warn(
        "Deprecated: use automata UR class instead (e.g.  g.UR.from_set(states, events, freeze_result=False)"
    )
    x_set = set()
    x_set.update(S)
    if not e:
        return x_set

    # adj_S = [t for s in S for t in g.vs["adj"][s] if t[1] in e and t[0] not in x_set]
    # print(S,adj_S)
    # uc_neighbors = {t.target for t in g.es(_source_in = S) if t["label"] in e and t.target not in x_set}
    uc_neighbors = {
        t[0] for s in S for t in g.vs["out"][s] if t[1] in e and t[0] not in x_set
    }
    # print(uc_neighbors)
    while uc_neighbors:
        x_set.update(uc_neighbors)
        uc_neighbors = {
            t[0]
            for s in uc_neighbors
            for t in g.vs["out"][s]
            if t[1] in e and t[0] not in x_set
        }
        # print(uc_neighbors)
        # uc_neighbors = {t.target for t in g.es(_source_in = uc_neighbors) if t["label"] in e and t.target not in x_set}

    return x_set


def ureach_from_set_adjdict(S, g, e):
    """
    Find the collected unobservable reach for all states in S
    S: set of states to search from (graph indicies)
    g: graph to search
    e: set of unobservable events to consider
    """
    warnings.warn(
        "Deprecated: use automata UR class instead (e.g.  g.UR.from_set(states, events, freeze_result=False)"
    )
    x_set = set()
    x_set.update(S)
    if not e:
        return x_set

    # adj_S = [t for s in S for t in g.vs["adj"][s] if t[1] in e and t[0] not in x_set]
    # print(S,adj_S)
    # uc_neighbors = {t.target for t in g.es(_source_in = S) if t["label"] in e and t.target not in x_set}
    uc_neighbors = {
        g.vs["out_dict"][s][ev]
        for s in S
        for ev in e
        if ev in g.vs["out_dict"][s] and g.vs["out_dict"][s][ev] not in x_set
    }
    # print(uc_neighbors)
    while uc_neighbors:
        x_set.update(uc_neighbors)
        uc_neighbors = {
            g.vs["out_dict"][s][ev]
            for s in uc_neighbors
            for ev in e
            if ev in g.vs["out_dict"][s] and g.vs["out_dict"][s][ev] not in x_set
        }
        # print(uc_neighbors)
        # uc_neighbors = {t.target for t in g.es(_source_in = uc_neighbors) if t["label"] in e and t.target not in x_set}

    return x_set


def ureach_from_set_adjlist(S, g, e, adj_list):
    warnings.warn(
        "Deprecated: use automata UR class instead (e.g.  g.UR.from_set(states, events, freeze_result=False)"
    )
    x_set = set()
    x_set.update(S)
    if not e:
        return x_set

    # adj_S = [t for s in S for t in g.vs["adj"][s] if t[1] in e and t[0] not in x_set]
    # print(S,adj_S)
    # uc_neighbors = {t.target for t in g.es(_source_in = S) if t["label"] in e and t.target not in x_set}
    labels = g.es["label"]

    # IS THIS FASTER THAN GETTING FROM THE OUT?
    cond = lambda edge: edge["label"] in e and edge.target not in x_set
    uc_neighbors = {g.es[t].target for s in S for t in adj_list[s] if cond(g.es[t])}
    while uc_neighbors:
        x_set.update(uc_neighbors)
        uc_neighbors = {
            g.es[t].target for s in uc_neighbors for t in adj_list[s] if cond(g.es[t])
        }
        # print(uc_neighbors)
        # uc_neighbors = {t.target for t in g.es(_source_in = uc_neighbors) if t["label"] in e and t.target not in x_set}

    return x_set


def extended_ureach(x_set, state, g, e, Euo):
    """
    Find the extended unobservable reach from a state in g.

    e_o: single observable event, set of events e
    Defined as unobservable reach via unobservable events e in E_uo, followed by the single observable event e_o in E_o
    Starting from state in g
    result stored in x_set
    """
    unobservable_reach(x_set, state, g, e)
    new_set = set()
    for new_state in x_set:
        for edge in g.es(_source=new_state):
            if edge["label"] in e and edge["label"] not in Euo:
                new_set.add(edge.target)
    x_set.update(new_set)
    return


def extended_ureach_from_set_adj(set_of_states, g, e, Euo):
    """
    Find extended_ureach for each state in set_of_states.

    set_of_states: states to begin from
    g: igraph Graph object
    e: events to consider
    Euo: set of unobservable events in g
    """
    x_set = ureach_from_set_adj(set_of_states, g, e.intersection(Euo))

    new_set = set()

    for state in x_set:
        new_states = set(
            t[0] for t in g.vs[state]["out"] if t[1] in e and t[1] not in Euo
        )
        new_set.update(new_states)

    x_set.update(new_set)
    return x_set


def extended_ureach_from_set(x_set, set_of_states, g, e, Euo):
    """
    Find extended_ureach for each state in set_of_states.

    set_of_states: states to begin from
    g: igraph Graph object
    e: events to consider
    Euo: set of unobservable events in g
    """
    ureach_from_set(x_set, set_of_states, g, e.intersection(Euo))

    new_set = set()

    for state in x_set:
        new_states = set(
            t[0] for t in g.vs[state]["out"] if t[1] in e and t[1] not in Euo
        )
        new_set.update(new_states)

    x_set.update(new_set)


def ureach_ignore_states(x_set, state, g, e, ignore):
    """
    Find the collected unobservable reach for all states in S
    x_set: where resultant UR set is stored
    S: set of states to search from (graph indicies)
    g: graph to search
    e: set of unobservable events to consider
    ignore: set of states to ignore
    """
    if state in ignore:
        return
    x_set.add(state)
    if not e:
        return

    uc_neighbors = {
        t.target
        for t in g.es(_source=state)
        if t["label"] in e and t.target not in x_set and t.target not in ignore
    }
    while uc_neighbors:
        x_set.update(uc_neighbors)
        uc_neighbors = {
            t.target
            for t in g.es(_source_in=uc_neighbors)
            if t["label"] in e and t.target not in x_set and t.target not in ignore
        }

    return
