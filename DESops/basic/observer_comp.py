# pylint: disable=C0103
"""
Functions relevant to constructing an observer automaton from a partially-observed automaton.

Only observer_comp is used outside this module; the rest are included as helper functions
only used by observer_comp.
"""
from collections import OrderedDict

from ..basic.generic_functions import find_Euo
from ..basic.ureach import unobservable_reach, ureach_from_set


def observer_comp(
    g_po, g_obs, Euo=set(), save_state_names=False, save_marked_states=False
):
    """
    Compute an observer automata
    g_po: input partially observed automata
    g_obs: Obs(g_po)
    Euo: optionally provide set of unobservable events; if not provided, will attempt to find in g_po edge attributes
    save_state_names: TODO
    """

    if not g_po.vcount():
        return
    find_Euo([g_po], Euo)
    # 1. Determine x0_obs = u-reach(x0), add to X_obs
    x0_obs = set()
    unobservable_reach(x0_obs, 0, g_po, Euo)
    x0_obs = frozenset(x0_obs)
    X_obs, H = set(), set()
    Q = list()
    Q.append(x0_obs)
    X_obs.add(x0_obs)
    search(g_po, Q, Euo, X_obs, H)
    convert_to_graph(
        g_po, g_obs, X_obs, H, x0_obs, save_state_names, save_marked_states
    )


def search(g_po, Q, Euo, X_obs, H):
    """
    BFS of the states of g_po (the partially observed automaton).
    Uses queue-system via list Q.
    """
    while Q:
        q = Q.pop(0)
        active_events = set(g_po.es(_source_in=q)["label"])

        adjacent_states = {
            (frozenset({t.target for t in g_po.es(label_eq=e)(_source_in=q)}), e)
            for e in active_events
            if e not in Euo
        }
        adj_sets = ((t_ureach_from_set(S[0], g_po, Euo), S[1]) for S in adjacent_states)
        for s in adj_sets:
            if s[0] not in X_obs:
                Q.append(frozenset(s[0]))
                X_obs.add(frozenset(s[0]))
            H.add((q, s[1], frozenset(s[0])))
        # Older version, less comprehensions: (above is only marginally faster)
        """
        for e in active_events:
            if e in Euo: continue
            adjacent_states = {t.target for t in g_po.es(label_eq = e)(_source_in = q)}
            adjacent_set = set()
            ureach_from_set(adjacent_set,adjacent_states,g_po,Euo)
            if adjacent_set not in X_obs:
                Q.append(frozenset(adjacent_set))
                X_obs.add(frozenset(adjacent_set))
            H.add((q, e, frozenset(adjacent_set)))
        """


def convert_to_graph(
    g_po, g_obs, X_obs, H, init_set, save_state_names, save_marked_states
):
    """
    Convert sets/lists of states/transitions into final igraph Graph in g_obs.
    """
    g_obs.add_vertices(len(X_obs))
    X_obs.remove(init_set)
    vert_names = dict()
    vert_names_list = list()
    vert_names[init_set] = 0
    vert_names_list.append(init_set)
    for i, x in enumerate(X_obs, 1):
        vert_names_list.append(x)
        vert_names[x] = i
    edge_list = list(H)
    trans_labels = [q[1] for q in H]
    trans_pairs = [(vert_names[q[0]], vert_names[q[2]]) for q in H]
    g_obs.vs["name"] = vert_names_list
    g_obs.add_edges(trans_pairs)
    g_obs.es["label"] = trans_labels
    if save_marked_states:
        g_obs.vs["marked"] = [
            any(g_po.vs[v]["marked"] for v in v_set) for v_set in vert_names_list
        ]


def t_ureach_from_set(S, g, e):
    """
    Similar to ureach_from_set but with more set comprehensions, testing to see if any faster
    Seems to be no noticable difference, so will likely change back to using ureach_from_set
    """
    x_set = set(S)
    if not e:
        return x_set
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

    return x_set
