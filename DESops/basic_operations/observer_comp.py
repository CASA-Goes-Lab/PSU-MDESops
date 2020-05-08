# pylint: disable=C0103
"""
Functions relevant to constructing an observer automaton from a partially-observed automaton.

Only observer_comp is used outside this module; the rest are included as helper functions
only used by observer_comp.
"""
from DESops.automata.automata import _Automata
from DESops.basic_operations.generic_functions import find_Euo
from DESops.basic_operations.ureach import unobservable_reach


def observer_comp(part_obs, observer=None, Euo=set(), save_state_names=False, save_marked_states=False):
    """
    Compute an observer automata
    Constructs an observer of the given automata. Each state in the observer
    represents the best state estimate as a set of possible states the system
    could be in.

    Returns the observer as an Automata

    Requires the unobersvable events in the system be notated in some way.
    If Euo is not empty, those events will be used as the unobservable event set.
    Otherwise, the observer_comp function will check the igraph Graph edges
    for an "Euo" attribute, {G.es()["Euo"]} and from that construct the unobservable
    event set (legacy, shouldn't happen anymore; any initialization method from igraph Graphs
    should find the Euo set already).

    Parameters:
    save_state_names (default True): currently does nothing (!!!!)
        Note: the thinking for this was that currently, state names ("name" vertex attribute)
        are sets of states from the original Automata. This parameter could avoid
        allowing unnecessarily saving this information. Change to be similar to parallel_comp,
        where the names just don't get assigned to the result?

    save_marked_states (default False):

    Usage:
    >>> O = observer(G)

    part_obs: part_obs partially observed automata
    observer: Obs(part_obs)
    Euo: optionally provide set of unobservable events; if not provided, will attempt to find in part_obs edge attributes
    """

    observer_defined = True
    if not observer:
        observer = _Automata()
        observer_defined = False
    if not part_obs.vcount():
        return
    find_Euo([part_obs._graph], Euo)
    # 1. Determine x0_obs = u-reach(x0), add to X_obs
    x0_obs = set()
    unobservable_reach(x0_obs, 0, part_obs._graph, Euo)
    x0_obs = frozenset(x0_obs)
    X_obs, H = set(), set()
    Q = list()
    Q.append(x0_obs)
    X_obs.add(x0_obs)
    search(part_obs._graph, Q, Euo, X_obs, H)
    convert_to_graph(
        part_obs._graph,
        observer._graph,
        X_obs,
        H,
        x0_obs,
        save_state_names,
        save_marked_states,
    )
    observer.Euc = set(part_obs.Euc)
    observer.Euo = set(part_obs.Euo)
    if not observer_defined:
        return observer


def search(part_obs, Q, Euo, X_obs, H):
    """
    BFS of the states of part_obs (the partially observed automaton).
    Uses queue-system via list Q.
    """
    adj_list = part_obs.get_inclist()
    while Q:
        q = Q.pop(0)

        #active_events = set(part_obs.es(_source_in=q)["label"])
        #active_events = set(e[1] for vert in q for e in part_obs.vs["out"][vert])
        active_events = set(part_obs.es["label"][e] for vert in q for e in adj_list[vert])
        
        """
        adjacent_states = {
            (frozenset({t.target for t in part_obs.es(label_eq=e)(_source_in=q)}), e)
            for e in active_events
            if e not in Euo
        }
        """
        # TODO: make this more readable
        set_of_states = lambda e : (frozenset(part_obs.es[t].target for vert in q for t in adj_list[vert] if part_obs.es[t]["label"] == e), e)
        adjacent_states = {
            (set_of_states(e))
            for e in active_events 
            if e not in Euo
        }
        


        #adjacent_states = {frozenset()}
        adj_sets = ((t_ureach_from_set(S[0], part_obs, Euo), S[1]) for S in adjacent_states)
        for s in adj_sets:
            if s[0] not in X_obs:
                Q.append(frozenset(s[0]))
                X_obs.add(frozenset(s[0]))
            H.add((q, s[1], frozenset(s[0])))
        # Older version, less comprehensions: (above is only marginally faster)

        """
        for e in active_events:
            if e in Euo: continue
            adjacent_states = {t.target for t in part_obs.es(label_eq = e)(_source_in = q)}
            adjacent_set = set()
            ureach_from_set(adjacent_set,adjacent_states,part_obs,Euo)
            if adjacent_set not in X_obs:
                Q.append(frozenset(adjacent_set))
                X_obs.add(frozenset(adjacent_set))
            H.add((q, e, frozenset(adjacent_set)))
        """


def convert_to_graph(
    part_obs, observer, X_obs, H, init_set, save_state_names, save_marked_states
):
    """
    Convert sets/lists of states/transitions into final igraph Graph in observer.
    """
    observer.add_vertices(len(X_obs))
    X_obs.remove(init_set)
    vert_names = dict()
    vert_names_list = list()
    vert_names[init_set] = 0
    vert_names_list.append(init_set)
    for i, x in enumerate(X_obs, 1):
        vert_names_list.append(x)
        vert_names[x] = i
    # edge_list = list(H)
    trans_labels = [q[1] for q in H]
    trans_pairs = [(vert_names[q[0]], vert_names[q[2]]) for q in H]
    observer.vs["name"] = vert_names_list
    observer.add_edges(trans_pairs)
    observer.es["label"] = trans_labels
    if save_marked_states:
        observer.vs["marked"] = [
            any(part_obs.vs[v]["marked"] for v in v_set) for v_set in vert_names_list
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
