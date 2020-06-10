"""
Functions relevant to unary operations
"""

import warnings

from DESops.automata.automata import _Automata


def trim(G: _Automata) -> set:
    """
    Returns a list of vertex indices of G that are inaccessible and/or incoaccessible.
    """
    bad_states = find_inacc(G)
    bad_states |= find_incoacc(G, bad_states)

    return bad_states


def find_inacc(G: _Automata, states_removed=set()) -> set:
    """
    Returns a list of vertex indices of G that are inaccessible and should be removed.

    states_removed: vertices in G that have been marked for deletion, but not yet been deleted.
    """
    Q = list()
    Q.append({0})
    good_states = set()
    good_states.add(0)
    while Q:
        q = Q.pop(0)
        neighbors = {
            t.target
            for t in G.es(_source_in=q)
            if t.target not in good_states and t.target not in states_removed
        }
        if not neighbors:
            continue
        good_states.update(neighbors)
        Q.append(frozenset(neighbors))

    bad_states = {v.index for v in G.vs if v.index not in good_states}
    return bad_states


def find_incoacc(G: _Automata, states_removed=set()) -> set:
    """
    Returns a list of vertex indices of G that are not incoaccessible and should be removed.

    states_removed: vertices in G that have been marked for deletion, but not yet been deleted.
    """

    marked_states = {v.index for v in G.vs.select(marked_eq=True)}
    good_states = set()

    if len(marked_states) == 0:
        return good_states

    for state in G.vs:
        if state in states_removed:
            continue

        if state in marked_states:
            good_states.add(state.index)
            continue

        with warnings.catch_warnings():
            warnings.simplefilter("ignore", RuntimeWarning)
            for mstate in marked_states:
                shortest_path = G._graph.get_shortest_paths(state, mstate)[0]
                if len(shortest_path) > 0:
                    good_states.add(state.index)
                    break

    bad_states = {v.index for v in G.vs if v.index not in good_states}
    return bad_states
