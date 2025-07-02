"""
Functions relevant to unary operations
"""

import warnings
from collections import deque

from DESops.automata.automata import Automata

# TODO This is just functions related to trim/accessibility
#      Rename to trim.py?


def find_non_trim(g: Automata) -> set:
    """
    Returns a set of vertex indices of the automaton that are not trim (i.e. inaccessible and/or incoaccessible).

    Parameters
    ----------
    g : Automata
        The automata to compute the non-trim states of

    Returns
    -------
    set[int]
        The indices of vertices that are not trim
    """
    bad_states = find_inacc(g)
    bad_states |= find_incoacc(g, bad_states)

    return bad_states


def construct_trim(g: Automata, inplace=False) -> Automata:
    """
    Construct the trim of the given automaton
    Parameters
    ----------
    g : Automata
        The automaton
    inplace : bool
        If True, the construct the trim in place modifying `g`. Otherwise construct a new automaton.

    Returns
    -------
    Automata
        The trimmed automaton
    """
    bad_states = find_non_trim(g)

    if not inplace:
        h = g.copy()
    else:
        h = g
    h.delete_vertices(h.vs.select(list(bad_states)))
    return h


def find_inacc(g: Automata, states_removed=None) -> set:
    """
    Returns a set of vertex indices of the automaton that are inaccessible,
    i.e., states that cannot be reached from the initial states.

    Parameters
    ----------
    g : Automata
        The automaton
    states_removed: set or NoneType
        The vertices in G that have been marked for deletion, but not yet been deleted. Or None to use the empty set.

    Returns
    -------
    set
        The inaccessible states
    """
    if g.vcount() == 0:
        # warnings.warn("Ac(): the given automaton is empty.")
        return set()

    if states_removed is None:
        states_removed = set()

    init_set = None
    try:
        init_set = set([v.index for v in g.vs.select(init=True)])
    except KeyError:
        init_set = {0}
    if init_set.issubset(states_removed):
        # warnings.warn("Initial state deleted.")
        return set([v.index for v in g.vs])

    good_states = init_set
    stack = deque(good_states)
    while len(stack) > 0:
        index = stack.popleft()
        neighbors = {
            out[0]
            for out in g.vs[index]["out"]
            if out[0] not in good_states and out[0] not in states_removed
        }
        good_states |= neighbors
        stack.extend(neighbors)

    bad_states = {v.index for v in g.vs if v.index not in good_states}
    return bad_states


def construct_acc(g: Automata, inplace=False) -> Automata:
    """
    Construct the accessible part of the given automaton

    Parameters
    ----------
    g : Automata
        The automaton
    inplace : bool
        If True, the construct the accessible part in place modifying `g`. Otherwise construct a new automaton.

    Returns
    -------
    Automata
        The accessible part of the automaton
    """
    bad_states = find_inacc(g)

    if not inplace:
        h = g.copy()
    else:
        h = g
    h.delete_vertices(h.vs.select(list(bad_states)))
    return h

def find_incoacc(g: Automata, states_removed=None) -> set:
    """
    Returns a set of vertex indices of G that are not incoaccessible,
    i.e., states that cannot reach the marked states.

    Parameters
    ----------
    g : Automata
        The automaton
    states_removed: set or NoneType
        The vertices in G that have been marked for deletion, but not yet been deleted. Or None to use the empty set.

    Returns
    -------
    set
        The incoaccessible states
    """
    if g.vcount() == 0:
        # warnings.warn("CoAc(): the given automaton is empty.")
        return set()

    if states_removed is None:
        states_removed = set()

    good_states = {
        v.index for v in g.vs.select(marked_eq=True) if v.index not in states_removed
    }
    if len(good_states) == 0:
        return set(range(g.vcount()))

    # backtrack states from marked states
    stack = deque(good_states)

    while len(stack) > 0:
        index = stack.pop()
        src_states = {
            src.index
            for src in g.vs[index].predecessors()
            if src.index not in good_states and src.index not in states_removed
        }
        good_states |= src_states
        stack.extend(src_states)

    bad_states = {v.index for v in g.vs if v.index not in good_states}
    return bad_states


def construct_coac(g: Automata, inplace=False) -> Automata:
    """
    Construct the coaccessible part of the given automaton

    Parameters
    ----------
    g : Automata
        The automaton
    inplace : bool
        If True, the construct the coaccessible part in place modifying `g`. Otherwise construct a new automaton.

    Returns
    -------
    Automata
        The coaccessible part of the automaton
    """
    bad_states = find_incoacc(g)

    if not inplace:
        h = g.copy()
    else:
        h = g
    h.delete_vertices(h.vs.select(list(bad_states)))
    return h
