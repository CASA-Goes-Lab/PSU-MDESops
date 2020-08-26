"""
Functions relevant to unary operations
"""

import warnings
from collections import deque

from DESops.automata.automata import _Automata

### This is just functions related to trim/accessibility
# Rename to trim.py?


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
    if G.vcount() == 0:
        # warnings.warn("Ac(): the given automaton is empty.")
        return set()
    if 0 in states_removed:
        # warnings.warn("Initial state deleted.")
        return set([v.index for v in G.vs])

    good_states = {0}
    stack = deque(good_states)
    while len(stack) > 0:
        index = stack.popleft()
        neighbors = {
            out[0]
            for out in G.vs[index]["out"]
            if out[0] not in good_states and out[0] not in states_removed
        }
        good_states |= neighbors
        stack.extend(neighbors)

    bad_states = {v.index for v in G.vs if v.index not in good_states}
    return bad_states


def find_incoacc(G: _Automata, states_removed=set()) -> set:
    """
    Returns a list of vertex indices of G that are not incoaccessible and should be removed.

    states_removed: vertices in G that have been marked for deletion, but not yet been deleted.
    """
    if G.vcount() == 0:
        # warnings.warn("CoAc(): the given automaton is empty.")
        return set()

    good_states = {
        v.index for v in G.vs.select(marked_eq=True) if v.index not in states_removed
    }
    if len(good_states) == 0:
        return set(range(G.vcount()))

    # backtrack states from marked states
    stack = deque(good_states)

    while len(stack) > 0:
        index = stack.pop()
        src_states = {
            src.index
            for src in G.vs[index].predecessors()
            if src.index not in good_states and src.index not in states_removed
        }
        good_states |= src_states
        stack.extend(src_states)

    bad_states = {v.index for v in G.vs if v.index not in good_states}
    return bad_states
