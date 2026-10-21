"""
Trusted wrapper: event numbering and Automaton <-> plain lists.

Not verified. Kept to plain copying so it can be checked by reading, and tested by round trips
(tests/test_verified.py). Spec: DESops-proof/spec/wrapper.md, sections 3 and 4.
"""

from typing import Any, Dict, Iterable, List, Optional

from DESops.core.automaton import Automaton
from DESops.error import InvalidAutomatonError


class Encoded:
    """An automaton as plain lists, grouped by state (wrapper.md section 4).

    State x owns positions start[x] .. start[x+1]-1 of evt/dst; position k is the transition
    x --evt[k]--> dst[k]. Events are numbers 0..m-1 from an event table.
    """

    __slots__ = ("n", "m", "in_E", "in_Euc", "in_Euo", "init", "marked", "start", "evt", "dst")

    def __init__(self, n, m, in_E, in_Euc, in_Euo, init, marked, start, evt, dst):
        self.n: int = n
        self.m: int = m
        self.in_E: List[bool] = in_E
        self.in_Euc: List[bool] = in_Euc
        self.in_Euo: List[bool] = in_Euo
        self.init: List[bool] = init
        self.marked: List[bool] = marked
        self.start: List[int] = start
        self.evt: List[int] = evt
        self.dst: List[int] = dst


def event_table(automata: Iterable[Automaton]) -> Dict[Any, int]:
    """One numbering for all automata of an operation: {event: number}.

    Includes events used in transitions, so a transition whose event is missing from `events`
    (a W1 violation) reaches the verified checker instead of failing here with a KeyError.
    Same number <=> same dict key (Python == and hash), as in the unverified code.
    """
    table: Dict[Any, int] = {}
    for G in automata:
        for e in G.events:
            table.setdefault(e, len(table))
        for e in G.Euc:
            table.setdefault(e, len(table))
        for e in G.Euo:
            table.setdefault(e, len(table))
        for state in G.states:
            for e in state.out:
                table.setdefault(e, len(table))
    return table


def encode(G: Automaton, table: Dict[Any, int]) -> Encoded:
    """Copy G into plain lists. Raises InvalidAutomatonError for the two conditions the lists
    cannot represent: a non-bool marking, and an initial-state index that is not a state."""
    n = len(G.states)
    m = len(table)

    in_E = [False] * m
    in_Euc = [False] * m
    in_Euo = [False] * m
    for e in G.events:
        in_E[table[e]] = True
    for e in G.Euc:
        in_Euc[table[e]] = True
    for e in G.Euo:
        in_Euo[table[e]] = True

    init = [False] * n
    for x in G.init:
        if not (isinstance(x, int) and 0 <= x < n):
            raise InvalidAutomatonError(f"initial state {x!r} is not a state index")
        init[x] = True

    marked = []
    for state in G.states:
        if type(state.marked) is not bool:
            raise InvalidAutomatonError(
                f"state {state.name!r}: marked must be bool, got {state.marked!r}")
        marked.append(state.marked)

    start, evt, dst = [0], [], []
    for state in G.states:
        for event, targets in state.out.items():
            for t in targets:
                evt.append(table[event])
                dst.append(t)
        start.append(len(evt))

    return Encoded(n, m, in_E, in_Euc, in_Euo, init, marked, start, evt, dst)


def decode(enc: Encoded, event_of: List[Any], names: Optional[List[Any]] = None) -> Automaton:
    """Rebuild an Automaton from lists. `event_of[k]` is the event numbered k (list(table)).
    State names default to the index as a str; attributes are not carried."""
    G = Automaton(
        events=[event_of[e] for e in range(enc.m) if enc.in_E[e]],
        Euc=[event_of[e] for e in range(enc.m) if enc.in_Euc[e]],
        Euo=[event_of[e] for e in range(enc.m) if enc.in_Euo[e]],
    )
    for x in range(enc.n):
        G.add_state(None if names is None else names[x], enc.marked[x], init=enc.init[x])
    for x in range(enc.n):
        for k in range(enc.start[x], enc.start[x + 1]):
            G.add_transition(x, event_of[enc.evt[k]], enc.dst[k])
    return G
