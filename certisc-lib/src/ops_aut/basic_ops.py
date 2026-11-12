"""
Public basic operations on Automaton objects.

Each one calls the Verus-verified Rust code (certisc-lib/rust/verified/src/ops_aut/) through
the extension rust_core._rs; the automaton is already in Rust (ValidAutomaton._rs). This file is
trusted glue: it checks the arguments (state indices), translates event labels to numbers and
back, and gives the results their state names. `backend="rust"` is the only implementation
(the parameter stays for a later one).

Each function takes a ValidAutomaton (validated once: nothing is checked or encoded again) or a
plain Automaton (validated and encoded on every call; fine for one-off calls, slow in loops).
Spec: certisc-proof/spec/basic_ops.md.
"""

import warnings
from typing import Any, Iterable, List, Optional, Tuple, Union

from core_aut import Automaton, ValidAutomaton, validate

_BACKENDS = ("rust",)


class EmptyAutomatonWarning(UserWarning):
    """An operation returned the empty automaton (no states): every state was deleted, or every
    initial state was (an automaton with states but no initial state is not valid, W3)."""


def _valid(G: Union[ValidAutomaton, Automaton], backend: str) -> ValidAutomaton:
    """G as a ValidAutomaton (validated now if it is a plain Automaton); checks `backend`."""
    if backend not in _BACKENDS:
        raise ValueError(f"unknown backend {backend!r}; available: {_BACKENDS}")
    return G if isinstance(G, ValidAutomaton) else validate(G)


def _states(V: ValidAutomaton, states: Iterable[int]) -> List[int]:
    """`states` as a list, after checking that each is a state index of V (the `requires` of
    the Rust functions)."""
    S = list(states)
    n = V.num_states
    for x in S:
        if not (isinstance(x, int) and 0 <= x < n):
            raise ValueError(f"{x!r} is not a state index of G")
    return S


def next_states(G: Union[ValidAutomaton, Automaton], states: Iterable[int], event: Any, *,
                witnesses: bool = False,
                backend: str = "rust") -> Union[List[int], Tuple[List[int], List[int]]]:
    """The states reached from `states` by `event`, each once.

    With witnesses=True, also a list `sources`: states reached[i] is reached from sources[i]
    (a state of `states`) by `event`.

    Verified (rust/verified/src/ops_aut/basic_ops.rs): the result is exactly Lean's
    `step f S e`, with no repeats. Raises InvalidAutomatonError if G is not a valid automaton,
    ValueError for a state index out of range or an unknown backend."""
    V = _valid(G, backend)
    S = _states(V, states)
    e = V._event_number(event)
    if e is None:                            # no transition uses it: nothing is reached
        return ([], []) if witnesses else []
    out, src = V._rs.next_states(S, e)
    return (out, [S[j] for j in src]) if witnesses else out


def active_events(G: Union[ValidAutomaton, Automaton], states: Iterable[int], *,
                  witnesses: bool = False,
                  backend: str = "rust") -> Union[List[Any], Tuple[List[Any], List[int]]]:
    """The events enabled at some state of `states` (event labels), each once.

    With witnesses=True, also a list `sources`: event events[i] is enabled at the state
    sources[i] (a state of `states`).

    Verified (rust/verified/src/ops_aut/basic_ops.rs): exactly Lean's `active f S`. Raises
    InvalidAutomatonError if G is not a valid automaton, ValueError for a state index out of
    range or an unknown backend."""
    V = _valid(G, backend)
    S = _states(V, states)
    out, src = V._rs.active_events(S)
    labels = [V._event_of[e] for e in out]
    return (labels, [S[j] for j in src]) if witnesses else labels


def active_events_at(G: Union[ValidAutomaton, Automaton], state: int) -> List[Any]:
    """The events enabled at one state (event labels), each once, in event-number order.

    Same as active_events(G, [state]). Raises InvalidAutomatonError if G is not a valid
    automaton, ValueError for a state index out of range."""
    return active_events(G, [state])


def reachable(G: Union[ValidAutomaton, Automaton], states: Optional[Iterable[int]] = None, *,
              witnesses: bool = False, backend: str = "rust"
              ) -> Union[List[int], Tuple[List[int], List[Optional[Tuple[int, Any]]]]]:
    """The states reachable from `states` (default: the initial states), each once, in
    breadth-first order.

    With witnesses=True, also a list `parents`: parents[i] is None if reached[i] is a start
    state, else (x, e): reached[i] is reached from the state x by the event e, and x comes
    earlier in the list. Following the parents back gives a shortest word to each state.

    Verified (rust/verified/src/ops_aut/reach.rs): the result is exactly Lean's `reach f S`,
    and the witnesses are correct. (Breadth-first order, hence shortest words, is tested, not
    proved.) Spec: certisc-proof/spec/reach.md.

    Raises InvalidAutomatonError if G is not a valid automaton, ValueError for a state index
    out of range or an unknown backend."""
    V = _valid(G, backend)
    S = sorted(V.init) if states is None else _states(V, states)
    out, par = V._rs.reachable(S)
    if not witnesses:
        return out
    return out, [None if w is None else (out[w[0]], V._event_of[w[1]]) for w in par]


def coreachable(G: Union[ValidAutomaton, Automaton], states: Optional[Iterable[int]] = None, *,
                witnesses: bool = False, backend: str = "rust"
                ) -> Union[List[int], Tuple[List[int], List[Optional[Tuple[Any, int]]]]]:
    """The states from which some state of `states` (default: the marked states) can be
    reached, each once, in breadth-first order from those target states.

    With witnesses=True, also a list `nexts`: nexts[i] is None if coreached[i] is a target
    state, else (e, y): the event e leads from coreached[i] to the state y, and y comes earlier
    in the list. Following the nexts gives a shortest word from each state to a target.

    Verified (rust/verified/src/ops_aut/reach.rs): exactly Lean's `coreach f Xm`, over the
    reverse index (built in Rust on the first call for a ValidAutomaton, then kept; for a plain
    Automaton, on every call). Spec: certisc-proof/spec/coreach.md.

    Raises InvalidAutomatonError if G is not a valid automaton, ValueError for a state index
    out of range or an unknown backend."""
    V = _valid(G, backend)
    Xm = sorted(V.marked) if states is None else _states(V, states)
    out, nxt = V._rs.coreachable(Xm)
    if not witnesses:
        return out
    return out, [None if w is None else (V._event_of[w[1]], out[w[0]]) for w in nxt]


def delete_states(G: Union[ValidAutomaton, Automaton], states: Iterable[int], *,
                  backend: str = "rust") -> ValidAutomaton:
    """A new automaton: G without the given states (indices; repeats are fine) and without the
    transitions into or out of them. The kept states keep their names, flags and order, and are
    renumbered 0, 1, ...; the events (and Euc, Euo) are unchanged.

    If every initial state is deleted (or every state), the result is the empty automaton, with
    an EmptyAutomatonWarning: an automaton with states but no initial state is not valid (W3).

    G itself is not changed. The result is a new ValidAutomaton; the old one is freed when
    nothing refers to it any more (e.g. after V = delete_states(V, S)). To delete several sets,
    pass their union: one copy instead of several.

    Verified (rust/verified/src/ops_aut/delete.rs): the result is exactly G with the states
    deleted (Lean `Automaton.IsDeletion`), and a valid automaton. Spec:
    certisc-proof/spec/delete_states.md.

    Raises InvalidAutomatonError if G is not a valid automaton, ValueError for a state index
    out of range or an unknown backend."""
    V = _valid(G, backend)
    dele = [False] * V.num_states
    for x in _states(V, states):
        dele[x] = True
    return _wrap(V, V._rs.delete_states(dele), "delete_states")


def accessible(G: Union[ValidAutomaton, Automaton], *,
               backend: str = "rust") -> ValidAutomaton:
    """The accessible part of G: a new automaton with only the states reachable from an initial
    state (reachable(G)), and the transitions between them. Same as
    delete_states(G, the states not in reachable(G)).

    Verified (rust/verified/src/ops_aut/delete.rs): exactly Lean's IsDeletion of the states
    outside Ac(G). Raises InvalidAutomatonError if G is not a valid automaton, ValueError for an
    unknown backend."""
    V = _valid(G, backend)
    return _wrap(V, V._rs.accessible(), "accessible")


def coaccessible(G: Union[ValidAutomaton, Automaton], *,
                 backend: str = "rust") -> ValidAutomaton:
    """The coaccessible part of G: a new automaton with only the states from which a marked
    state can be reached (coreachable(G)), and the transitions between them. Same as
    delete_states(G, the states not in coreachable(G)).

    If no initial state is coaccessible (so Lm(G) is empty), the result is the empty automaton,
    with an EmptyAutomatonWarning.

    Verified (rust/verified/src/ops_aut/delete.rs): exactly Lean's IsDeletion of the states
    outside CoAc(G). Raises InvalidAutomatonError if G is not a valid automaton, ValueError for
    an unknown backend."""
    V = _valid(G, backend)
    return _wrap(V, V._rs.coaccessible(), "coaccessible")


def trim(G: Union[ValidAutomaton, Automaton], *, backend: str = "rust") -> ValidAutomaton:
    """The trim part of G: a new automaton with only the states that are both accessible
    (reachable(G)) and coaccessible (coreachable(G)), and the transitions between them.

    One deletion is enough: every path from a reachable state stays among reachable states, so
    "coaccessible in the accessible part" is "coaccessible in G" for those states.

    If no initial state is coaccessible (so Lm(G) is empty), the result is the empty automaton,
    with an EmptyAutomatonWarning.

    Verified (rust/verified/src/ops_aut/delete.rs): exactly Lean's IsDeletion of the states
    outside Ac(G) ∩ CoAc(G). Raises InvalidAutomatonError if G is not a valid automaton,
    ValueError for an unknown backend."""
    V = _valid(G, backend)
    return _wrap(V, V._rs.trim(), "trim")


def _wrap(V: ValidAutomaton, result, op: str) -> ValidAutomaton:
    """The ValidAutomaton for a Rust deletion result (RsAut, old): old[i] is the state of V that
    state i comes from, so it keeps its name. The Rust functions return the empty automaton
    exactly when no initial state is kept; warn then."""
    rs, old = result
    if rs.n == 0:
        warnings.warn(f"{op}: the result is the empty automaton (no initial state is kept)",
                      EmptyAutomatonWarning, stacklevel=3)
    names = V.names
    return ValidAutomaton._make(rs, list(V._event_of), [names[x] for x in old])


def parallel_2aut(G1: Union[ValidAutomaton, Automaton], G2: Union[ValidAutomaton, Automaton], *,
                  backend: str = "rust") -> ValidAutomaton:
    """The parallel composition G1 ‖ G2: a new automaton over the pairs of states reachable
    from the initial pairs. A shared event (in both alphabets) moves both automata together; a
    private event moves only its own automaton.

    State i is named (name1, name2), the names of its two states. Events: E1 ∪ E2; Euc and Euo:
    the unions. Marked: both states marked. L(G1 ‖ G2) = P1⁻¹ L(G1) ∩ P2⁻¹ L(G2), and the same
    for Lm. If an input has no states, the result is the empty automaton, with an
    EmptyAutomatonWarning.

    Verified (rust/verified/src/ops_aut/compose.rs): the result is a valid automaton and exactly
    Lean's IsComposition with parMode; the agreement check below is verified too (check_agree),
    and with it every event keeps its controllability and observability. Trusted: matching the
    two event tables by name. Spec: certisc-proof/spec/parallel.md.

    Raises InvalidAutomatonError if G1 or G2 is not a valid automaton; ValueError if a shared
    event is controllable in one and uncontrollable in the other (or observable in one and
    unobservable in the other), or for an unknown backend."""
    return _compose(G1, G2, True, backend, "parallel_2aut")


def product_2aut(G1: Union[ValidAutomaton, Automaton], G2: Union[ValidAutomaton, Automaton], *,
                 backend: str = "rust") -> ValidAutomaton:
    """The product G1 × G2: as parallel_2aut, but only shared events can occur. Private events
    stay in the alphabet (E1 ∪ E2) but are never enabled. L(G1 × G2) = L(G1) ∩ L(G2), and the
    same for Lm.

    Verified (rust/verified/src/ops_aut/compose.rs): exactly Lean's IsComposition with
    prodMode. Errors and warnings as parallel_2aut."""
    return _compose(G1, G2, False, backend, "product_2aut")


def _compose(G1, G2, par: bool, backend: str, op: str) -> ValidAutomaton:
    """Shared code of parallel_2aut and product_2aut (trusted glue)."""
    V1, V2 = _valid(G1, backend), _valid(G2, backend)
    rs, p1, p2, events = _compose_parts(V1, V2, par, op)
    if rs.n == 0:
        warnings.warn(f"{op}: the result is the empty automaton (an input has no states)",
                      EmptyAutomatonWarning, stacklevel=3)
    n1, n2 = V1.names, V2.names
    return ValidAutomaton._make(rs, events, [(n1[a], n2[b]) for a, b in zip(p1, p2)])


def _compose_parts(V1: ValidAutomaton, V2: ValidAutomaton, par: bool, op: str):
    """(rs, p1, p2, events): the Rust composition of V1 and V2, with the state labels and the
    output event table (also used by sup.supervisor, which needs p1)."""
    # Output event numbering: V1's numbers, then V2's private events in V2's order (the order
    # map_ok asks for). Events are matched by name (Python == and hash), as in event_table.
    events = list(V1._event_of)
    map2 = []
    for e in V2._event_of:
        k = V1._event_number(e)
        if k is None:
            k = len(events)
            events.append(e)
        map2.append(k)
    m = len(events)
    # Verified agreement check; Python only turns its answer into a message.
    code, e2 = V1._rs.agree(V2._rs, map2, m)
    if code != 0:
        what = ("controllable in one and uncontrollable in the other" if code == 1 else
                "observable in one and unobservable in the other")
        raise ValueError(f"{op}: shared event {V2._event_of[e2]!r} is {what}")
    rs, p1, p2 = V1._rs.compose(V2._rs, map2, m, par)
    return rs, p1, p2, events
