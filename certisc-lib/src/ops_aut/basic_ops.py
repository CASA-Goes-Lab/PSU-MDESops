"""
Public basic operations on Automaton objects. Each one calls an implementation:

- backend="verified" (default): the Nagini-verified code in verified_ops/, stripped of its
  contracts at import (core_aut/trusted/_strip.py).
- (later: backend="numpy", trusted via differential tests against the verified one.)

Each function takes a ValidAutomaton (validated once, encoding stored: nothing is checked or
encoded again) or a plain Automaton (validated and encoded on every call; fine for one-off
calls, slow in loops). Spec: certisc-proof/spec/basic_ops.md.
"""

import warnings
from pathlib import Path
from typing import Any, Iterable, List, Optional, Sequence, Tuple, Union

from core_aut import Automaton, InvalidAutomatonError, ValidAutomaton, validate
from core_aut.trusted._strip import load_stripped
from core_aut.trusted.delete_states import build_delete
from core_aut.trusted.encoding import Encoded
from core_aut.trusted.wrapper import validate_encoded

_verified = load_stripped(Path(__file__).parent / "verified_ops" / "basic_ops.py",
                          "ops_aut.verified_ops.basic_ops (stripped)")
_verified_reach = load_stripped(Path(__file__).parent / "verified_ops" / "reach.py",
                                "ops_aut.verified_ops.reach (stripped)")
_verified_coreach = load_stripped(Path(__file__).parent / "verified_ops" / "coreach.py",
                                  "ops_aut.verified_ops.coreach (stripped)")
# coreach.py calls reach.reachable through a normal import, which would run the version with its
# contracts; point it at the stripped one (the same code, minus contracts and lemma calls).
_verified_coreach.reachable = _verified_reach.reachable
_verified_delete = load_stripped(Path(__file__).parent / "verified_ops" / "delete.py",
                                 "ops_aut.verified_ops.delete (stripped)")
_BACKENDS = ("verified",)


class EmptyAutomatonWarning(UserWarning):
    """An operation returned the empty automaton (no states): every state was deleted, or every
    initial state was (an automaton with states but no initial state is not valid, W3)."""


def next_states(G: Union[ValidAutomaton, Automaton], states: Iterable[int], event: Any, *,
                witnesses: bool = False,
                backend: str = "verified") -> Union[List[int], Tuple[List[int], List[int]]]:
    """The states reached from `states` by `event`, each once.

    With witnesses=True, also a list `sources`: states reached[i] is reached from sources[i]
    (a state of `states`) by `event`.

    Raises InvalidAutomatonError if G is not a valid automaton, ValueError for a state index
    out of range or an unknown backend."""
    if backend not in _BACKENDS:
        raise ValueError(f"unknown backend {backend!r}; available: {_BACKENDS}")
    V = G if isinstance(G, ValidAutomaton) else validate(G)
    S = list(states)
    for x in S:
        if not (isinstance(x, int) and 0 <= x < V.num_states):
            raise ValueError(f"{x!r} is not a state index of G")
    e = V._event_number(event)
    if e is None:                            # no transition uses it: nothing is reached
        return ([], []) if witnesses else []
    enc = V._encoding()
    out, src, via, pos = [], [], [], {}
    _verified.next_states(enc.n, enc.m, enc.start, enc.evt, enc.dst, enc.in_E, S, e,
                          out, src, via, pos)
    if witnesses:
        return out, [S[j] for j in src]
    return out


def active_events(G: Union[ValidAutomaton, Automaton], states: Iterable[int], *,
                  witnesses: bool = False,
                  backend: str = "verified") -> Union[List[Any], Tuple[List[Any], List[int]]]:
    """The events enabled at some state of `states` (event labels), each once.

    With witnesses=True, also a list `sources`: event events[i] is enabled at the state
    sources[i] (a state of `states`).

    Raises InvalidAutomatonError if G is not a valid automaton, ValueError for a state index
    out of range or an unknown backend."""
    if backend not in _BACKENDS:
        raise ValueError(f"unknown backend {backend!r}; available: {_BACKENDS}")
    V = G if isinstance(G, ValidAutomaton) else validate(G)
    S = list(states)
    for x in S:
        if not (isinstance(x, int) and 0 <= x < V.num_states):
            raise ValueError(f"{x!r} is not a state index of G")
    labels, src = _active(V, S, use_index=isinstance(G, ValidAutomaton))
    if witnesses:
        return labels, [S[j] for j in src]
    return labels


def active_events_at(G: Union[ValidAutomaton, Automaton], state: int) -> List[Any]:
    """The events enabled at one state (event labels), each once, in event-number order.

    Same as active_events(G, [state]). Raises InvalidAutomatonError if G is not a valid
    automaton, ValueError for a state index out of range."""
    return active_events(G, [state])


def _active(V: ValidAutomaton, S: List[int], use_index: bool) -> Tuple[List[Any], List[int]]:
    """Run a verified active_events: over the active-event index (built and checked once per
    ValidAutomaton, then kept), or with a binary search per run (no index: for an Automaton,
    which is validated again on every call, building the index would cost more than it saves)."""
    enc = V._encoding()
    emark = [-1] * enc.m                     # one entry per event number (alphabet size)
    out, src, via = [], [], []
    if use_index:
        A, H = V._active_index()
        _verified.active_events_idx(enc.n, enc.m, enc.start, enc.evt, enc.dst, enc.in_E, A, H,
                                    S, emark, out, src, via)
    else:
        _verified.active_events(enc.n, enc.m, enc.start, enc.evt, enc.dst, enc.in_E, S, emark,
                                out, src, via)
    return [V._event_of[e] for e in out], src


def reachable(G: Union[ValidAutomaton, Automaton], states: Optional[Iterable[int]] = None, *,
              witnesses: bool = False, backend: str = "verified"
              ) -> Union[List[int], Tuple[List[int], List[Optional[Tuple[int, Any]]]]]:
    """The states reachable from `states` (default: the initial states), each once, in
    breadth-first order.

    With witnesses=True, also a list `parents`: parents[i] is None if reached[i] is a start
    state, else (x, e): reached[i] is reached from the state x by the event e, and x comes
    earlier in the list. Following the parents back gives a shortest word to each state.

    Verified core: verified_ops/reach.py. Spec: certisc-proof/spec/reach.md. Lean: `reach f S`,
    and `reach_eq_of_certificate`, which turns the verified properties (contains S, closed,
    witnesses) into "exactly the reachable states".

    Raises InvalidAutomatonError if G is not a valid automaton, ValueError for a state index
    out of range or an unknown backend."""
    if backend not in _BACKENDS:
        raise ValueError(f"unknown backend {backend!r}; available: {_BACKENDS}")
    V = G if isinstance(G, ValidAutomaton) else validate(G)
    enc = V._encoding()
    S = sorted(V.init) if states is None else list(states)
    for x in S:
        if not (isinstance(x, int) and 0 <= x < enc.n):
            raise ValueError(f"{x!r} is not a state index of G")
    mark = [-1] * enc.n                      # one entry per state
    out, par, via = [], [], []
    _verified_reach.reachable(enc.n, enc.start, enc.dst, S, mark, out, par, via)
    if not witnesses:
        return out
    parents = [None if p == -1 else (out[p], V._event_of[enc.evt[k]])
               for p, k in zip(par, via)]
    return out, parents


def coreachable(G: Union[ValidAutomaton, Automaton], states: Optional[Iterable[int]] = None, *,
                witnesses: bool = False, backend: str = "verified"
                ) -> Union[List[int], Tuple[List[int], List[Optional[Tuple[Any, int]]]]]:
    """The states from which some state of `states` (default: the marked states) can be
    reached, each once, in breadth-first order from those target states.

    With witnesses=True, also a list `nexts`: nexts[i] is None if coreached[i] is a target
    state, else (e, y): the event e leads from coreached[i] to the state y, and y comes earlier
    in the list. Following the nexts gives a shortest word from each state to a target.

    Verified core: verified_ops/coreach.py, over the reverse index (built and checked once per
    ValidAutomaton; for a plain Automaton, on every call). Spec: certisc-proof/spec/coreach.md.
    Lean: `coreach f Xm`, and `coreach_eq_of_certificate`.

    Raises InvalidAutomatonError if G is not a valid automaton, ValueError for a state index
    out of range or an unknown backend."""
    if backend not in _BACKENDS:
        raise ValueError(f"unknown backend {backend!r}; available: {_BACKENDS}")
    V = G if isinstance(G, ValidAutomaton) else validate(G)
    enc = V._encoding()
    Xm = sorted(V.marked) if states is None else list(states)
    for x in Xm:
        if not (isinstance(x, int) and 0 <= x < enc.n):
            raise ValueError(f"{x!r} is not a state index of G")
    rstart, rk, rsrc, pos = V._reverse_index()
    mark = [-1] * enc.n                      # one entry per state
    out, nxt, via = [], [], []
    _verified_coreach.coreachable(enc.n, enc.start, enc.dst, rstart, rk, rsrc, pos, Xm, mark,
                                  out, nxt, via)
    if not witnesses:
        return out
    nexts = [None if p == -1 else (V._event_of[enc.evt[rk[j]]], out[p])
             for p, j in zip(nxt, via)]
    return out, nexts


def delete_states(G: Union[ValidAutomaton, Automaton], states: Iterable[int], *,
                  backend: str = "verified") -> ValidAutomaton:
    """A new automaton: G without the given states (indices; repeats are fine) and without the
    transitions into or out of them. The kept states keep their names, flags and order, and are
    renumbered 0, 1, ...; the events (and Euc, Euo) are unchanged.

    If every initial state is deleted (or every state), the result is the empty automaton, with
    an EmptyAutomatonWarning: an automaton with states but no initial state is not valid (W3).

    G itself is not changed. The result is a new ValidAutomaton; the old one is freed when
    nothing refers to it any more (e.g. after V = delete_states(V, S)). To delete several sets,
    pass their union: one copy instead of several.

    Verified: the result is checked to be exactly G with the states deleted
    (verified_ops/delete.py; Lean `Automaton.IsDeletion`), then validated by the verified
    checker. Spec: certisc-proof/spec/delete_states.md.

    Raises InvalidAutomatonError if G is not a valid automaton, ValueError for a state index
    out of range or an unknown backend."""
    if backend not in _BACKENDS:
        raise ValueError(f"unknown backend {backend!r}; available: {_BACKENDS}")
    V = G if isinstance(G, ValidAutomaton) else validate(G)
    n = V.num_states
    dele = [False] * n
    for x in states:
        if not (isinstance(x, int) and 0 <= x < n):
            raise ValueError(f"{x!r} is not a state index of G")
        dele[x] = True
    return _delete(V, dele, "delete_states")


def accessible(G: Union[ValidAutomaton, Automaton], *,
               backend: str = "verified") -> ValidAutomaton:
    """The accessible part of G: a new automaton with only the states reachable from an initial
    state (reachable(G)), and the transitions between them. Same as
    delete_states(G, the states not in reachable(G)).

    Built from the verified reachable and delete_states (each proved); only the complement
    (which states to delete) is computed here. Raises InvalidAutomatonError if G is not a valid
    automaton, ValueError for an unknown backend."""
    if backend not in _BACKENDS:
        raise ValueError(f"unknown backend {backend!r}; available: {_BACKENDS}")
    V = G if isinstance(G, ValidAutomaton) else validate(G)
    dele = [True] * V.num_states
    for x in reachable(V):
        dele[x] = False
    return _delete(V, dele, "accessible")


def coaccessible(G: Union[ValidAutomaton, Automaton], *,
                 backend: str = "verified") -> ValidAutomaton:
    """The coaccessible part of G: a new automaton with only the states from which a marked
    state can be reached (coreachable(G)), and the transitions between them. Same as
    delete_states(G, the states not in coreachable(G)).

    If no initial state is coaccessible (so Lm(G) is empty), the result is the empty automaton,
    with an EmptyAutomatonWarning.

    Built from the verified coreachable and delete_states (each proved); only the complement is
    computed here. Raises InvalidAutomatonError if G is not a valid automaton, ValueError for an
    unknown backend."""
    if backend not in _BACKENDS:
        raise ValueError(f"unknown backend {backend!r}; available: {_BACKENDS}")
    V = G if isinstance(G, ValidAutomaton) else validate(G)
    dele = [True] * V.num_states
    for x in coreachable(V):
        dele[x] = False
    return _delete(V, dele, "coaccessible")


def trim(G: Union[ValidAutomaton, Automaton], *, backend: str = "verified") -> ValidAutomaton:
    """The trim part of G: a new automaton with only the states that are both accessible
    (reachable(G)) and coaccessible (coreachable(G)), and the transitions between them.

    One deletion is enough: every path from a reachable state stays among reachable states, so
    "coaccessible in the accessible part" is "coaccessible in G" for those states.

    If no initial state is coaccessible (so Lm(G) is empty), the result is the empty automaton,
    with an EmptyAutomatonWarning.

    Built from the verified reachable, coreachable and delete_states (each proved); only the
    intersection and complement are computed here. Raises InvalidAutomatonError if G is not a
    valid automaton, ValueError for an unknown backend."""
    if backend not in _BACKENDS:
        raise ValueError(f"unknown backend {backend!r}; available: {_BACKENDS}")
    V = G if isinstance(G, ValidAutomaton) else validate(G)
    co = [False] * V.num_states
    for x in coreachable(V):
        co[x] = True
    dele = [True] * V.num_states
    for x in reachable(V):
        if co[x]:
            dele[x] = False
    return _delete(V, dele, "trim")


def _delete(V: ValidAutomaton, dele: Sequence[bool], op: str) -> ValidAutomaton:
    """Delete the states x with dele[x] from V: the empty automaton (with a warning) if no
    initial state is kept; otherwise build (trusted), check exactness (verified), validate
    (verified)."""
    enc = V._encoding()
    if not any(enc.init[x] and not dele[x] for x in range(enc.n)):
        warnings.warn(f"{op}: the result is the empty automaton (no initial state is kept)",
                      EmptyAutomatonWarning, stacklevel=3)
        empty = Encoded(0, enc.m, enc.in_E, enc.in_Euc, enc.in_Euo, [], [], [0], [], [])
        return validate_encoded(empty, list(V._event_of), [])
    new_of, old_of, start2, evt2, dst2, init2, marked2, src2, pos2 = build_delete(enc, dele)
    if not _verified_delete.check_delete(enc.n, enc.start, enc.evt, enc.dst, enc.init,
                                         enc.marked, dele, new_of, old_of, start2, evt2, dst2,
                                         init2, marked2, src2, pos2):
        raise InvalidAutomatonError("internal error: the result of deleting states was "
                                    "rejected by the verified checker")
    out = Encoded(len(old_of), enc.m, enc.in_E, enc.in_Euc, enc.in_Euo, init2, marked2, start2,
                  evt2, dst2)
    names = V.names
    return validate_encoded(out, list(V._event_of), [names[x] for x in old_of])
