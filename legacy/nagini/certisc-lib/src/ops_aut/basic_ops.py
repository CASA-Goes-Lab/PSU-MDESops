"""
Public basic operations on Automaton objects. Each one calls an implementation:

- backend="rust" (default): the Verus-verified Rust code (rust/verified/src/ops_aut/), through
  the extension core_aut._rs. The automaton is already in Rust (ValidAutomaton._rs).
- backend="nagini": the Nagini-verified code in verified_ops/, stripped of its contracts at
  import (core_aut/trusted/_strip.py). Kept for comparison while both exist.

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
_BACKENDS = ("rust", "nagini")


class EmptyAutomatonWarning(UserWarning):
    """An operation returned the empty automaton (no states): every state was deleted, or every
    initial state was (an automaton with states but no initial state is not valid, W3)."""


def next_states(G: Union[ValidAutomaton, Automaton], states: Iterable[int], event: Any, *,
                witnesses: bool = False,
                backend: str = "rust") -> Union[List[int], Tuple[List[int], List[int]]]:
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
    if backend == "rust":
        out, src = V._rs.next_states(S, e)
        return (out, [S[j] for j in src]) if witnesses else out
    enc = V._encoding()
    out, src, via, pos = [], [], [], {}
    _verified.next_states(enc.n, enc.m, enc.start, enc.evt, enc.dst, enc.in_E, S, e,
                          out, src, via, pos)
    if witnesses:
        return out, [S[j] for j in src]
    return out


def active_events(G: Union[ValidAutomaton, Automaton], states: Iterable[int], *,
                  witnesses: bool = False,
                  backend: str = "rust") -> Union[List[Any], Tuple[List[Any], List[int]]]:
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
    if backend == "rust":
        out, src = V._rs.active_events(S)
        labels = [V._event_of[e] for e in out]
    else:
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
    """(Nagini backend) Run a verified active_events: over the active-event index (built and checked once per
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
              witnesses: bool = False, backend: str = "rust"
              ) -> Union[List[int], Tuple[List[int], List[Optional[Tuple[int, Any]]]]]:
    """The states reachable from `states` (default: the initial states), each once, in
    breadth-first order.

    With witnesses=True, also a list `parents`: parents[i] is None if reached[i] is a start
    state, else (x, e): reached[i] is reached from the state x by the event e, and x comes
    earlier in the list. Following the parents back gives a shortest word to each state.

    Verified core: rust/verified/src/ops_aut/reach.rs (proved: the result is exactly Lean's
    `reach f S`), or verified_ops/reach.py (Nagini backend). Spec: certisc-proof/spec/reach.md.
    Lean: `reach f S`, and `reach_eq_of_certificate`, which turns the verified properties
    (contains S, closed, witnesses) into "exactly the reachable states".

    Raises InvalidAutomatonError if G is not a valid automaton, ValueError for a state index
    out of range or an unknown backend."""
    if backend not in _BACKENDS:
        raise ValueError(f"unknown backend {backend!r}; available: {_BACKENDS}")
    V = G if isinstance(G, ValidAutomaton) else validate(G)
    n = V.num_states
    S = sorted(V.init) if states is None else list(states)
    for x in S:
        if not (isinstance(x, int) and 0 <= x < n):
            raise ValueError(f"{x!r} is not a state index of G")
    if backend == "rust":
        out, par = V._rs.reachable(S)
        if not witnesses:
            return out
        return out, [None if w is None else (out[w[0]], V._event_of[w[1]]) for w in par]
    enc = V._encoding()
    mark = [-1] * enc.n                      # one entry per state
    out, par, via = [], [], []
    _verified_reach.reachable(enc.n, enc.start, enc.dst, S, mark, out, par, via)
    if not witnesses:
        return out
    parents = [None if p == -1 else (out[p], V._event_of[enc.evt[k]])
               for p, k in zip(par, via)]
    return out, parents


def coreachable(G: Union[ValidAutomaton, Automaton], states: Optional[Iterable[int]] = None, *,
                witnesses: bool = False, backend: str = "rust"
                ) -> Union[List[int], Tuple[List[int], List[Optional[Tuple[Any, int]]]]]:
    """The states from which some state of `states` (default: the marked states) can be
    reached, each once, in breadth-first order from those target states.

    With witnesses=True, also a list `nexts`: nexts[i] is None if coreached[i] is a target
    state, else (e, y): the event e leads from coreached[i] to the state y, and y comes earlier
    in the list. Following the nexts gives a shortest word from each state to a target.

    Verified core: rust/verified/src/ops_aut/reach.rs (proved: exactly Lean's `coreach f Xm`),
    over the reverse index (built once per ValidAutomaton, then kept; for a plain Automaton, on
    every call); or verified_ops/coreach.py (Nagini backend). Spec:
    certisc-proof/spec/coreach.md. Lean: `coreach f Xm`, and `coreach_eq_of_certificate`.

    Raises InvalidAutomatonError if G is not a valid automaton, ValueError for a state index
    out of range or an unknown backend."""
    if backend not in _BACKENDS:
        raise ValueError(f"unknown backend {backend!r}; available: {_BACKENDS}")
    V = G if isinstance(G, ValidAutomaton) else validate(G)
    n = V.num_states
    Xm = sorted(V.marked) if states is None else list(states)
    for x in Xm:
        if not (isinstance(x, int) and 0 <= x < n):
            raise ValueError(f"{x!r} is not a state index of G")
    if backend == "rust":
        out, nxt = V._rs.coreachable(Xm)
        if not witnesses:
            return out
        return out, [None if w is None else (V._event_of[w[1]], out[w[0]]) for w in nxt]
    enc = V._encoding()
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
                  backend: str = "rust") -> ValidAutomaton:
    """A new automaton: G without the given states (indices; repeats are fine) and without the
    transitions into or out of them. The kept states keep their names, flags and order, and are
    renumbered 0, 1, ...; the events (and Euc, Euo) are unchanged.

    If every initial state is deleted (or every state), the result is the empty automaton, with
    an EmptyAutomatonWarning: an automaton with states but no initial state is not valid (W3).

    G itself is not changed. The result is a new ValidAutomaton; the old one is freed when
    nothing refers to it any more (e.g. after V = delete_states(V, S)). To delete several sets,
    pass their union: one copy instead of several.

    Verified: rust/verified/src/ops_aut/delete.rs is proved to build exactly G with the states
    deleted (Lean `Automaton.IsDeletion`), and a valid automaton. (Nagini backend: a trusted
    builder, whose result verified_ops/delete.py checks, then the verified checker.) Spec:
    certisc-proof/spec/delete_states.md.

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
    if backend == "rust":
        return _wrap(V, V._rs.delete_states(dele), "delete_states")
    return _delete(V, dele, "delete_states")


def accessible(G: Union[ValidAutomaton, Automaton], *,
               backend: str = "rust") -> ValidAutomaton:
    """The accessible part of G: a new automaton with only the states reachable from an initial
    state (reachable(G)), and the transitions between them. Same as
    delete_states(G, the states not in reachable(G)).

    Rust backend: one verified function, proved to give exactly Lean's IsDeletion for this
    set of states. (Nagini backend: built from the verified reachable, coreachable and
    delete_states; only which states to delete is computed here.) Raises InvalidAutomatonError if G is not a valid
    automaton, ValueError for an unknown backend."""
    if backend not in _BACKENDS:
        raise ValueError(f"unknown backend {backend!r}; available: {_BACKENDS}")
    V = G if isinstance(G, ValidAutomaton) else validate(G)
    if backend == "rust":
        return _wrap(V, V._rs.accessible(), "accessible")
    dele = [True] * V.num_states
    for x in reachable(V, backend="nagini"):
        dele[x] = False
    return _delete(V, dele, "accessible")


def coaccessible(G: Union[ValidAutomaton, Automaton], *,
                 backend: str = "rust") -> ValidAutomaton:
    """The coaccessible part of G: a new automaton with only the states from which a marked
    state can be reached (coreachable(G)), and the transitions between them. Same as
    delete_states(G, the states not in coreachable(G)).

    If no initial state is coaccessible (so Lm(G) is empty), the result is the empty automaton,
    with an EmptyAutomatonWarning.

    Rust backend: one verified function, proved to give exactly Lean's IsDeletion for this
    set of states. (Nagini backend: built from the verified reachable, coreachable and
    delete_states; only which states to delete is computed here.) Raises InvalidAutomatonError if G is not a valid automaton, ValueError for an
    unknown backend."""
    if backend not in _BACKENDS:
        raise ValueError(f"unknown backend {backend!r}; available: {_BACKENDS}")
    V = G if isinstance(G, ValidAutomaton) else validate(G)
    if backend == "rust":
        return _wrap(V, V._rs.coaccessible(), "coaccessible")
    dele = [True] * V.num_states
    for x in coreachable(V, backend="nagini"):
        dele[x] = False
    return _delete(V, dele, "coaccessible")


def trim(G: Union[ValidAutomaton, Automaton], *, backend: str = "rust") -> ValidAutomaton:
    """The trim part of G: a new automaton with only the states that are both accessible
    (reachable(G)) and coaccessible (coreachable(G)), and the transitions between them.

    One deletion is enough: every path from a reachable state stays among reachable states, so
    "coaccessible in the accessible part" is "coaccessible in G" for those states.

    If no initial state is coaccessible (so Lm(G) is empty), the result is the empty automaton,
    with an EmptyAutomatonWarning.

    Rust backend: one verified function, proved to give exactly Lean's IsDeletion for this
    set of states. (Nagini backend: built from the verified reachable, coreachable and
    delete_states; only which states to delete is computed here.) Raises InvalidAutomatonError if G is not a
    valid automaton, ValueError for an unknown backend."""
    if backend not in _BACKENDS:
        raise ValueError(f"unknown backend {backend!r}; available: {_BACKENDS}")
    V = G if isinstance(G, ValidAutomaton) else validate(G)
    if backend == "rust":
        return _wrap(V, V._rs.trim(), "trim")
    co = [False] * V.num_states
    for x in coreachable(V, backend="nagini"):
        co[x] = True
    dele = [True] * V.num_states
    for x in reachable(V, backend="nagini"):
        if co[x]:
            dele[x] = False
    return _delete(V, dele, "trim")


def _wrap(V: ValidAutomaton, result, op: str) -> ValidAutomaton:
    """(Rust backend) The ValidAutomaton for a Rust deletion result (RsAut, old): old[i] is the
    state of V that state i comes from, so it keeps its name. The Rust functions return the
    empty automaton exactly when no initial state is kept; warn then."""
    rs, old = result
    if rs.n == 0:
        warnings.warn(f"{op}: the result is the empty automaton (no initial state is kept)",
                      EmptyAutomatonWarning, stacklevel=3)
    names = V.names
    return ValidAutomaton._make(rs, list(V._event_of), [names[x] for x in old])


def _delete(V: ValidAutomaton, dele: Sequence[bool], op: str) -> ValidAutomaton:
    """(Nagini backend) Delete the states x with dele[x] from V: the empty automaton (with a warning) if no
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
