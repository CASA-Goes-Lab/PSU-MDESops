"""
The supervisor (spec: certisc-proof/spec/supervisor.md).

Trusted glue around the verified Rust code: argument checks, event names and state names. The
algorithms (method="fast") run in rust/verified/src/sup/ (supcon.rs, complete.rs);
method="naive" is plain Python and is not verified.

Three constructions, each with both methods:
- "escape" (default): on G ‖ H, delete the states from which an uncontrollable word leads to
  an uncontrollable event that G allows and G ‖ H does not (Lean: supervisor_escape_L).
- "refine": complete H with a dump state (Hc), take P = G × Hc (G refined: the specification
  is the part of P away from the dump state, a strict subautomaton), and delete the states
  from which an uncontrollable word leads to the dump part (Lean: supervisor_L).
- "subautomaton": H is given as G with some states deleted (same names, same events), or as
  the indices of the states of G to keep; the same deletion runs on G itself, with I = the
  states of H (Lean: supervisor_L).
All three give the same automaton (same state names, transitions, initial and marked states).
"""

import collections
import itertools
import operator
import warnings
from typing import Iterable, Optional, Union

from core_aut import Automaton, ValidAutomaton, validate
from ops_aut.basic_ops import EmptyAutomatonWarning, _compose_parts, _valid

_MODES = ("prefix_closed",)
_LATER = ("nonblocking", "partial_observation")
_METHODS = ("fast", "naive")
_CONSTRUCTIONS = ("escape", "refine", "subautomaton")
_DUMP = object()                                  # the dump state of Hc in the naive method


def supervisor(G: Union[ValidAutomaton, Automaton], H=None, *,
               forbidden: Optional[Iterable[int]] = None,
               mode: str = "prefix_closed", method: str = "fast",
               construction: Optional[str] = None, backend: str = "rust") -> ValidAutomaton:
    """The supervisor for plant G and specification H: an automaton S with L(S) = K↑C, the
    supremal controllable sublanguage of K = L(G) ∩ P_H⁻¹ L(H) (H does not constrain the
    plant's events it does not mention), with respect to L(G) and the uncontrollable events.

    State i of S is named (g_name, h_name): its plant state and its specification state.
    Events: those of G; Euc and Euo: G's (H must agree on the events it shares with G).
    If the initial state must be removed, K↑C is empty and the result is the empty automaton,
    with an EmptyAutomatonWarning.

    mode: "prefix_closed" (only this one so far).
    method: "fast" (default) is verified: Rust code checked by Verus (rust/verified/src/sup/),
    with the language result proved in Lean (Supervisor.lean); linear in the size of the
    product. "naive" is plain Python, not verified: delete the violating states and take the
    accessible part, until nothing changes (quadratic).
    construction: "escape" (default), "refine" or "subautomaton" (see the module doc). For
    "subautomaton", H is either G with some states deleted (its state names are names of G, it
    has G's events and flags, and every transition of G between its states; else ValueError),
    or simply the states of G to keep, as indices (any iterable of ints): then the
    specification is G restricted to them, with no names to match and nothing to check, which
    is the fastest form.
    forbidden: instead of H, the states of G to delete, as indices (a forbidden-state
    specification): the same as H = the other states of G, with construction "subautomaton"
    (implied; another construction is an error).

    Raises InvalidAutomatonError if G or H is not a valid automaton; ValueError if G or H is not
    deterministic, if H has events that G does not, if a shared event is controllable in one
    and uncontrollable in the other (or observable in one and unobservable in the other), or for
    an unknown mode, method, construction or backend; NotImplementedError for a mode not
    written yet."""
    if mode in _LATER:
        raise NotImplementedError(f"supervisor: mode {mode!r} is not implemented yet")
    if mode not in _MODES:
        raise ValueError(f"unknown mode {mode!r}; available: {_MODES}")
    if method not in _METHODS:
        raise ValueError(f"unknown method {method!r}; available: {_METHODS}")
    if forbidden is not None:
        if H is not None:
            raise ValueError("supervisor: give either a specification H or forbidden states, "
                             "not both")
        if construction not in (None, "subautomaton"):
            raise ValueError("supervisor: forbidden states are a strict-subautomaton "
                             "specification; use construction='subautomaton' (or leave it out)")
        construction = "subautomaton"
    elif H is None:
        raise ValueError("supervisor: a specification H or forbidden states are needed")
    if construction is None:
        construction = "escape"
    if construction not in _CONSTRUCTIONS:
        raise ValueError(f"unknown construction {construction!r}; available: {_CONSTRUCTIONS}")
    VG = _valid(G, backend)
    if not VG.is_deterministic:
        raise ValueError("supervisor: the plant G must be deterministic")
    if forbidden is not None or (construction == "subautomaton"
                                 and not isinstance(H, (Automaton, ValidAutomaton))):
        # The states of G to keep (H) or to delete (forbidden), as indices: the specification
        # is G restricted to the kept states; no names to match and nothing to check.
        if forbidden is not None:
            inside = _inside_of_indices(VG, forbidden, keep=False)
        else:
            inside = _inside_of_indices(VG, H)
        if method == "naive":
            return _naive_on_g(VG, inside)
        rs, old = VG._rs.supervisor_sub(inside)
        return _result(rs, list(VG._event_of), _pair_names(VG.names, VG.names, old, old))
    VH = _valid(H, backend)
    if not VH.is_deterministic:
        raise ValueError("supervisor: the specification H must be deterministic")
    extra = VH.events - VG.events
    if extra:
        raise ValueError("supervisor: H has events that G does not: "
                         + ", ".join(sorted(map(repr, extra))))
    if construction == "subautomaton":
        match = _sub_inside(VG, VH)
    if method == "naive":
        _check_agree_names(VG, VH)
        if construction == "subautomaton":
            return _naive_sub(VG, VH, match[0])
        return _naive(VG, VH, refine=(construction == "refine"))
    if construction == "escape":
        # P0 = G ‖ H (verified composition; also the verified agreement check).
        rs0, p1, p2, events = _compose_parts(VG, VH, True, "supervisor")
        rs, old = rs0.supervisor_pc(VG._rs, p1)
        return _result(rs, events, _pair_names(VG.names, VH.names, _at(p1, old), _at(p2, old)))
    if construction == "refine":
        return _refine(VG, VH)
    return _subautomaton(VG, VH, match)


def _at(lst, idx):
    """[lst[i] for i in idx], in C (map)."""
    return list(map(lst.__getitem__, idx))


def _pair_names(gn, hn, gi, hi):
    """[(gn[a], hn[b]) for a, b in zip(gi, hi)], in C (map, zip): this runs once per state."""
    return list(zip(map(gn.__getitem__, gi), map(hn.__getitem__, hi)))


def _inside_of_indices(VG: ValidAutomaton, states, keep: bool = True) -> list:
    """inside[x] for states of G given as indices: the states to keep (keep=True, H given as
    states) or the states to delete (keep=False, forbidden states)."""
    S = list(states)
    n = VG.num_states
    inside = [not keep] * n
    try:
        if S and (min(S) < 0 or max(S) >= n):
            raise IndexError
        collections.deque(map(inside.__setitem__, S, itertools.repeat(keep)), maxlen=0)
    except (IndexError, TypeError):
        what = "H given as states" if keep else "forbidden states"
        raise ValueError(f"supervisor: {what} must be state indices of G (0 .. {n - 1})") from None
    return inside


def _result(rs, events, names) -> ValidAutomaton:
    if rs.n == 0:
        warnings.warn("supervisor: the result is the empty automaton (K↑C is empty)",
                      EmptyAutomatonWarning, stacklevel=3)
    return ValidAutomaton._make(rs, events, names)


def _empty(VG: ValidAutomaton) -> ValidAutomaton:
    warnings.warn("supervisor: the result is the empty automaton (K↑C is empty)",
                  EmptyAutomatonWarning, stacklevel=3)
    return validate(Automaton(events=VG.events, Euc=VG.Euc, Euo=VG.Euo))


def _refine(VG: ValidAutomaton, VH: ValidAutomaton) -> ValidAutomaton:
    """construction="refine", method="fast"."""
    if VH.num_states == 0:                       # L(H) = ∅, so K↑C = ∅
        return _empty(VG)
    # Hc: H's events, then G's events that H does not mention (they self-loop), with G's flags.
    extra = [e for e in VG._event_of if VH._event_number(e) is None]
    hc = VH._rs.complete(len(extra), [e in VG.Euc for e in extra], [e in VG.Euo for e in extra])
    hc_events = list(VH._event_of) + extra
    # P = G × Hc in G's event numbering (every event of Hc is an event of G).
    map2 = [VG._event_number(e) for e in hc_events]
    m = len(VG._event_of)
    code, e2 = VG._rs.agree(hc, map2, m)
    if code != 0:
        what = ("controllable in one and uncontrollable in the other" if code == 1 else
                "observable in one and unobservable in the other")
        raise ValueError(f"supervisor: shared event {hc_events[e2]!r} is {what}")
    rs_p, p1, p2 = VG._rs.compose(hc, map2, m, False)
    rs, old = rs_p.supervisor_sub_label(p2, VH.num_states)
    return _result(rs, list(VG._event_of), _pair_names(VG.names, VH.names, _at(p1, old), _at(p2, old)))


def _sub_inside(VG: ValidAutomaton, VH: ValidAutomaton):
    """construction="subautomaton": (inside, pos, in_order). pos[i] is the state of G named as
    state i of H; inside[x] marks the states of G that are states of H; in_order says that H's
    states are in G's order. Names are matched by Python == (trusted, then checked by the
    verified `restricts`). Written with C-level built-ins (map, zip): this runs once per state."""
    gnames = VG.names
    n = len(gnames)
    gidx = dict(zip(gnames, range(n)))
    if len(gidx) != n:
        raise ValueError("supervisor: construction='subautomaton' needs unique state names in G")
    try:
        pos = list(map(gidx.__getitem__, VH.names))
    except (KeyError, TypeError):
        pos = None
    in_order = pos is not None and all(map(operator.lt, pos, pos[1:]))
    if pos is None or (not in_order and len(set(pos)) != len(pos)):
        raise ValueError("supervisor: construction='subautomaton' needs H's state names to be "
                         "distinct names of states of G")
    inside = [False] * n
    collections.deque(map(inside.__setitem__, pos, itertools.repeat(True)), maxlen=0)
    return inside, pos, in_order


def _subautomaton(VG: ValidAutomaton, VH: ValidAutomaton, match) -> ValidAutomaton:
    """construction="subautomaton", method="fast"."""
    inside, pos, in_order = match
    # The verified check that H is exactly G with the other states deleted. If H already has
    # G's event table and its states in G's order (as from delete_states(G, ...)), its Rust
    # copy is compared as is; else Rust re-encodes it first (trusted; a wrong re-encoding can
    # only make the check fail).
    if in_order and VH._event_of == VG._event_of:
        ok = VG._rs.restricts(VH._rs, inside)
    else:
        order = sorted(range(VH.num_states), key=pos.__getitem__)
        emap = [VG._event_number(e) for e in VH._event_of]
        ok = VG._rs.restricts_mapped(VH._rs, inside, emap, order)
    if not ok:
        raise ValueError("supervisor: H is not a strict subautomaton of G (G with some states "
                         "deleted: same events and flags, the same initial and marked states, "
                         "and every transition of G between H's states)")
    rs, old = VG._rs.supervisor_sub(inside)
    return _result(rs, list(VG._event_of), _pair_names(VG.names, VG.names, old, old))


# --- method="naive" (plain Python, not verified) -------------------------------------------

def _check_agree_names(VG: ValidAutomaton, VH: ValidAutomaton) -> None:
    for e in VH.events:
        if (e in VH.Euc) != (e in VG.Euc):
            raise ValueError(f"supervisor: shared event {e!r} is controllable in one and "
                             "uncontrollable in the other")
        if (e in VH.Euo) != (e in VG.Euo):
            raise ValueError(f"supervisor: shared event {e!r} is observable in one and "
                             "unobservable in the other")


def _iterate(init, moves, ok, uc):
    """The textbook iteration. `moves(p)` = {event: next state}; `ok(p)` = p is allowed by
    itself (no uncontrollable escape, not outside). Repeat: delete the states that are not ok or
    have an uncontrollable move into a deleted state, and keep the accessible part. Returns the
    remaining states in breadth-first order."""
    def accessible(alive):
        seen = [p for p in init if alive is None or p in alive]
        index, todo = set(seen), list(seen)
        while todo:
            p = todo.pop(0)
            for q in moves(p).values():
                if (alive is None or q in alive) and q not in index:
                    index.add(q)
                    seen.append(q)
                    todo.append(q)
        return seen

    alive = set(accessible(None))
    while True:
        bad = {p for p in alive
               if not ok(p) or any(e in uc and q not in alive for e, q in moves(p).items())}
        order = accessible(alive - bad)
        if not bad and len(order) == len(alive):
            return order
        alive = set(order)


def _build(VG: ValidAutomaton, order, moves, name, marked) -> ValidAutomaton:
    S = Automaton(events=VG.events, Euc=VG.Euc, Euo=VG.Euo)
    index = {}
    for p in order:
        index[p] = S.add_state(name(p), marked(p), init=not index)
    for p in order:
        for e, q in moves(p).items():
            if q in index:
                S.add_transition(index[p], e, index[q])
    if not order:
        warnings.warn("supervisor: the result is the empty automaton (K↑C is empty)",
                      EmptyAutomatonWarning, stacklevel=4)
    return validate(S)


def _naive(VG: ValidAutomaton, VH: ValidAutomaton, refine: bool) -> ValidAutomaton:
    """construction "escape" (on G ‖ H) or "refine" (on G × Hc, Hc with a dump state)."""
    dG = {(x, e): y for x, e, y in VG.transitions()}
    dH = {(x, e): y for x, e, y in VH.transitions()}
    outG = {}
    for x, e, _ in VG.transitions():
        outG.setdefault(x, []).append(e)
    EH = VH.events

    def step_h(h, e):
        """H's next state on e in G ‖ H (None: blocked) or in Hc (the dump state instead)."""
        if h is _DUMP:
            return _DUMP
        if e not in EH:
            return h                                # H does not constrain e
        if (h, e) in dH:
            return dH[h, e]
        return _DUMP if refine else None

    def moves(p):
        g, h = p
        out = {}
        for e in outG.get(g, ()):
            h2 = step_h(h, e)
            if h2 is not None:
                out[e] = (dG[g, e], h2)
        return out

    def ok(p):
        g, h = p
        if refine:
            return h is not _DUMP
        # escape: no uncontrollable event that G allows and G ‖ H blocks
        return not any(e in VG.Euc and step_h(h, e) is None for e in outG.get(g, ()))

    init = [(g, h) for g in VG.init for h in VH.init]
    order = _iterate(init, moves, ok, VG.Euc)
    gm, hm, gn, hn = VG.marked, VH.marked, VG.names, VH.names      # read once
    return _build(VG, order, moves, lambda p: (gn[p[0]], hn[p[1]]),
                  lambda p: p[0] in gm and p[1] in hm)


def _naive_sub(VG: ValidAutomaton, VH: ValidAutomaton, inside: list) -> ValidAutomaton:
    """construction "subautomaton": the iteration on G itself, I = H's states. H is checked
    against G by names (plain Python)."""
    gidx = {name: x for x, name in enumerate(VG.names)}
    expected = {(VG.names[x], e, VG.names[y]) for x, e, y in VG.transitions()
                if inside[x] and inside[y]}
    given = {(VH.names[x], e, VH.names[y]) for x, e, y in VH.transitions()}
    same = (expected == given and VH.events == VG.events and VH.Euc == VG.Euc
            and VH.Euo == VG.Euo
            and {VH.names[i] for i in VH.init} == {VG.names[x] for x in VG.init if inside[x]}
            and {VH.names[i] for i in VH.marked} == {VG.names[x] for x in VG.marked if inside[x]})
    if not same:
        raise ValueError("supervisor: H is not a strict subautomaton of G (G with some states "
                         "deleted: same events and flags, the same initial and marked states, "
                         "and every transition of G between H's states)")
    return _naive_on_g(VG, inside)


def _naive_on_g(VG: ValidAutomaton, inside: list) -> ValidAutomaton:
    """The naive iteration on G itself, with I = the states marked in `inside`."""
    dG = {}
    for x, e, y in VG.transitions():
        dG.setdefault(x, {})[e] = y

    def moves(x):
        return dG.get(x, {})

    order = _iterate(list(VG.init), moves, lambda x: inside[x], VG.Euc)
    gm, gn = VG.marked, VG.names                                    # read once
    return _build(VG, order, moves, lambda x: (gn[x], gn[x]), lambda x: x in gm)
