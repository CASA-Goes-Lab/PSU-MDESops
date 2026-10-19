"""
Verified core of parallel composition (in progress; not used by DESops.composition yet).

Verify with Nagini, from DESops-lib/ (about 30 s):

    nagini DESops/verified/parallel.py

Inputs (both automata encoded as in check.py, with one shared event numbering 0 .. m-1):
    n1, init1, start1, evt1, dst1, in_E1     G1
    n2, init2, start2, evt2, dst2, in_E2     G2
Outputs (empty lists filled by parallel_core):
    p1, p2               output state i is the pair (p1[i], p2[i])
    ostart, oevt, odst   output transitions grouped by source state, as in check.py
    index                dict: key x1 * n2 + x2 -> output state (lookup accelerator)
Result: 0 success, 1 fuel exhausted (more than n1 * n2 states; cannot happen at runtime).

Algorithm: add every pair of initial states; then breadth-first over the output-state list
(state `head` is expanded once, its new successors are appended). From (x1, x2): a G1 transition
on a shared event pairs with each G2 transition on the same event; a G1 transition on a G1-only
event moves G1 alone; a G2 transition on a G2-only event moves G2 alone.

Proved so far (step A), for every input satisfying the preconditions:
- termination (MustTerminate; the BFS is bounded by n1 * n2 new states, the "fuel");
- on success: every output state is a pair of input states (map_ok); the output blocks tile the
  output transitions (blocks_ok, as in check.py); every output transition uses an event of
  E1 or E2 and targets an output state (out_ok).
Not yet proved: that the transitions are exactly the product transitions (P1), the initial
states (P2), closure (P3), reachability witnesses (P4), marking and event sets (P5), the full
valid_automaton for the output (P6). See doc/logs/formal-verification.md.

Design notes:
- The pair key x1 * n2 + x2 is injective, but that is NOT proved (it needs nonlinear
  arithmetic, which made Z3 time out). lookup checks the components of the state it finds at
  runtime instead; the proof only needs "every value in the dict is a state".
- Runtime: the contract statements must be stripped before running (Old(...) is None at
  runtime, so e.g. `Ensures(Old(len(p1)) <= len(p1))` raises TypeError). Until stripping at
  import exists, tests/test_verified_parallel.py strips them itself.
"""

from typing import Dict, List

from nagini_contracts.contracts import *
from nagini_contracts.obligations import MustTerminate

# --- input structure (as in check.py) --------------------------------------------------------


@Pure
def blocks_ok(n: int, start: List[int], T: int) -> bool:
    Requires(Acc(list_pred(start), 1 / 2))
    if n < 0 or len(start) != n + 1:
        return False
    if start[0] != 0 or start[n] != T:
        return False
    return Forall(int, lambda x: (
        Implies(0 <= x and x < n,
                0 <= start[x] and start[x] <= start[x + 1] and start[x + 1] <= T),
        [[start[x + 1]]]))


@Pure
def trans_ok(n: int, m: int, in_E: List[bool], evt: List[int], dst: List[int]) -> bool:
    """Every transition's event is an event number in E (W1), and its target a state."""
    Requires(Acc(list_pred(in_E), 1 / 2) and Acc(list_pred(evt), 1 / 2)
             and Acc(list_pred(dst), 1 / 2))
    if len(in_E) != m or len(evt) != len(dst):
        return False
    return Forall(int, lambda k: (Implies(
        0 <= k and k < len(evt),
        0 <= evt[k] and evt[k] < m and in_E[evt[k]] and 0 <= dst[k] and dst[k] < n),
        [[evt[k]], [dst[k]]]))


@Pure
def input_ok(n: int, m: int, start: List[int], evt: List[int], dst: List[int],
             in_E: List[bool]) -> bool:
    Requires(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2)
             and Acc(list_pred(dst), 1 / 2) and Acc(list_pred(in_E), 1 / 2))
    return (m >= 0 and len(in_E) == m and blocks_ok(n, start, len(evt))
            and trans_ok(n, m, in_E, evt, dst))


# --- state map (verified on its own: state_map_verified.py) ----------------------------------


@Pure
def pairs_ok(n1: int, n2: int, p1: List[int], p2: List[int]) -> bool:
    """Output state i is the pair (p1[i], p2[i]) of input states."""
    Requires(Acc(list_pred(p1), 1 / 2) and Acc(list_pred(p2), 1 / 2))
    Requires(len(p1) == len(p2))
    return Forall(int, lambda i: (Implies(
        0 <= i and i < len(p1),
        0 <= ToSeq(p1)[i] and ToSeq(p1)[i] < n1 and 0 <= ToSeq(p2)[i] and ToSeq(p2)[i] < n2),
        [[ToSeq(p1)[i]], [ToSeq(p2)[i]]]))


@Pure
def values_ok(T: int, index: Dict[int, int]) -> bool:
    """Every value in the map is one of the T output states."""
    Requires(Acc(dict_pred(index), 1 / 2))
    return Forall(index, lambda k: 0 <= index[k] and index[k] < T)


@Pure
def map_ok(n1: int, n2: int, p1: List[int], p2: List[int], index: Dict[int, int]) -> bool:
    Requires(Acc(list_pred(p1), 1 / 2) and Acc(list_pred(p2), 1 / 2)
             and Acc(dict_pred(index), 1 / 2))
    return (len(p1) == len(p2) and pairs_ok(n1, n2, p1, p2)
            and values_ok(len(p1), index))


def lookup(n1: int, n2: int, p1: List[int], p2: List[int], index: Dict[int, int],
           x1: int, x2: int) -> int:
    """An output state with components (x1, x2), or -1."""
    Requires(MustTerminate(2))
    Requires(Acc(list_pred(p1), 1 / 2) and Acc(list_pred(p2), 1 / 2)
             and Acc(dict_pred(index), 1 / 2))
    Requires(map_ok(n1, n2, p1, p2, index))
    Ensures(Acc(list_pred(p1), 1 / 2) and Acc(list_pred(p2), 1 / 2)
            and Acc(dict_pred(index), 1 / 2))
    Ensures(map_ok(n1, n2, p1, p2, index))
    Ensures(ToSeq(p1) == Old(ToSeq(p1)) and ToSeq(p2) == Old(ToSeq(p2)))
    Ensures(Result() == -1 or (0 <= Result() and Result() < len(p1)
                               and ToSeq(p1)[Result()] == x1 and ToSeq(p2)[Result()] == x2))
    k = x1 * n2 + x2
    if k in index:
        found = index[k]
        if p1[found] == x1 and p2[found] == x2:   # always true when 0 <= x2 < n2; checked, not proved
            return found
    return -1


def add(n1: int, n2: int, p1: List[int], p2: List[int], index: Dict[int, int],
        x1: int, x2: int) -> int:
    """Add output state (x1, x2); return its index."""
    Requires(MustTerminate(2))
    Requires(Acc(list_pred(p1)) and Acc(list_pred(p2)) and Acc(dict_pred(index)))
    Requires(0 <= x1 and x1 < n1 and 0 <= x2 and x2 < n2)
    Requires(map_ok(n1, n2, p1, p2, index))
    Ensures(Acc(list_pred(p1)) and Acc(list_pred(p2)) and Acc(dict_pred(index)))
    Ensures(map_ok(n1, n2, p1, p2, index))
    Ensures(ToSeq(p1) == Old(ToSeq(p1)) + PSeq(x1) and ToSeq(p2) == Old(ToSeq(p2)) + PSeq(x2))
    Ensures(Result() == Old(len(p1)))
    i = len(p1)
    p1.append(x1)
    p2.append(x2)
    index[x1 * n2 + x2] = i
    # The append keeps the old entries: entry j < i is what it was when add was called.
    Assert(Forall(int, lambda j: (Implies(0 <= j and j < i,
                                          ToSeq(p1)[j] == Old(ToSeq(p1))[j]
                                          and ToSeq(p2)[j] == Old(ToSeq(p2))[j]),
                                  [[ToSeq(p1)[j]], [ToSeq(p2)[j]]])))
    return i


def get_or_add(n1: int, n2: int, bound: int, p1: List[int], p2: List[int],
               index: Dict[int, int], x1: int, x2: int) -> int:
    """Output state (x1, x2), added if new; -1 if it is new and `bound` states exist already."""
    Requires(MustTerminate(3))
    Requires(Acc(list_pred(p1)) and Acc(list_pred(p2)) and Acc(dict_pred(index)))
    Requires(0 <= x1 and x1 < n1 and 0 <= x2 and x2 < n2)
    Requires(map_ok(n1, n2, p1, p2, index) and len(p1) <= bound)
    Ensures(Acc(list_pred(p1)) and Acc(list_pred(p2)) and Acc(dict_pred(index)))
    Ensures(map_ok(n1, n2, p1, p2, index) and len(p1) <= bound)
    Ensures(Old(len(p1)) <= len(p1))
    Ensures(ToSeq(p1).take(Old(len(p1))) == Old(ToSeq(p1))
            and ToSeq(p2).take(Old(len(p2))) == Old(ToSeq(p2)))
    Ensures(Result() == -1 or (0 <= Result() and Result() < len(p1)
                               and ToSeq(p1)[Result()] == x1 and ToSeq(p2)[Result()] == x2))
    found = lookup(n1, n2, p1, p2, index, x1, x2)
    if found >= 0:
        return found
    if len(p1) >= bound:
        return -1
    return add(n1, n2, p1, p2, index, x1, x2)


# --- output transitions ----------------------------------------------------------------------


@Pure
def out_ok(m: int, in_E1: List[bool], in_E2: List[bool], oevt: List[int], odst: List[int],
           T: int) -> bool:
    """Every output transition uses an event of E1 or E2 and targets one of T output states."""
    Requires(Acc(list_pred(in_E1), 1 / 2) and Acc(list_pred(in_E2), 1 / 2)
             and Acc(list_pred(oevt), 1 / 2) and Acc(list_pred(odst), 1 / 2))
    Requires(len(in_E1) == m and len(in_E2) == m)
    if len(oevt) != len(odst):
        return False
    return Forall(int, lambda k: (Implies(
        0 <= k and k < len(oevt),
        0 <= ToSeq(oevt)[k] and ToSeq(oevt)[k] < m
        and (in_E1[ToSeq(oevt)[k]] or in_E2[ToSeq(oevt)[k]])
        and 0 <= ToSeq(odst)[k] and ToSeq(odst)[k] < T),
        [[ToSeq(oevt)[k]], [ToSeq(odst)[k]]]))


def emit(m: int, in_E1: List[bool], in_E2: List[bool], oevt: List[int], odst: List[int],
         T: int, e: int, t: int) -> None:
    """Append output transition (event e, target t)."""
    Requires(MustTerminate(2))
    Requires(Acc(list_pred(in_E1), 1 / 2) and Acc(list_pred(in_E2), 1 / 2)
             and Acc(list_pred(oevt)) and Acc(list_pred(odst)))
    Requires(len(in_E1) == m and len(in_E2) == m)
    Requires(out_ok(m, in_E1, in_E2, oevt, odst, T))
    Requires(0 <= e and e < m and (in_E1[e] or in_E2[e]) and 0 <= t and t < T)
    Ensures(Acc(list_pred(in_E1), 1 / 2) and Acc(list_pred(in_E2), 1 / 2)
            and Acc(list_pred(oevt)) and Acc(list_pred(odst)))
    Ensures(ToSeq(in_E1) == Old(ToSeq(in_E1)) and ToSeq(in_E2) == Old(ToSeq(in_E2)))
    Ensures(out_ok(m, in_E1, in_E2, oevt, odst, T))
    Ensures(ToSeq(oevt) == Old(ToSeq(oevt)) + PSeq(e) and ToSeq(odst) == Old(ToSeq(odst)) + PSeq(t))
    n = len(oevt)
    oevt.append(e)
    odst.append(t)
    Assert(Forall(int, lambda j: (Implies(0 <= j and j < n,
                                          ToSeq(oevt)[j] == Old(ToSeq(oevt))[j]
                                          and ToSeq(odst)[j] == Old(ToSeq(odst))[j]),
                                  [[ToSeq(oevt)[j]], [ToSeq(odst)[j]]])))


# --- expanding one output state ---------------------------------------------------------------


def expand(n1: int, n2: int, m: int, bound: int,
           start1: List[int], evt1: List[int], dst1: List[int], in_E1: List[bool],
           start2: List[int], evt2: List[int], dst2: List[int], in_E2: List[bool],
           p1: List[int], p2: List[int], index: Dict[int, int],
           oevt: List[int], odst: List[int], x1: int, x2: int) -> int:
    """Append the transitions of output state (x1, x2). 0 = done, 1 = fuel exhausted."""
    Requires(MustTerminate(5))
    Requires(Acc(list_pred(start1), 1 / 2) and Acc(list_pred(evt1), 1 / 2)
             and Acc(list_pred(dst1), 1 / 2) and Acc(list_pred(in_E1), 1 / 2))
    Requires(Acc(list_pred(start2), 1 / 2) and Acc(list_pred(evt2), 1 / 2)
             and Acc(list_pred(dst2), 1 / 2) and Acc(list_pred(in_E2), 1 / 2))
    Requires(Acc(list_pred(p1)) and Acc(list_pred(p2)) and Acc(dict_pred(index))
             and Acc(list_pred(oevt)) and Acc(list_pred(odst)))
    Requires(input_ok(n1, m, start1, evt1, dst1, in_E1)
             and input_ok(n2, m, start2, evt2, dst2, in_E2))
    Requires(0 <= x1 and x1 < n1 and 0 <= x2 and x2 < n2)
    Requires(map_ok(n1, n2, p1, p2, index) and len(p1) <= bound)
    Requires(out_ok(m, in_E1, in_E2, oevt, odst, len(p1)))
    Ensures(Acc(list_pred(start1), 1 / 2) and Acc(list_pred(evt1), 1 / 2)
            and Acc(list_pred(dst1), 1 / 2) and Acc(list_pred(in_E1), 1 / 2))
    Ensures(Acc(list_pred(start2), 1 / 2) and Acc(list_pred(evt2), 1 / 2)
            and Acc(list_pred(dst2), 1 / 2) and Acc(list_pred(in_E2), 1 / 2))
    Ensures(Acc(list_pred(p1)) and Acc(list_pred(p2)) and Acc(dict_pred(index))
            and Acc(list_pred(oevt)) and Acc(list_pred(odst)))
    Ensures(input_ok(n1, m, start1, evt1, dst1, in_E1)
            and input_ok(n2, m, start2, evt2, dst2, in_E2))
    Ensures(map_ok(n1, n2, p1, p2, index) and len(p1) <= bound)
    Ensures(Old(len(p1)) <= len(p1))
    Ensures(ToSeq(p1).take(Old(len(p1))) == Old(ToSeq(p1))
            and ToSeq(p2).take(Old(len(p2))) == Old(ToSeq(p2)))
    Ensures(out_ok(m, in_E1, in_E2, oevt, odst, len(p1)))
    Ensures(Old(len(oevt)) <= len(oevt))
    Ensures(ToSeq(oevt).take(Old(len(oevt))) == Old(ToSeq(oevt))
            and ToSeq(odst).take(Old(len(odst))) == Old(ToSeq(odst)))
    # Moves of G1: on a shared event together with G2, on a private event alone.
    k1 = start1[x1]
    hi1 = start1[x1 + 1]
    while k1 < hi1:
        Invariant(Acc(list_pred(start1), 1 / 2) and Acc(list_pred(evt1), 1 / 2)
                  and Acc(list_pred(dst1), 1 / 2) and Acc(list_pred(in_E1), 1 / 2))
        Invariant(Acc(list_pred(start2), 1 / 2) and Acc(list_pred(evt2), 1 / 2)
                  and Acc(list_pred(dst2), 1 / 2) and Acc(list_pred(in_E2), 1 / 2))
        Invariant(Acc(list_pred(p1)) and Acc(list_pred(p2)) and Acc(dict_pred(index))
                  and Acc(list_pred(oevt)) and Acc(list_pred(odst)))
        Invariant(MustTerminate(hi1 - k1 + 4))
        Invariant(ToSeq(start1) == Old(ToSeq(start1)) and ToSeq(evt1) == Old(ToSeq(evt1))
                  and ToSeq(dst1) == Old(ToSeq(dst1)) and ToSeq(in_E1) == Old(ToSeq(in_E1)))
        Invariant(ToSeq(start2) == Old(ToSeq(start2)) and ToSeq(evt2) == Old(ToSeq(evt2))
                  and ToSeq(dst2) == Old(ToSeq(dst2)) and ToSeq(in_E2) == Old(ToSeq(in_E2)))
        Invariant(input_ok(n1, m, start1, evt1, dst1, in_E1)
                  and input_ok(n2, m, start2, evt2, dst2, in_E2))
        Invariant(start1[x1] <= k1 and k1 <= hi1 and hi1 == start1[x1 + 1] and hi1 <= len(evt1))
        Invariant(map_ok(n1, n2, p1, p2, index) and len(p1) <= bound)
        Invariant(Old(len(p1)) <= len(p1))
        Invariant(ToSeq(p1).take(Old(len(p1))) == Old(ToSeq(p1))
                  and ToSeq(p2).take(Old(len(p2))) == Old(ToSeq(p2)))
        Invariant(out_ok(m, in_E1, in_E2, oevt, odst, len(p1)))
        Invariant(Old(len(oevt)) <= len(oevt))
        Invariant(ToSeq(oevt).take(Old(len(oevt))) == Old(ToSeq(oevt))
                  and ToSeq(odst).take(Old(len(odst))) == Old(ToSeq(odst)))
        e = evt1[k1]
        y1 = dst1[k1]
        if in_E2[e]:
            k2 = start2[x2]
            hi2 = start2[x2 + 1]
            while k2 < hi2:
                Invariant(Acc(list_pred(start1), 1 / 2) and Acc(list_pred(evt1), 1 / 2)
                          and Acc(list_pred(dst1), 1 / 2) and Acc(list_pred(in_E1), 1 / 2))
                Invariant(Acc(list_pred(start2), 1 / 2) and Acc(list_pred(evt2), 1 / 2)
                          and Acc(list_pred(dst2), 1 / 2) and Acc(list_pred(in_E2), 1 / 2))
                Invariant(Acc(list_pred(p1)) and Acc(list_pred(p2)) and Acc(dict_pred(index))
                          and Acc(list_pred(oevt)) and Acc(list_pred(odst)))
                Invariant(MustTerminate(hi2 - k2 + 4))
                Invariant(ToSeq(start1) == Old(ToSeq(start1)) and ToSeq(evt1) == Old(ToSeq(evt1))
                          and ToSeq(dst1) == Old(ToSeq(dst1))
                          and ToSeq(in_E1) == Old(ToSeq(in_E1)))
                Invariant(ToSeq(start2) == Old(ToSeq(start2)) and ToSeq(evt2) == Old(ToSeq(evt2))
                          and ToSeq(dst2) == Old(ToSeq(dst2))
                          and ToSeq(in_E2) == Old(ToSeq(in_E2)))
                Invariant(input_ok(n1, m, start1, evt1, dst1, in_E1)
                          and input_ok(n2, m, start2, evt2, dst2, in_E2))
                Invariant(start1[x1] <= k1 and k1 < hi1 and hi1 == start1[x1 + 1]
                          and hi1 <= len(evt1))
                Invariant(start2[x2] <= k2 and k2 <= hi2 and hi2 == start2[x2 + 1]
                          and hi2 <= len(evt2))
                Invariant(0 <= e and e < m and in_E1[e] and in_E2[e] and 0 <= y1 and y1 < n1)
                Invariant(map_ok(n1, n2, p1, p2, index) and len(p1) <= bound)
                Invariant(Old(len(p1)) <= len(p1))
                Invariant(ToSeq(p1).take(Old(len(p1))) == Old(ToSeq(p1))
                          and ToSeq(p2).take(Old(len(p2))) == Old(ToSeq(p2)))
                Invariant(out_ok(m, in_E1, in_E2, oevt, odst, len(p1)))
                Invariant(Old(len(oevt)) <= len(oevt))
                Invariant(ToSeq(oevt).take(Old(len(oevt))) == Old(ToSeq(oevt))
                          and ToSeq(odst).take(Old(len(odst))) == Old(ToSeq(odst)))
                if evt2[k2] == e:
                    t = get_or_add(n1, n2, bound, p1, p2, index, y1, dst2[k2])
                    if t < 0:
                        return 1
                    emit(m, in_E1, in_E2, oevt, odst, len(p1), e, t)
                k2 += 1
        else:
            t = get_or_add(n1, n2, bound, p1, p2, index, y1, x2)
            if t < 0:
                return 1
            emit(m, in_E1, in_E2, oevt, odst, len(p1), e, t)
        k1 += 1
    # Moves of G2 on its private events (shared events were handled with G1 above).
    j2 = start2[x2]
    hj2 = start2[x2 + 1]
    while j2 < hj2:
        Invariant(Acc(list_pred(start1), 1 / 2) and Acc(list_pred(evt1), 1 / 2)
                  and Acc(list_pred(dst1), 1 / 2) and Acc(list_pred(in_E1), 1 / 2))
        Invariant(Acc(list_pred(start2), 1 / 2) and Acc(list_pred(evt2), 1 / 2)
                  and Acc(list_pred(dst2), 1 / 2) and Acc(list_pred(in_E2), 1 / 2))
        Invariant(Acc(list_pred(p1)) and Acc(list_pred(p2)) and Acc(dict_pred(index))
                  and Acc(list_pred(oevt)) and Acc(list_pred(odst)))
        Invariant(MustTerminate(hj2 - j2 + 4))
        Invariant(ToSeq(start1) == Old(ToSeq(start1)) and ToSeq(evt1) == Old(ToSeq(evt1))
                  and ToSeq(dst1) == Old(ToSeq(dst1)) and ToSeq(in_E1) == Old(ToSeq(in_E1)))
        Invariant(ToSeq(start2) == Old(ToSeq(start2)) and ToSeq(evt2) == Old(ToSeq(evt2))
                  and ToSeq(dst2) == Old(ToSeq(dst2)) and ToSeq(in_E2) == Old(ToSeq(in_E2)))
        Invariant(input_ok(n1, m, start1, evt1, dst1, in_E1)
                  and input_ok(n2, m, start2, evt2, dst2, in_E2))
        Invariant(start2[x2] <= j2 and j2 <= hj2 and hj2 == start2[x2 + 1] and hj2 <= len(evt2))
        Invariant(map_ok(n1, n2, p1, p2, index) and len(p1) <= bound)
        Invariant(Old(len(p1)) <= len(p1))
        Invariant(ToSeq(p1).take(Old(len(p1))) == Old(ToSeq(p1))
                  and ToSeq(p2).take(Old(len(p2))) == Old(ToSeq(p2)))
        Invariant(out_ok(m, in_E1, in_E2, oevt, odst, len(p1)))
        Invariant(Old(len(oevt)) <= len(oevt))
        Invariant(ToSeq(oevt).take(Old(len(oevt))) == Old(ToSeq(oevt))
                  and ToSeq(odst).take(Old(len(odst))) == Old(ToSeq(odst)))
        f = evt2[j2]
        if not in_E1[f]:
            u = get_or_add(n1, n2, bound, p1, p2, index, x1, dst2[j2])
            if u < 0:
                return 1
            emit(m, in_E1, in_E2, oevt, odst, len(p1), f, u)
        j2 += 1
    return 0


# --- the core --------------------------------------------------------------------------------


@Pure
def starts_ok(h: int, ostart: List[int], T: int) -> bool:
    """The first h block starts are recorded: they begin at 0, never decrease, and are <= T."""
    Requires(Acc(list_pred(ostart), 1 / 2))
    if len(ostart) != h:
        return False
    if h > 0 and ToSeq(ostart)[0] != 0:
        return False
    # Each recorded start is within 0 .. T.
    bounded = Forall(int, lambda y: (Implies(
        0 <= y and y < h,
        0 <= ToSeq(ostart)[y] and ToSeq(ostart)[y] <= T),
        [[ToSeq(ostart)[y]]]))
    # Consecutive starts do not decrease. Trigger on [y + 1] only: a trigger on [y] would
    # create [y + 1], which triggers again (a matching loop, as in check_blocks).
    ordered = Forall(int, lambda y: (Implies(
        0 <= y and y + 1 < h,
        ToSeq(ostart)[y] <= ToSeq(ostart)[y + 1]),
        [[ToSeq(ostart)[y + 1]]]))
    return bounded and ordered


def push_start(ostart: List[int], h: int, v: int, T: int) -> None:
    """Record the start v of block h."""
    Requires(MustTerminate(2))
    Requires(Acc(list_pred(ostart)))
    Requires(starts_ok(h, ostart, T) and 0 <= v and v <= T)
    Requires(Implies(h == 0, v == 0) and Implies(h > 0, ToSeq(ostart)[h - 1] <= v))
    Ensures(Acc(list_pred(ostart)))
    Ensures(starts_ok(h + 1, ostart, T) and ToSeq(ostart)[h] == v)
    ostart.append(v)
    # The append keeps the old entries.
    Assert(Forall(int, lambda y: (Implies(0 <= y and y < h, ToSeq(ostart)[y] == Old(ToSeq(ostart))[y]),
                                  [[ToSeq(ostart)[y]]])))


def starts_to_blocks(n: int, ostart: List[int], T: int) -> None:
    """Lemma: n + 1 recorded starts, the last one T, form the blocks of n states."""
    Requires(MustTerminate(2))
    Requires(Acc(list_pred(ostart), 1 / 2))
    Requires(n >= 0 and starts_ok(n + 1, ostart, T) and ToSeq(ostart)[n] == T)
    Ensures(Acc(list_pred(ostart), 1 / 2))
    Ensures(ToSeq(ostart) == Old(ToSeq(ostart)))
    Ensures(blocks_ok(n, ostart, T))
    # Heap reads ostart[x] are the sequence entries ToSeq(ostart)[x].
    Assert(Forall(int, lambda x: (Implies(0 <= x and x <= n, ostart[x] == ToSeq(ostart)[x]),
                                  [[ostart[x]]])))


def parallel_core(n1: int, n2: int, m: int,
                  init1: List[bool], start1: List[int], evt1: List[int], dst1: List[int],
                  in_E1: List[bool],
                  init2: List[bool], start2: List[int], evt2: List[int], dst2: List[int],
                  in_E2: List[bool],
                  p1: List[int], p2: List[int], index: Dict[int, int],
                  ostart: List[int], oevt: List[int], odst: List[int]) -> int:
    """G1 || G2 into the (empty) output lists. 0 = done, 1 = fuel exhausted."""
    Requires(MustTerminate(8))
    Requires(Acc(list_pred(init1), 1 / 2) and Acc(list_pred(start1), 1 / 2)
             and Acc(list_pred(evt1), 1 / 2) and Acc(list_pred(dst1), 1 / 2)
             and Acc(list_pred(in_E1), 1 / 2))
    Requires(Acc(list_pred(init2), 1 / 2) and Acc(list_pred(start2), 1 / 2)
             and Acc(list_pred(evt2), 1 / 2) and Acc(list_pred(dst2), 1 / 2)
             and Acc(list_pred(in_E2), 1 / 2))
    Requires(Acc(list_pred(p1)) and Acc(list_pred(p2)) and Acc(dict_pred(index))
             and Acc(list_pred(ostart)) and Acc(list_pred(oevt)) and Acc(list_pred(odst)))
    Requires(n1 >= 0 and n2 >= 0 and len(init1) == n1 and len(init2) == n2)
    Requires(input_ok(n1, m, start1, evt1, dst1, in_E1)
             and input_ok(n2, m, start2, evt2, dst2, in_E2))
    Requires(len(p1) == 0 and len(p2) == 0 and len(index) == 0
             and len(ostart) == 0 and len(oevt) == 0 and len(odst) == 0)
    Ensures(Acc(list_pred(init1), 1 / 2) and Acc(list_pred(start1), 1 / 2)
            and Acc(list_pred(evt1), 1 / 2) and Acc(list_pred(dst1), 1 / 2)
            and Acc(list_pred(in_E1), 1 / 2))
    Ensures(Acc(list_pred(init2), 1 / 2) and Acc(list_pred(start2), 1 / 2)
            and Acc(list_pred(evt2), 1 / 2) and Acc(list_pred(dst2), 1 / 2)
            and Acc(list_pred(in_E2), 1 / 2))
    Ensures(Acc(list_pred(p1)) and Acc(list_pred(p2)) and Acc(dict_pred(index))
            and Acc(list_pred(ostart)) and Acc(list_pred(oevt)) and Acc(list_pred(odst)))
    Ensures(input_ok(n1, m, start1, evt1, dst1, in_E1)
            and input_ok(n2, m, start2, evt2, dst2, in_E2))
    Ensures(Result() == 0 or Result() == 1)
    Ensures(Implies(Result() == 0,
                    map_ok(n1, n2, p1, p2, index)
                    and blocks_ok(len(p1), ostart, len(oevt))
                    and out_ok(m, in_E1, in_E2, oevt, odst, len(p1))))
    bound = n1 * n2         # at most n1 * n2 distinct pairs: never exhausted at runtime
    # Initial states: every pair of initial states.
    x1 = 0
    while x1 < n1:
        Invariant(Acc(list_pred(init1), 1 / 2) and Acc(list_pred(init2), 1 / 2))
        Invariant(Acc(list_pred(p1)) and Acc(list_pred(p2)) and Acc(dict_pred(index)))
        Invariant(Acc(list_pred(ostart)) and Acc(list_pred(oevt)) and Acc(list_pred(odst)))
        Invariant(MustTerminate(n1 - x1 + 5))
        Invariant(len(init1) == n1 and len(init2) == n2 and 0 <= x1 and x1 <= n1)
        Invariant(map_ok(n1, n2, p1, p2, index) and len(p1) <= bound)
        Invariant(len(ostart) == 0 and len(oevt) == 0 and len(odst) == 0)
        if init1[x1]:
            x2 = 0
            while x2 < n2:
                Invariant(Acc(list_pred(init1), 1 / 2) and Acc(list_pred(init2), 1 / 2))
                Invariant(Acc(list_pred(p1)) and Acc(list_pred(p2)) and Acc(dict_pred(index)))
                Invariant(Acc(list_pred(ostart)) and Acc(list_pred(oevt)) and Acc(list_pred(odst)))
                Invariant(MustTerminate(n2 - x2 + 4))
                Invariant(len(init1) == n1 and len(init2) == n2 and 0 <= x1 and x1 < n1
                          and 0 <= x2 and x2 <= n2)
                Invariant(map_ok(n1, n2, p1, p2, index) and len(p1) <= bound)
                Invariant(len(ostart) == 0 and len(oevt) == 0 and len(odst) == 0)
                if init2[x2]:
                    t = get_or_add(n1, n2, bound, p1, p2, index, x1, x2)
                    if t < 0:
                        return 1
                x2 += 1
        x1 += 1
    # Breadth-first search over the output states: expand each one once, in order.
    head = 0
    while head < len(p1):
        Invariant(Acc(list_pred(init1), 1 / 2) and Acc(list_pred(start1), 1 / 2)
                  and Acc(list_pred(evt1), 1 / 2) and Acc(list_pred(dst1), 1 / 2)
                  and Acc(list_pred(in_E1), 1 / 2))
        Invariant(Acc(list_pred(init2), 1 / 2) and Acc(list_pred(start2), 1 / 2)
                  and Acc(list_pred(evt2), 1 / 2) and Acc(list_pred(dst2), 1 / 2)
                  and Acc(list_pred(in_E2), 1 / 2))
        Invariant(Acc(list_pred(p1)) and Acc(list_pred(p2)) and Acc(dict_pred(index))
                  and Acc(list_pred(ostart)) and Acc(list_pred(oevt)) and Acc(list_pred(odst)))
        Invariant(MustTerminate(bound - head + 6))
        Invariant(input_ok(n1, m, start1, evt1, dst1, in_E1)
                  and input_ok(n2, m, start2, evt2, dst2, in_E2))
        Invariant(map_ok(n1, n2, p1, p2, index) and 0 <= head and head <= len(p1)
                  and len(p1) <= bound)
        Invariant(starts_ok(head, ostart, len(oevt)))
        Invariant(Implies(head == 0, len(oevt) == 0))   # no transitions before the first block
        Invariant(out_ok(m, in_E1, in_E2, oevt, odst, len(p1)))
        push_start(ostart, head, len(oevt), len(oevt))
        a = p1[head]
        b = p2[head]
        Assert(a == ToSeq(p1)[head] and b == ToSeq(p2)[head])   # links the read to pairs_ok
        r = expand(n1, n2, m, bound, start1, evt1, dst1, in_E1, start2, evt2, dst2, in_E2,
                   p1, p2, index, oevt, odst, a, b)
        if r != 0:
            return 1
        head += 1
    push_start(ostart, head, len(oevt), len(oevt))
    starts_to_blocks(len(p1), ostart, len(oevt))
    return 0
