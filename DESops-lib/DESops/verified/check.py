"""
Verified validity checker for the encoded automaton (DESops-proof/spec/wrapper.md, section 5).

Verify with Nagini (Python >= 3.12, `verify` extra, Java), from DESops-lib/:

    nagini DESops/verified/check.py

(about 15-25 s, "Verification successful").

Each `check_*` function is proved to return True exactly when its `*_ok` predicate holds.
`check_automaton` combines them: it returns 0 exactly when `valid_automaton` holds, and a nonzero
code names the first condition that fails. The `*_ok` predicates are the specification: the list
form of (W1)-(W3) and determinism in DESops-proof/spec/automaton.md, section 3.

At runtime the contract calls (Requires, Ensures, Invariant, ...) are no-ops.
"""

from typing import List

from nagini_contracts.contracts import *

# --- specification --------------------------------------------------------------------------


@Pure
def blocks_ok(n: int, start: List[int], T: int) -> bool:
    """`start` splits positions 0..T-1 into n consecutive blocks, one per state."""
    Requires(Acc(list_pred(start), 1 / 2))
    return (n >= 0 and len(start) == n + 1 and start[0] == 0 and start[n] == T
            and Forall(int, lambda x: (
                Implies(0 <= x and x < n,
                        0 <= start[x] and start[x] <= start[x + 1] and start[x + 1] <= T),
                [[start[x + 1]]])))


@Pure
def transitions_ok(n: int, m: int, in_E: List[bool], evt: List[int], dst: List[int]) -> bool:
    """Every transition has an event number in range, the event is in E (W1), and the target is a
    state."""
    Requires(Acc(list_pred(in_E), 1 / 2) and Acc(list_pred(evt), 1 / 2)
             and Acc(list_pred(dst), 1 / 2))
    return (len(in_E) == m and len(evt) == len(dst)
            and Forall(int, lambda k: Implies(
                0 <= k and k < len(evt),
                0 <= evt[k] and evt[k] < m and in_E[evt[k]] and 0 <= dst[k] and dst[k] < n)))


@Pure
def events_ok(m: int, in_E: List[bool], in_Euc: List[bool], in_Euo: List[bool]) -> bool:
    """(W2): Euc and Euo are subsets of E."""
    Requires(Acc(list_pred(in_E), 1 / 2) and Acc(list_pred(in_Euc), 1 / 2)
             and Acc(list_pred(in_Euo), 1 / 2))
    return (len(in_E) == m and len(in_Euc) == m and len(in_Euo) == m
            and Forall(int, lambda e: Implies(
                0 <= e and e < m,
                Implies(in_Euc[e], in_E[e]) and Implies(in_Euo[e], in_E[e]))))


@Pure
def init_ok(n: int, init: List[bool], deterministic: bool) -> bool:
    """(W3): an initial state iff there are states; at most one if deterministic."""
    Requires(Acc(list_pred(init), 1 / 2))
    return (len(init) == n
            and (n == 0 or Exists(int, lambda x: 0 <= x and x < n and init[x]))
            and (not deterministic or Forall2(int, int, lambda x, y: Implies(
                0 <= x and x < n and 0 <= y and y < n and init[x] and init[y], x == y))))


@Pure
def block_det(lo: int, hi: int, evt: List[int]) -> bool:
    """No event occurs twice among positions lo .. hi-1."""
    Requires(Acc(list_pred(evt), 1 / 2))
    Requires(0 <= lo and lo <= hi and hi <= len(evt))
    return Forall2(int, int, lambda j, i: Implies(lo <= j and j < i and i < hi, evt[j] != evt[i]))


@Pure
def det_ok(n: int, start: List[int], evt: List[int]) -> bool:
    """Determinism: no state has two transitions with the same event."""
    Requires(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2))
    Requires(blocks_ok(n, start, len(evt)))
    return Forall(int, lambda x: (Implies(0 <= x and x < n,
                                          block_det(start[x], start[x + 1], evt)),
                                  [[block_det(start[x], start[x + 1], evt)]]))


@Pure
def valid_automaton(n: int, m: int, in_E: List[bool], in_Euc: List[bool], in_Euo: List[bool],
                    init: List[bool], marked: List[bool], start: List[int], evt: List[int],
                    dst: List[int], deterministic: bool) -> bool:
    """The encoding is a well-formed automaton (a DFA if `deterministic`)."""
    Requires(Acc(list_pred(in_E), 1 / 2) and Acc(list_pred(in_Euc), 1 / 2)
             and Acc(list_pred(in_Euo), 1 / 2) and Acc(list_pred(init), 1 / 2)
             and Acc(list_pred(marked), 1 / 2) and Acc(list_pred(start), 1 / 2)
             and Acc(list_pred(evt), 1 / 2) and Acc(list_pred(dst), 1 / 2))
    return (n >= 0 and m >= 0 and len(marked) == n
            and blocks_ok(n, start, len(evt))
            and transitions_ok(n, m, in_E, evt, dst)
            and events_ok(m, in_E, in_Euc, in_Euo)
            and init_ok(n, init, deterministic)
            and (not deterministic or det_ok(n, start, evt)))


# --- checkers -------------------------------------------------------------------------------


def check_blocks(n: int, start: List[int], T: int) -> bool:
    Requires(Acc(list_pred(start), 1 / 2))
    Ensures(Acc(list_pred(start), 1 / 2))
    Ensures(ToSeq(start) == Old(ToSeq(start)))
    Ensures(Result() == blocks_ok(n, start, T))
    if n < 0 or len(start) != n + 1:
        return False
    if start[0] != 0 or start[n] != T:
        return False
    x = 0
    while x < n:
        Invariant(Acc(list_pred(start), 1 / 2))
        Invariant(ToSeq(start) == Old(ToSeq(start)))
        Invariant(n >= 0 and len(start) == n + 1 and 0 <= x and x <= n)
        Invariant(start[0] == 0 and start[n] == T)
        Invariant(Forall(int, lambda y: (Implies(0 <= y and y < x,
                                                 0 <= start[y] and start[y] <= start[y + 1]
                                                 and start[y + 1] <= T),
                                         [[start[y + 1]]])))
        lo = start[x]
        hi = start[x + 1]      # read both first: the solver needs the term start[x + 1] on every path
        if lo < 0 or lo > hi or hi > T:
            return False
        x += 1
    return True


def check_transitions(n: int, m: int, in_E: List[bool], evt: List[int], dst: List[int]) -> bool:
    Requires(Acc(list_pred(in_E), 1 / 2) and Acc(list_pred(evt), 1 / 2)
             and Acc(list_pred(dst), 1 / 2))
    Ensures(Acc(list_pred(in_E), 1 / 2) and Acc(list_pred(evt), 1 / 2)
            and Acc(list_pred(dst), 1 / 2))
    Ensures(ToSeq(in_E) == Old(ToSeq(in_E)))
    Ensures(ToSeq(evt) == Old(ToSeq(evt)))
    Ensures(ToSeq(dst) == Old(ToSeq(dst)))
    Ensures(Result() == transitions_ok(n, m, in_E, evt, dst))
    if len(in_E) != m or len(evt) != len(dst):
        return False
    k = 0
    while k < len(evt):
        Invariant(Acc(list_pred(in_E), 1 / 2) and Acc(list_pred(evt), 1 / 2)
                  and Acc(list_pred(dst), 1 / 2))
        Invariant(ToSeq(in_E) == Old(ToSeq(in_E)))
        Invariant(ToSeq(evt) == Old(ToSeq(evt)))
        Invariant(ToSeq(dst) == Old(ToSeq(dst)))
        Invariant(len(in_E) == m and len(evt) == len(dst) and 0 <= k and k <= len(evt))
        Invariant(Forall(int, lambda j: Implies(0 <= j and j < k,
                  0 <= evt[j] and evt[j] < m and in_E[evt[j]] and 0 <= dst[j] and dst[j] < n)))
        e = evt[k]
        if e < 0 or e >= m:
            return False
        if not in_E[e]:
            return False
        if dst[k] < 0 or dst[k] >= n:
            return False
        k += 1
    return True


def check_events(m: int, in_E: List[bool], in_Euc: List[bool], in_Euo: List[bool]) -> bool:
    Requires(Acc(list_pred(in_E), 1 / 2) and Acc(list_pred(in_Euc), 1 / 2)
             and Acc(list_pred(in_Euo), 1 / 2))
    Ensures(Acc(list_pred(in_E), 1 / 2) and Acc(list_pred(in_Euc), 1 / 2)
            and Acc(list_pred(in_Euo), 1 / 2))
    Ensures(ToSeq(in_E) == Old(ToSeq(in_E)))
    Ensures(ToSeq(in_Euc) == Old(ToSeq(in_Euc)))
    Ensures(ToSeq(in_Euo) == Old(ToSeq(in_Euo)))
    Ensures(Result() == events_ok(m, in_E, in_Euc, in_Euo))
    if len(in_E) != m or len(in_Euc) != m or len(in_Euo) != m:
        return False
    e = 0
    while e < m:
        Invariant(Acc(list_pred(in_E), 1 / 2) and Acc(list_pred(in_Euc), 1 / 2)
                  and Acc(list_pred(in_Euo), 1 / 2))
        Invariant(ToSeq(in_E) == Old(ToSeq(in_E)))
        Invariant(ToSeq(in_Euc) == Old(ToSeq(in_Euc)))
        Invariant(ToSeq(in_Euo) == Old(ToSeq(in_Euo)))
        Invariant(len(in_E) == m and len(in_Euc) == m and len(in_Euo) == m
                  and 0 <= e and e <= m)
        Invariant(Forall(int, lambda f: Implies(0 <= f and f < e,
                  Implies(in_Euc[f], in_E[f]) and Implies(in_Euo[f], in_E[f]))))
        if in_Euc[e] and not in_E[e]:
            return False
        if in_Euo[e] and not in_E[e]:
            return False
        e += 1
    return True


def check_init(n: int, init: List[bool], deterministic: bool) -> bool:
    Requires(Acc(list_pred(init), 1 / 2))
    Ensures(Acc(list_pred(init), 1 / 2))
    Ensures(ToSeq(init) == Old(ToSeq(init)))
    Ensures(Result() == init_ok(n, init, deterministic))
    if len(init) != n:
        return False
    first = -1          # index of the first initial state, -1 = none yet
    x = 0
    while x < n:
        Invariant(Acc(list_pred(init), 1 / 2))
        Invariant(ToSeq(init) == Old(ToSeq(init)))
        Invariant(len(init) == n and 0 <= x and x <= n and -1 <= first and first < x)
        Invariant(Implies(first == -1,
                          Forall(int, lambda y: Implies(0 <= y and y < x, not init[y]))))
        Invariant(Implies(first >= 0, init[first]))
        Invariant(Implies(deterministic and first >= 0,
                  Forall(int, lambda y: Implies(0 <= y and y < x and init[y], y == first))))
        if init[x]:
            if first == -1:
                first = x
            elif deterministic:
                return False
        x += 1
    if n > 0 and first == -1:
        return False
    return True


def check_block(evt: List[int], lo: int, hi: int) -> bool:
    """True iff no event occurs twice among positions lo .. hi-1. Compares each position with the
    earlier ones of the block and stops at the first repeat, so a block is never scanned past
    (number of distinct events + 1) positions."""
    Requires(Acc(list_pred(evt), 1 / 2))
    Requires(0 <= lo and lo <= hi and hi <= len(evt))
    Ensures(Acc(list_pred(evt), 1 / 2) and hi <= len(evt))
    Ensures(ToSeq(evt) == Old(ToSeq(evt)))
    Ensures(Result() == block_det(lo, hi, evt))
    k = lo
    while k < hi:
        Invariant(Acc(list_pred(evt), 1 / 2))
        Invariant(ToSeq(evt) == Old(ToSeq(evt)))
        Invariant(0 <= lo and lo <= k and k <= hi and hi <= len(evt))
        Invariant(Forall2(int, int, lambda j, i: Implies(lo <= j and j < i and i < k,
                                                         evt[j] != evt[i])))
        j = lo
        while j < k:
            Invariant(Acc(list_pred(evt), 1 / 2))
            Invariant(ToSeq(evt) == Old(ToSeq(evt)))
            Invariant(0 <= lo and lo <= j and j <= k and k < hi and hi <= len(evt))
            Invariant(Forall2(int, int, lambda a, b: Implies(lo <= a and a < b and b < k,
                                                             evt[a] != evt[b])))
            Invariant(Forall(int, lambda a: Implies(lo <= a and a < j, evt[a] != evt[k])))
            if evt[j] == evt[k]:
                return False
            j += 1
        k += 1
    return True


def check_det(n: int, start: List[int], evt: List[int]) -> bool:
    Requires(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2))
    Requires(blocks_ok(n, start, len(evt)))
    Ensures(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2))
    Ensures(ToSeq(start) == Old(ToSeq(start)))
    Ensures(ToSeq(evt) == Old(ToSeq(evt)))
    Ensures(blocks_ok(n, start, len(evt)))
    Ensures(Result() == det_ok(n, start, evt))
    x = 0
    while x < n:
        Invariant(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2))
        Invariant(ToSeq(start) == Old(ToSeq(start)))
        Invariant(ToSeq(evt) == Old(ToSeq(evt)))
        Invariant(0 <= x and x <= n)
        Invariant(blocks_ok(n, start, len(evt)))
        Invariant(Forall(int, lambda y: (Implies(0 <= y and y < x,
                                                 block_det(start[y], start[y + 1], evt)),
                                         [[block_det(start[y], start[y + 1], evt)]])))
        if not check_block(evt, start[x], start[x + 1]):
            return False
        x += 1
    return True


def check_automaton(n: int, m: int, in_E: List[bool], in_Euc: List[bool], in_Euo: List[bool],
                    init: List[bool], marked: List[bool], start: List[int], evt: List[int],
                    dst: List[int], deterministic: bool) -> int:
    """0 iff the encoding is valid; otherwise the number of the first failing condition:
    1 sizes, 2 blocks, 3 transitions (ranges, W1), 4 events (W2), 5 initial states (W3),
    6 more than one initial state, 7 a state with two transitions on one event."""
    Requires(Acc(list_pred(in_E), 1 / 2) and Acc(list_pred(in_Euc), 1 / 2)
             and Acc(list_pred(in_Euo), 1 / 2) and Acc(list_pred(init), 1 / 2)
             and Acc(list_pred(marked), 1 / 2) and Acc(list_pred(start), 1 / 2)
             and Acc(list_pred(evt), 1 / 2) and Acc(list_pred(dst), 1 / 2))
    Ensures(Acc(list_pred(in_E), 1 / 2) and Acc(list_pred(in_Euc), 1 / 2)
            and Acc(list_pred(in_Euo), 1 / 2) and Acc(list_pred(init), 1 / 2)
            and Acc(list_pred(marked), 1 / 2) and Acc(list_pred(start), 1 / 2)
            and Acc(list_pred(evt), 1 / 2) and Acc(list_pred(dst), 1 / 2))
    Ensures((Result() == 0) == valid_automaton(n, m, in_E, in_Euc, in_Euo, init, marked,
                                               start, evt, dst, deterministic))
    Ensures(Implies(Result() == 2, not blocks_ok(n, start, len(evt))))
    Ensures(Implies(Result() == 3, not transitions_ok(n, m, in_E, evt, dst)))
    Ensures(Implies(Result() == 4, not events_ok(m, in_E, in_Euc, in_Euo)))
    Ensures(Implies(Result() == 5, not init_ok(n, init, False)))
    Ensures(Implies(Result() == 6, not init_ok(n, init, True)))
    Ensures(Implies(Result() == 7, blocks_ok(n, start, len(evt)) and not det_ok(n, start, evt)))
    if n < 0 or m < 0 or len(marked) != n:
        return 1
    if not check_blocks(n, start, len(evt)):
        return 2
    if not check_transitions(n, m, in_E, evt, dst):
        return 3
    if not check_events(m, in_E, in_Euc, in_Euo):
        return 4
    if not check_init(n, init, False):
        return 5
    if deterministic:
        if not check_init(n, init, True):
            return 6
        if not check_det(n, start, evt):
            return 7
    return 0
