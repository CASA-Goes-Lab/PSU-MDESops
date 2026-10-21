"""
Verified validity checker for the encoded automaton (DESops-proof/spec/wrapper.md, section 5).

Verify with Nagini (Python >= 3.12, `verify` extra, Java), from DESops-lib/:

    nagini DESops/verified/check.py

(about 15-25 s, "Verification successful").

What is proved, for every input:
- Each `check_*` function returns True exactly when its `*_ok` predicate holds.
- `check_automaton` returns 0 exactly when `valid_automaton` holds, and a nonzero code names a
  condition that fails.
- Every function terminates (`MustTerminate`), never reads outside a list, and never changes its
  input lists.

How to read this file:
- The `@Pure` functions are the SPECIFICATION. They are formulas, not code that runs during the
  proof. They are the list form of (W1)-(W3) and determinism in
  DESops-proof/spec/automaton.md, section 3. A person checks that they say the right thing.
- The `check_*` functions are the CODE. Nagini proves that each one computes its predicate.
- Contract statements: `Requires` (precondition), `Ensures` (postcondition; `Result()` is the
  return value), `Invariant` (holds each time a loop reaches its test), `MustTerminate(k)` (the
  method, or loop, terminates; for a loop, k must decrease on every iteration and stay positive).
  `Acc(list_pred(l), 1 / 2)` is permission to read list `l` (half permission: read only).
  `ToSeq(l) == Old(ToSeq(l))` says the contents of `l` are unchanged.
  `Forall(int, lambda x: (..., [[t]]))` reads "for every integer x"; `[[t]]` is a trigger, a hint
  telling the solver which terms to instantiate the formula at.
- At runtime the contract calls are no-ops (DESops/verified/_contracts.py).

The automaton arrives as plain lists (DESops/verified/encoding.py):
    n, m              number of states (0 .. n-1) and of events (0 .. m-1)
    in_E, in_Euc,     in_E[e]: event e is in E; likewise Euc, Euo (length m)
    in_Euo
    init, marked      init[x]: state x is initial; marked[x]: x is marked (length n)
    start, evt, dst   transitions grouped by source state: state x owns positions
                      start[x] .. start[x+1]-1, and position k is the transition
                      x --evt[k]--> dst[k]
"""

from typing import List

from nagini_contracts.contracts import *
from nagini_contracts.obligations import MustTerminate

# --- vocabulary ------------------------------------------------------------------------------
# Named ranges, used by the specification and by the loop invariants.
#
# Every Forall/Exists that uses one of these carries an explicit trigger on a list read
# ([[evt[k]], [dst[k]]], [[init[x]]], ...). Without it, the solver may pick the helper call
# itself (e.g. is_state(n, x)) as the trigger, and verification ran past 4 minutes instead of
# about 15 s. The triggers change only how the solver searches, not what is proved.


@Pure
def is_state(n: int, x: int) -> bool:
    """x is one of the n states 0 .. n-1."""
    return 0 <= x and x < n


@Pure
def is_event(m: int, e: int) -> bool:
    """e is one of the m event numbers 0 .. m-1."""
    return 0 <= e and e < m


@Pure
def is_position(T: int, k: int) -> bool:
    """k is one of the T transition positions 0 .. T-1 (an index into evt and dst)."""
    return 0 <= k and k < T


# --- specification ---------------------------------------------------------------------------


@Pure
def blocks_ok(n: int, start: List[int], T: int) -> bool:
    """`start` splits the transition positions 0 .. T-1 into n consecutive blocks, one per state:
    state x owns positions start[x] .. start[x+1]-1 (empty when the two are equal)."""
    Requires(Acc(list_pred(start), 1 / 2))
    # One boundary per state, plus a closing one.
    if n < 0 or len(start) != n + 1:
        return False
    # The first block starts at position 0; the last block ends at T.
    if start[0] != 0 or start[n] != T:
        return False
    # Every block lies inside 0 .. T and does not run backwards.
    return Forall(int, lambda x: (
        Implies(is_state(n, x),
                0 <= start[x] and start[x] <= start[x + 1] and start[x + 1] <= T),
        [[start[x + 1]]]))


@Pure
def transitions_ok(n: int, m: int, in_E: List[bool], evt: List[int], dst: List[int]) -> bool:
    """Every transition uses an event of E (W1), and its target is a state."""
    Requires(Acc(list_pred(in_E), 1 / 2) and Acc(list_pred(evt), 1 / 2)
             and Acc(list_pred(dst), 1 / 2))
    # One flag per event; one event and one target per transition.
    if len(in_E) != m or len(evt) != len(dst):
        return False
    # Transition k: its event is an event number, that event is in E (W1), its target is a state.
    return Forall(int, lambda k: (Implies(
        is_position(len(evt), k),
        is_event(m, evt[k]) and in_E[evt[k]] and is_state(n, dst[k])),
        [[evt[k]], [dst[k]]]))


@Pure
def events_ok(m: int, in_E: List[bool], in_Euc: List[bool], in_Euo: List[bool]) -> bool:
    """(W2): Euc and Euo are subsets of E."""
    Requires(Acc(list_pred(in_E), 1 / 2) and Acc(list_pred(in_Euc), 1 / 2)
             and Acc(list_pred(in_Euo), 1 / 2))
    # One flag per event in each of E, Euc, Euo.
    if len(in_E) != m or len(in_Euc) != m or len(in_Euo) != m:
        return False
    # An uncontrollable or unobservable event is in E.
    return Forall(int, lambda e: (Implies(
        is_event(m, e),
        Implies(in_Euc[e], in_E[e]) and Implies(in_Euo[e], in_E[e])),
        [[in_E[e]], [in_Euc[e]], [in_Euo[e]]]))


@Pure
def init_ok(n: int, init: List[bool], deterministic: bool) -> bool:
    """(W3): an initial state exactly when there are states; at most one if deterministic."""
    Requires(Acc(list_pred(init), 1 / 2))
    # One flag per state. (So with no states there is no initial state.)
    if len(init) != n:
        return False
    # With states, at least one of them is initial.
    if n != 0 and not Exists(int, lambda x: (is_state(n, x) and init[x], [[init[x]]])):
        return False
    # Deterministic: two initial states are the same state.
    return (not deterministic) or Forall2(int, int, lambda x, y: (Implies(
        is_state(n, x) and is_state(n, y) and init[x] and init[y],
        x == y), [[init[x], init[y]]]))


@Pure
def block_det(lo: int, hi: int, evt: List[int]) -> bool:
    """No event occurs twice among positions lo .. hi-1 (one state's block)."""
    Requires(Acc(list_pred(evt), 1 / 2))
    Requires(0 <= lo and lo <= hi and hi <= len(evt))
    # Two positions j < i of the block carry different events.
    return Forall2(int, int, lambda j, i: Implies(
        lo <= j and j < i and i < hi,
        evt[j] != evt[i]))


@Pure
def det_ok(n: int, start: List[int], evt: List[int]) -> bool:
    """Determinism: no state has two transitions with the same event."""
    Requires(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2))
    Requires(blocks_ok(n, start, len(evt)))
    # Every state's block has no repeated event.
    return Forall(int, lambda x: (
        Implies(is_state(n, x), block_det(start[x], start[x + 1], evt)),
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
    # Sizes: no negative counts; one marking flag per state.
    if n < 0 or m < 0 or len(marked) != n:
        return False
    # The transition blocks tile the positions of evt / dst.
    if not blocks_ok(n, start, len(evt)):
        return False
    # (W1) and ranges of events and targets.
    if not transitions_ok(n, m, in_E, evt, dst):
        return False
    # (W2).
    if not events_ok(m, in_E, in_Euc, in_Euo):
        return False
    # (W3), and at most one initial state if deterministic.
    if not init_ok(n, init, deterministic):
        return False
    # Deterministic: no state has two transitions with the same event.
    return (not deterministic) or det_ok(n, start, evt)


# --- checkers --------------------------------------------------------------------------------
# Each loop invariant says what the loop has established so far, about the part already scanned.
# When the loop ends, that part is everything, so the invariant becomes the predicate.


def check_blocks(n: int, start: List[int], T: int) -> bool:
    Requires(MustTerminate(2))
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
        Invariant(MustTerminate(n - x + 2))
        Invariant(Acc(list_pred(start), 1 / 2))
        Invariant(ToSeq(start) == Old(ToSeq(start)))
        # The size and end checks above passed; x is in 0 .. n.
        Invariant(n >= 0 and len(start) == n + 1 and 0 <= x and x <= n)
        Invariant(start[0] == 0 and start[n] == T)
        # Blocks of states 0 .. x-1 lie inside 0 .. T and do not run backwards.
        Invariant(Forall(int, lambda y: (
            Implies(is_state(x, y),
                    0 <= start[y] and start[y] <= start[y + 1] and start[y + 1] <= T),
            [[start[y + 1]]])))
        lo = start[x]
        hi = start[x + 1]      # read both first: the solver needs the term start[x + 1] on every path
        if lo < 0 or lo > hi or hi > T:
            return False
        x += 1
    return True


def check_transitions(n: int, m: int, in_E: List[bool], evt: List[int], dst: List[int]) -> bool:
    Requires(MustTerminate(2))
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
        Invariant(MustTerminate(len(evt) - k + 2))   # after Acc: reading len(evt) needs it
        Invariant(ToSeq(in_E) == Old(ToSeq(in_E)))
        Invariant(ToSeq(evt) == Old(ToSeq(evt)))
        Invariant(ToSeq(dst) == Old(ToSeq(dst)))
        # The size checks above passed; k is in 0 .. len(evt).
        Invariant(len(in_E) == m and len(evt) == len(dst) and 0 <= k and k <= len(evt))
        # Transitions 0 .. k-1 are fine: event number in range, event in E, target a state.
        Invariant(Forall(int, lambda j: (Implies(
            is_position(k, j),
            is_event(m, evt[j]) and in_E[evt[j]] and is_state(n, dst[j])),
            [[evt[j]], [dst[j]]])))
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
    Requires(MustTerminate(2))
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
        Invariant(MustTerminate(m - e + 2))
        Invariant(Acc(list_pred(in_E), 1 / 2) and Acc(list_pred(in_Euc), 1 / 2)
                  and Acc(list_pred(in_Euo), 1 / 2))
        Invariant(ToSeq(in_E) == Old(ToSeq(in_E)))
        Invariant(ToSeq(in_Euc) == Old(ToSeq(in_Euc)))
        Invariant(ToSeq(in_Euo) == Old(ToSeq(in_Euo)))
        # The size checks above passed; e is in 0 .. m.
        Invariant(len(in_E) == m and len(in_Euc) == m and len(in_Euo) == m
                  and 0 <= e and e <= m)
        # Events 0 .. e-1: if uncontrollable or unobservable, then in E.
        Invariant(Forall(int, lambda f: (Implies(
            is_event(e, f),
            Implies(in_Euc[f], in_E[f]) and Implies(in_Euo[f], in_E[f])),
            [[in_E[f]], [in_Euc[f]], [in_Euo[f]]])))
        if in_Euc[e] and not in_E[e]:
            return False
        if in_Euo[e] and not in_E[e]:
            return False
        e += 1
    return True


def check_init(n: int, init: List[bool], deterministic: bool) -> bool:
    Requires(MustTerminate(2))
    Requires(Acc(list_pred(init), 1 / 2))
    Ensures(Acc(list_pred(init), 1 / 2))
    Ensures(ToSeq(init) == Old(ToSeq(init)))
    Ensures(Result() == init_ok(n, init, deterministic))
    if len(init) != n:
        return False
    first = -1          # index of the first initial state, -1 = none yet
    x = 0
    while x < n:
        Invariant(MustTerminate(n - x + 2))
        Invariant(Acc(list_pred(init), 1 / 2))
        Invariant(ToSeq(init) == Old(ToSeq(init)))
        # x is in 0 .. n; first is -1 or one of the states already scanned.
        Invariant(len(init) == n and 0 <= x and x <= n and -1 <= first and first < x)
        # first == -1: none of states 0 .. x-1 is initial.
        Invariant(Implies(first == -1,
                          Forall(int, lambda y: (Implies(is_state(x, y), not init[y]),
                                                 [[init[y]]]))))
        # first >= 0: first is an initial state.
        Invariant(Implies(first >= 0, init[first]))
        # Deterministic: every initial state among 0 .. x-1 is first.
        Invariant(Implies(deterministic and first >= 0,
                          Forall(int, lambda y: (Implies(is_state(x, y) and init[y],
                                                         y == first),
                                                 [[init[y]]]))))
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
    Requires(MustTerminate(2))
    Requires(Acc(list_pred(evt), 1 / 2))
    Requires(0 <= lo and lo <= hi and hi <= len(evt))
    Ensures(Acc(list_pred(evt), 1 / 2) and hi <= len(evt))
    Ensures(ToSeq(evt) == Old(ToSeq(evt)))
    Ensures(Result() == block_det(lo, hi, evt))
    k = lo
    while k < hi:
        Invariant(MustTerminate(hi - k + 2))
        Invariant(Acc(list_pred(evt), 1 / 2))
        Invariant(ToSeq(evt) == Old(ToSeq(evt)))
        Invariant(0 <= lo and lo <= k and k <= hi and hi <= len(evt))
        # Positions lo .. k-1 carry pairwise different events.
        Invariant(Forall2(int, int, lambda j, i: Implies(
            lo <= j and j < i and i < k,
            evt[j] != evt[i])))
        j = lo
        while j < k:
            Invariant(MustTerminate(k - j + 2))
            Invariant(Acc(list_pred(evt), 1 / 2))
            Invariant(ToSeq(evt) == Old(ToSeq(evt)))
            Invariant(0 <= lo and lo <= j and j <= k and k < hi and hi <= len(evt))
            # Still true from the outer loop: positions lo .. k-1 pairwise different.
            Invariant(Forall2(int, int, lambda a, b: Implies(
                lo <= a and a < b and b < k,
                evt[a] != evt[b])))
            # Positions lo .. j-1 differ from position k.
            Invariant(Forall(int, lambda a: Implies(
                lo <= a and a < j,
                evt[a] != evt[k])))
            if evt[j] == evt[k]:
                return False
            j += 1
        k += 1
    return True


def check_det(n: int, start: List[int], evt: List[int]) -> bool:
    Requires(MustTerminate(3))
    Requires(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2))
    Requires(blocks_ok(n, start, len(evt)))
    Ensures(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2))
    Ensures(ToSeq(start) == Old(ToSeq(start)))
    Ensures(ToSeq(evt) == Old(ToSeq(evt)))
    Ensures(blocks_ok(n, start, len(evt)))
    Ensures(Result() == det_ok(n, start, evt))
    x = 0
    while x < n:
        Invariant(MustTerminate(n - x + 3))     # > 2: the loop calls check_block (measure 2)
        Invariant(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2))
        Invariant(ToSeq(start) == Old(ToSeq(start)))
        Invariant(ToSeq(evt) == Old(ToSeq(evt)))
        Invariant(0 <= x and x <= n)
        Invariant(blocks_ok(n, start, len(evt)))
        # States 0 .. x-1 have no repeated event in their blocks.
        Invariant(Forall(int, lambda y: (
            Implies(is_state(x, y), block_det(start[y], start[y + 1], evt)),
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
    Requires(MustTerminate(4))                  # > 3: calls check_det (measure 3)
    Requires(Acc(list_pred(in_E), 1 / 2) and Acc(list_pred(in_Euc), 1 / 2)
             and Acc(list_pred(in_Euo), 1 / 2) and Acc(list_pred(init), 1 / 2)
             and Acc(list_pred(marked), 1 / 2) and Acc(list_pred(start), 1 / 2)
             and Acc(list_pred(evt), 1 / 2) and Acc(list_pred(dst), 1 / 2))
    Ensures(Acc(list_pred(in_E), 1 / 2) and Acc(list_pred(in_Euc), 1 / 2)
            and Acc(list_pred(in_Euo), 1 / 2) and Acc(list_pred(init), 1 / 2)
            and Acc(list_pred(marked), 1 / 2) and Acc(list_pred(start), 1 / 2)
            and Acc(list_pred(evt), 1 / 2) and Acc(list_pred(dst), 1 / 2))
    # The main guarantee: 0 exactly for valid automata.
    Ensures((Result() == 0) == valid_automaton(n, m, in_E, in_Euc, in_Euo, init, marked,
                                               start, evt, dst, deterministic))
    # Each error code is returned only when its condition really fails.
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
