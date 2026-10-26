"""
Verified checker for the active-event index of an encoded automaton (certisc-proof/spec/basic_ops.md §3).

The index lists, for each state x, the positions where the runs of its sorted block start (one
run per event). With A = astart and H = heads:
    the run heads of x are H[A[x]], ..., H[A[x+1]-1], and the event of head i is evt[H[i]].
It is built once, by trusted code (core_aut/trusted/active_index.py), and checked here; a
ValidAutomaton keeps it, read-only, for the operations that use it.

Verify, from certisc-lib/ (Python >= 3.12, `verify` extra, Java):

    nagini src/core_aut/verified_core/active_index.py

Math notation (as in ops_aut/verified_ops/basic_ops.py):
    [a, b)       the integers a, ..., b-1;   T = |evt|;   block(x) = [start[x], start[x+1])
    hb(x)        [A[x], A[x+1]), the indices in H of the run heads of x
    nxt(i)       the end of the run of head i: H[i+1] if i+1 < a1, else s1
    For a state x: s0 = start[x], s1 = start[x+1] (its block), a0 = A[x], a1 = A[x+1] (its heads).

The predicates take these four numbers rather than x. Nagini treats ints as objects: from y = x
it does not conclude f(y) = f(x) for a function f, but list reads do normalize (start[y] is
start[x] when y = x). So "for every state y" can be connected to a fact proved for state x.
"""

from typing import List

from nagini_contracts.contracts import *
from nagini_contracts.obligations import MustTerminate

from core_aut.verified_core.check import block_sorted, blocks_ok, sorted_ok


# --- specification ---------------------------------------------------------------------------


@Pure
def nxt(H: List[int], s1: int, a1: int, i: int) -> int:
    """The end of the run that starts at head i (of a state with heads up to a1, block up to s1)."""
    # Why: read access.
    Requires(Acc(list_pred(H), 1 / 8))
    # Math: 0 ≤ i < a1 ≤ |H|
    Requires(0 <= i and i < a1 and a1 <= len(H))
    # Math: nxt(i) = H[i+1] if i+1 < a1, else s1
    if i + 1 < a1:
        return H[i + 1]
    return s1


@Pure
def run_ok(evt: List[int], H: List[int], s0: int, s1: int, a1: int, i: int) -> bool:
    """Head i starts a non-empty run inside [s0, s1) on one event; the next head (if any) is on a
    different event."""
    # Why: read access.
    Requires(Acc(list_pred(evt), 1 / 8) and Acc(list_pred(H), 1 / 8))
    # Math: 0 ≤ i < a1 ≤ |H|
    Requires(0 <= i and i < a1 and a1 <= len(H))
    # Math: 0 ≤ s0 ≤ H[i] < nxt(i) ≤ s1 ≤ T
    #       ∧ ∀ t ∈ [H[i], nxt(i)): evt[t] = evt[H[i]]
    #       ∧ (i+1 < a1 → H[i+1] < s1 ∧ evt[H[i]] ≠ evt[H[i+1]])
    # Why: the run of head i is the positions H[i] .. nxt-1, all on the event evt[H[i]].
    return (0 <= s0 and s0 <= H[i] and H[i] < nxt(H, s1, a1, i)
            and nxt(H, s1, a1, i) <= s1 and s1 <= len(evt)
            and Forall(int, lambda t: (Implies(H[i] <= t and t < nxt(H, s1, a1, i),
                                               evt[t] == evt[H[i]]), [[evt[t]]]))
            and Implies(i + 1 < a1, H[i + 1] < s1 and evt[H[i]] != evt[H[i + 1]]))


@Pure
def seg_ok(evt: List[int], H: List[int], s0: int, s1: int, a0: int, a1: int) -> bool:
    """The heads H[a0 .. a1-1] cover the block [s0, s1) run by run, with strictly increasing
    events."""
    # Why: read access.
    Requires(Acc(list_pred(evt), 1 / 8) and Acc(list_pred(H), 1 / 8))
    # Math: 0 ≤ a0 ≤ a1 ≤ |H|
    Requires(0 <= a0 and a0 <= a1 and a1 <= len(H))
    # Math: (a0 = a1 ⟺ s0 = s1)                          (no heads ⟺ empty block)
    #       ∧ (a0 < a1 → H[a0] = s0)                     (the first head opens the block)
    #       ∧ ∀ i ∈ [a0,a1): run_ok(i)                   (each run is constant)
    #       ∧ ∀ i1 < i2 ∈ [a0,a1): evt[H[i1]] < evt[H[i2]]   (no duplicates, by value)
    return ((a0 == a1) == (s0 == s1)
            and Implies(a0 < a1, H[a0] == s0)
            and Forall(int, lambda i: (Implies(a0 <= i and i < a1, run_ok(evt, H, s0, s1, a1, i)),
                                       [[run_ok(evt, H, s0, s1, a1, i)]]))
            and Forall2(int, int, lambda i1, i2: Implies(
                a0 <= i1 and i1 < i2 and i2 < a1 and 0 <= H[i1] and H[i1] < len(evt)
                and 0 <= H[i2] and H[i2] < len(evt),
                evt[H[i1]] < evt[H[i2]])))


# "index_ok(n, start, evt, A, H)" names this formula; contracts state it in full, because
# Nagini does not fold a function whose body applies other functions to quantified variables:
#
#     n ≥ 0 ∧ |A| = n+1 ∧ |start| = n+1 ∧ A[0] = 0 ∧ A[n] = |H|
#     ∧ ∀ x ∈ [0,n): 0 ≤ A[x] ≤ A[x+1] ≤ |H| ∧ seg_ok(start[x], start[x+1], A[x], A[x+1])
#
# i.e. A splits H into one list of heads per state (like start splits the transitions), and each
# state's heads are correct for its block.


# --- checkers --------------------------------------------------------------------------------
# Each loop invariant says what is established for the part scanned so far (as in check.py).


def check_run(evt: List[int], H: List[int], s0: int, s1: int, a1: int, i: int) -> bool:
    """True only if run_ok(i)."""
    # Why: read access (1/8: the caller keeps a share, so the lists are known unchanged after).
    Requires(Acc(list_pred(evt), 1 / 8) and Acc(list_pred(H), 1 / 8))
    # Math: termination measure 2.
    Requires(MustTerminate(2))
    # Math: 0 ≤ i < a1 ≤ |H|
    Requires(0 <= i and i < a1 and a1 <= len(H))
    # Why: gives the permissions back; restates the bounds for the caller.
    Ensures(Acc(list_pred(evt), 1 / 8) and Acc(list_pred(H), 1 / 8))
    Ensures(0 <= i and i < a1 and a1 <= len(H))
    # Math: Result → run_ok(i)
    # Why: the guarantee (a failing index is rejected; only a correct one passes).
    Ensures(Implies(Result(), run_ok(evt, H, s0, s1, a1, i)))
    h = H[i]                                   # the head position
    if i + 1 < a1:                             # nx = nxt(i): where this run ends
        nx = H[i + 1]
    else:
        nx = s1
    # Math: nx = nxt(i)
    # Why (hint): links the local to the definition.
    Assert(nx == nxt(H, s1, a1, i))
    if not (0 <= s0 and s0 <= h and h < nx and nx <= s1 and s1 <= len(evt)):
        return False                           # head or run outside the block, or empty run
    if i + 1 < a1:
        if not (H[i + 1] < s1 and evt[h] != evt[H[i + 1]]):
            return False                       # next head not inside, or on the same event
    t = h
    while t < nx:                              # every position of the run has the head's event
        # Math: termination measure nx - t + 1, decreasing.
        Invariant(MustTerminate(nx - t + 1))
        # Why: read access to evt only: the loop reads nothing else, so H stays outside the loop
        #      and Nagini keeps knowing its contents.
        Invariant(Acc(list_pred(evt), 1 / 8))
        Invariant(ToSeq(evt) == Old(ToSeq(evt)))
        # Math: 0 ≤ h ≤ t ≤ nx ≤ T
        Invariant(0 <= h and h <= t and t <= nx and nx <= len(evt))
        # Math: ∀ u ∈ [h, t): evt[u] = evt[h]
        Invariant(Forall(int, lambda u: (Implies(h <= u and u < t, evt[u] == evt[h]),
                                         [[evt[u]]])))
        if evt[t] != evt[h]:
            return False                       # the run is not constant
        t += 1
    return True


def check_seg(evt: List[int], H: List[int], s0: int, s1: int, a0: int, a1: int) -> bool:
    """True only if seg_ok(s0, s1, a0, a1): the heads of one state are correct."""
    # Why: read access (1/4: passes 1/8 to check_run and keeps 1/8).
    Requires(Acc(list_pred(evt), 1 / 4) and Acc(list_pred(H), 1 / 4))
    # Math: termination measure 3 (calls check_run, measure 2).
    Requires(MustTerminate(3))
    # Math: 0 ≤ a0 ≤ a1 ≤ |H| ∧ 0 ≤ s0 ≤ s1 ≤ T ∧ block_sorted(s0, s1)
    # Why: valid ranges; the block is sorted (used to get strictly increasing head events).
    Requires(0 <= a0 and a0 <= a1 and a1 <= len(H))
    Requires(0 <= s0 and s0 <= s1 and s1 <= len(evt) and block_sorted(s0, s1, evt))
    # Why: gives the permissions back; restates the bounds for the caller.
    Ensures(Acc(list_pred(evt), 1 / 4) and Acc(list_pred(H), 1 / 4))
    Ensures(0 <= a0 and a0 <= a1 and a1 <= len(H))
    # Math: Result → seg_ok(s0, s1, a0, a1)
    Ensures(Implies(Result(), seg_ok(evt, H, s0, s1, a0, a1)))
    if (a0 == a1) != (s0 == s1):
        return False                           # heads ⟺ non-empty block, violated
    if a0 < a1 and H[a0] != s0:
        return False                           # the first head does not open the block
    i = a0
    while i < a1:
        # Math: termination measure a1 - i + 3, decreasing (> 2: calls check_run).
        Invariant(MustTerminate(a1 - i + 3))
        # Why: read access; lists unchanged.
        Invariant(Acc(list_pred(evt), 1 / 4) and Acc(list_pred(H), 1 / 4))
        Invariant(ToSeq(evt) == Old(ToSeq(evt)) and ToSeq(H) == Old(ToSeq(H)))
        # Math: the precondition facts, and a0 ≤ i ≤ a1
        Invariant(0 <= a0 and a0 <= a1 and a1 <= len(H) and a0 <= i and i <= a1)
        Invariant(0 <= s0 and s0 <= s1 and s1 <= len(evt) and block_sorted(s0, s1, evt))
        Invariant((a0 == a1) == (s0 == s1))
        Invariant(Implies(a0 < a1, H[a0] == s0))
        # Math: ∀ j ∈ [a0, i): run_ok(j)
        Invariant(Forall(int, lambda j: (Implies(a0 <= j and j < i, run_ok(evt, H, s0, s1, a1, j)),
                                         [[run_ok(evt, H, s0, s1, a1, j)]])))
        # Math: ∀ i1 < i2 ∈ [a0, i): evt[H[i1]] < evt[H[i2]]
        # Why: strictly increasing so far (no duplicates by value).
        Invariant(Forall2(int, int, lambda i1, i2: Implies(
            a0 <= i1 and i1 < i2 and i2 < i and 0 <= H[i1] and H[i1] < len(evt)
            and 0 <= H[i2] and H[i2] < len(evt),
            evt[H[i1]] < evt[H[i2]])))
        if not check_run(evt, H, s0, s1, a1, i):
            return False
        # Math: run_ok(i)
        # Why (hint): from check_run.
        Assert(run_ok(evt, H, s0, s1, a1, i))
        if i > a0:
            # Math: evt[H[i-1]] < evt[H[i]]
            # Why (hint): H[i-1] < nxt(i-1) = H[i] in a sorted block gives ≤; run_ok(i-1) says
            #      the two events differ.
            Assert(run_ok(evt, H, s0, s1, a1, i - 1))
            Assert(nxt(H, s1, a1, i - 1) == H[i])
            Assert(evt[H[i - 1]] <= evt[H[i]])
            Assert(evt[H[i - 1]] < evt[H[i]])
            # Math: ∀ i1 ∈ [a0, i): evt[H[i1]] < evt[H[i]]
            # Why (hint): earlier heads are below evt[H[i-1]] (invariant), hence below evt[H[i]].
            Assert(Forall(int, lambda i1: (Implies(a0 <= i1 and i1 < i - 1 and 0 <= H[i1]
                                                   and H[i1] < len(evt),
                                                   evt[H[i1]] < evt[H[i - 1]]), [[H[i1]]])))
            Assert(Forall(int, lambda i1: (Implies(a0 <= i1 and i1 < i and 0 <= H[i1]
                                                   and H[i1] < len(evt),
                                                   evt[H[i1]] < evt[H[i]]), [[H[i1]]])))
        i += 1
    return True


def sorted_block(n: int, start: List[int], evt: List[int], x: int) -> None:
    """Lemma: in a validated automaton, the block of a state is a valid, sorted range."""
    # Why: read access (1/8: the caller keeps a share).
    Requires(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8))
    # Math: termination measure 1.
    Requires(MustTerminate(1))
    # Math: blocks_ok(n, start, T) ∧ sorted_ok(n, start, evt) ∧ x ∈ [0,n)
    Requires(blocks_ok(n, start, len(evt)) and sorted_ok(n, start, evt) and 0 <= x and x < n)
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8))
    # Math: x+1 < |start| ∧ 0 ≤ start[x] ≤ start[x+1] ≤ T ∧ block_sorted(start[x], start[x+1])
    Ensures(x + 1 < len(start) and 0 <= start[x] and start[x] <= start[x + 1]
            and start[x + 1] <= len(evt) and block_sorted(start[x], start[x + 1], evt))
    # Math: start[x+1] ≤ T ∧ block_sorted(...)
    # Why (hint): mentioning the terms triggers blocks_ok's and sorted_ok's quantifiers at x.
    Assert(start[x + 1] <= len(evt))
    Assert(block_sorted(start[x], start[x + 1], evt))


def check_index(n: int, start: List[int], evt: List[int], A: List[int], H: List[int]) -> bool:
    """True only if index_ok (the formula above): the active-event index is correct."""
    # Why: read access.
    Requires(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2)
             and Acc(list_pred(A), 1 / 2) and Acc(list_pred(H), 1 / 2))
    # Math: termination measure n + 6.
    Requires(MustTerminate(n + 6))
    # Math: blocks_ok(n, start, T) ∧ sorted_ok(n, start, evt)
    # Why: the automaton was validated (check_automaton), so its blocks are valid and sorted.
    Requires(blocks_ok(n, start, len(evt)) and sorted_ok(n, start, evt))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2)
            and Acc(list_pred(A), 1 / 2) and Acc(list_pred(H), 1 / 2))
    # Math: Result → index_ok(n, start, evt, A, H)   (the formula above, stated in full)
    # Why: the guarantee: a passing index is correct for every state.
    Ensures(Implies(Result(), n >= 0 and len(A) == n + 1 and len(start) == n + 1 and A[0] == 0
                    and A[n] == len(H)
                    and Forall(int, lambda y: (
                        Implies(0 <= y and y < n,
                                0 <= A[y] and A[y] <= A[y + 1] and A[y + 1] <= len(H)
                                and seg_ok(evt, H, start[y], start[y + 1], A[y], A[y + 1])),
                        [[A[y + 1]]]))))
    if n < 0 or len(A) != n + 1 or len(start) != n + 1:
        return False
    if A[0] != 0 or A[n] != len(H):
        return False
    x = 0
    while x < n:
        # Math: termination measure n - x + 4 (> 3: calls check_seg).
        Invariant(MustTerminate(n - x + 4))
        # Why: read access; lists unchanged.
        Invariant(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2)
                  and Acc(list_pred(A), 1 / 2) and Acc(list_pred(H), 1 / 2))
        Invariant(ToSeq(start) == Old(ToSeq(start)) and ToSeq(evt) == Old(ToSeq(evt))
                  and ToSeq(A) == Old(ToSeq(A)) and ToSeq(H) == Old(ToSeq(H)))
        # Math: the precondition facts, sizes, and 0 ≤ x ≤ n
        Invariant(blocks_ok(n, start, len(evt)) and sorted_ok(n, start, evt))
        Invariant(n >= 0 and len(A) == n + 1 and len(start) == n + 1 and A[0] == 0
                  and A[n] == len(H) and 0 <= x and x <= n)
        # Math: ∀ y ∈ [0,x): 0 ≤ A[y] ≤ A[y+1] ≤ |H| ∧ seg_ok(start[y], start[y+1], A[y], A[y+1])
        Invariant(Forall(int, lambda y: (
            Implies(0 <= y and y < x,
                    0 <= A[y] and A[y] <= A[y + 1] and A[y + 1] <= len(H)
                    and seg_ok(evt, H, start[y], start[y + 1], A[y], A[y + 1])),
            [[A[y + 1]]])))
        if not (0 <= A[x] and A[x] <= A[x + 1] and A[x + 1] <= len(H)):
            return False
        sorted_block(n, start, evt, x)        # lemma: block(x) is a valid, sorted range
        if not check_seg(evt, H, start[x], start[x + 1], A[x], A[x + 1]):
            return False
        nx = x + 1
        # Math: ∀ y ∈ [0,nx): ... (the invariant, extended to x)
        # Why (hint): written out with nx, the same object x becomes below (Nagini compares ints as
        #      objects in terms). The instance y = x is what check_seg just gave; the list reads
        #      start[y], A[y] normalize, so it matches.
        Assert(Forall(int, lambda y: (
            Implies(0 <= y and y < nx,
                    0 <= A[y] and A[y] <= A[y + 1] and A[y + 1] <= len(H)
                    and seg_ok(evt, H, start[y], start[y + 1], A[y], A[y + 1])),
            [[A[y + 1]]])))
        x = nx
    # Math: index_ok: ∀ y ∈ [0,n): ... (the invariant at x = n, written with n)
    # Why (hint): the postcondition's quantifier, written out.
    Assert(Forall(int, lambda y: (
        Implies(0 <= y and y < n,
                0 <= A[y] and A[y] <= A[y + 1] and A[y + 1] <= len(H)
                and seg_ok(evt, H, start[y], start[y + 1], A[y], A[y + 1])),
        [[A[y + 1]]])))
    return True
