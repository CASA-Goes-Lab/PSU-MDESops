"""
Verified checker for the reverse index of an encoded automaton (certisc-proof/spec/coreach.md).

The encoding groups the transitions by source: block(x) = [start[x], start[x+1]) of dst. The
reverse index groups them by target:
    rblock(y) = [rstart[y], rstart[y+1])   the reverse positions of the transitions into y;
    rk[j]                                   the (forward) transition at reverse position j;
    rsrc[j]                                 its source state;
    pos[k]                                  the reverse position of transition k (the inverse).
So (rstart, rsrc) is an encoding of the reversed automaton: going "forward" in it is going
backward in the automaton. It is built once, by trusted code (core_aut/trusted/reverse_index.py),
and checked here; a ValidAutomaton keeps it, read-only, for the operations that go backward.

Verify, from certisc-lib/ (Python >= 3.12, `verify` extra, Java):

    nagini src/core_aut/verified_core/reverse_index.py

Math notation used in the comments:
    [a, b)       the integers a, a+1, ..., b-1
    |l|          the length of list (or sequence) l
    T            |dst|, the number of transitions
    block(x)     [start[x], start[x+1]), the positions of the transitions out of x
    rblock(y)    [rstart[y], rstart[y+1]), the reverse positions of the transitions into y
    st, ds, rst, rk, rs, ps   ToSeq of start, dst, rstart, rk, rsrc, pos (values, not lists)

How to read the contracts (all removed before the code runs; core_aut/trusted/_strip.py):
- Requires(P) / Ensures(P)   precondition (the caller makes P true) / postcondition.
- Invariant(P)               loop invariant: true before the loop and kept by each iteration.
- Assert(P)                  a proof step, checked by Nagini. "Why (hint)": a fact Nagini can
                             prove but would not find by itself.
- Acc(list_pred(l), q)       permission to use list l: q = 1 read and write; q < 1 read only.
                             (A permission, not a formula: no Math.)
- MustTerminate(t)           the method (loop) terminates; t goes down; a method only calls
                             methods with a smaller t.
- ToSeq(l)                   the contents of list l as a value (a sequence).
- PSeq[int]                  the type of such a value.
- Old(e)                     e when the method was called.
- Implies(a, b)              a → b.
- Forall(int, lambda i: (P, [[t]]))   ∀ i ∈ ℤ: P; Nagini uses it for an i where the term t
                             appears (the trigger).
- Result()                   the method's return value.
- @Pure                      a side-effect-free function, usable in contracts (a definition).

Note on ints: Nagini treats ints as objects, so from i == j it does not conclude f(i) == f(j)
for a function f (list reads do compare by value). Loops therefore step with a new variable
(ny = y + 1; y = ny) and the invariants use the exact variables.

Map of the file:
- specification: the four facts (src_ok, tgt_ok, pos_ok, own_ok); in_blk is in blocks.py;
- one checker method per fact;
- check_reverse: the whole check (the four, plus the block structure of rstart).
"""

from typing import List

from nagini_contracts.contracts import *
from nagini_contracts.obligations import MustTerminate

# blocks_ok and its checker, from the verified validity checker.
from core_aut.verified_core.check import blocks_ok, check_blocks
# in_blk: "k is in block x" (shared with reach.py and coreach.py).
from core_aut.verified_core.blocks import in_blk


# --- specification ---------------------------------------------------------------------------
# Definitions used in the contracts. They say what "correct" means; they run no code.


# src_ok: each reverse position j names a transition rk[j] and its source rsrc[j], correctly.
# Used in: coreachable's witnesses (the transition taken from a state, toward a target).
@Pure
def src_ok(n: int, st: PSeq[int], T: int, rk: PSeq[int], rs: PSeq[int]) -> bool:
    """|rk| = |rsrc| = T, and rk[j] is a transition out of the state rsrc[j]."""
    # Math: |rk| = |rs| = T ∧ ∀ j ∈ [0,T): rk[j] ∈ [0,T) ∧ rs[j] ∈ [0,n) ∧ rs[j]+1 < |st|
    #                                      ∧ st[rs[j]] ≤ rk[j] < st[rs[j]+1]
    # Why: "rk[j] ∈ block(rsrc[j])". Trigger rs[j]: the reversed search reads rsrc (its "dst").
    return (len(rk) == T and len(rs) == T
            and Forall(int, lambda j: (Implies(0 <= j and j < T,
                                               0 <= rk[j] and rk[j] < T and 0 <= rs[j]
                                               and rs[j] < n and rs[j] + 1 < len(st)
                                               and st[rs[j]] <= rk[j]
                                               and rk[j] < st[rs[j] + 1]),
                                       [[rs[j]]])))


# tgt_ok: every reverse position in rblock(y) is a transition into y.
# Used in: coreachable's witnesses (the transition reaches the next state).
@Pure
def tgt_ok(rst: PSeq[int], ds: PSeq[int], rk: PSeq[int]) -> bool:
    """For j ∈ rblock(y): dst[rk[j]] = y."""
    # Math: ∀ j ∈ [0,|rk|). ∀ y. j ∈ rblock(y) → rk[j] ∈ [0,T) ∧ dst[rk[j]] = y
    # Why: the reverse blocks really are "the transitions into y". Triggers: rk[j] for the
    #      outer ∀; in_blk(rst, y, j) for the inner (no single read contains both y and j).
    return Forall(int, lambda j: (Implies(
        0 <= j and j < len(rk),
        Forall(int, lambda y: (Implies(in_blk(rst, y, j),
                                       0 <= rk[j] and rk[j] < len(ds) and ds[rk[j]] == y),
                               [[in_blk(rst, y, j)]]))),
        [[rk[j]]]))


# pos_ok: every transition k appears in the reverse index, in the block of its target.
# Used in: coreachable's backward closure (completeness: no transition is missed).
@Pure
def pos_ok(rst: PSeq[int], ds: PSeq[int], rk: PSeq[int], ps: PSeq[int]) -> bool:
    """|pos| = T, and transition k sits at reverse position pos[k], inside rblock(dst[k])."""
    # Math: |ps| = T ∧ ∀ k ∈ [0,T): ps[k] ∈ [0,|rk|) ∧ rk[ps[k]] = k ∧ ps[k] ∈ rblock(dst[k])
    # Why: completeness without counting (pos is the inverse of rk). Trigger ps[k].
    return (len(ps) == len(ds)
            and Forall(int, lambda k: (Implies(0 <= k and k < len(ds),
                                               0 <= ps[k] and ps[k] < len(rk)
                                               and rk[ps[k]] == k
                                               and in_blk(rst, ds[k], ps[k])),
                                       [[ps[k]]])))


# own_ok: the source stored for transition k (at its reverse position) is k's real source.
# Used in: coreachable's backward closure: a transition from x into a coreachable state makes x
# coreachable, and the reversed search knows x as rsrc[pos[k]].
@Pure
def own_ok(st: PSeq[int], rs: PSeq[int], ps: PSeq[int]) -> bool:
    """For k ∈ block(x): rsrc[pos[k]] = x."""
    # Math: ∀ k ∈ [0,|ps|). ∀ x. k ∈ block(x) → ps[k] ∈ [0,|rs|) ∧ rs[ps[k]] = x
    # Why: stated directly (not derived from src_ok), so no "blocks do not overlap" proof is
    #      needed. Triggers: ps[k] outer; in_blk(st, x, k) inner.
    return Forall(int, lambda k: (Implies(
        0 <= k and k < len(ps),
        Forall(int, lambda x: (Implies(in_blk(st, x, k),
                                       0 <= ps[k] and ps[k] < len(rs) and rs[ps[k]] == x),
                               [[in_blk(st, x, k)]]))),
        [[ps[k]]]))


# --- checkers --------------------------------------------------------------------------------
# One method per fact. Each returns True only if its fact holds (Ensures Result() → fact).


# check_src: one pass over the reverse positions.
def check_src(n: int, start: List[int], T: int, rk: List[int], rsrc: List[int]) -> bool:
    """True only if src_ok."""
    # Why: read access.
    Requires(Acc(list_pred(start), 1 / 4) and Acc(list_pred(rk), 1 / 4)
             and Acc(list_pred(rsrc), 1 / 4))
    # Math: termination measure 2.
    # Why: one loop, no calls.
    Requires(MustTerminate(2))
    # Math: blocks_ok(n, start, T)
    # Why: so start[x], start[x+1] are valid reads for a state x.
    Requires(blocks_ok(n, start, T))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 4) and Acc(list_pred(rk), 1 / 4)
            and Acc(list_pred(rsrc), 1 / 4))
    # Math: Result → src_ok(n, st, T, rk, rs)
    # Why: the fact checked.
    Ensures(Implies(Result(), src_ok(n, ToSeq(start), T, ToSeq(rk), ToSeq(rsrc))))
    if len(rk) != T or len(rsrc) != T:       # Math: |rk| = |rs| = T, else reject
        return False
    j = 0                                    # the reverse position
    while j < T:                             # each reverse position
        # Why: read access, kept through the loop.
        Invariant(Acc(list_pred(start), 1 / 4) and Acc(list_pred(rk), 1 / 4)
                  and Acc(list_pred(rsrc), 1 / 4))
        # Math: measure T - j.
        # Why: j goes up by 1.
        Invariant(MustTerminate(T - j + 1))
        # Math: blocks_ok(n, start, T) ∧ |rk| = |rs| = T ∧ 0 ≤ j ≤ T
        # Why: the precondition and the lengths, kept; j in range.
        Invariant(blocks_ok(n, start, T) and len(rk) == T and len(rsrc) == T
                  and 0 <= j and j <= T)
        # Math: ∀ i ∈ [0,j): rk[i] ∈ [0,T) ∧ rs[i] ∈ [0,n) ∧ st[rs[i]] ≤ rk[i] < st[rs[i]+1]
        # Why: src_ok for the positions checked so far. Trigger rs[i], as in src_ok.
        Invariant(Forall(int, lambda i: (Implies(0 <= i and i < j,
                                                 0 <= ToSeq(rk)[i] and ToSeq(rk)[i] < T
                                                 and 0 <= ToSeq(rsrc)[i] and ToSeq(rsrc)[i] < n
                                                 and ToSeq(rsrc)[i] + 1 < len(ToSeq(start))
                                                 and ToSeq(start)[ToSeq(rsrc)[i]] <= ToSeq(rk)[i]
                                                 and ToSeq(rk)[i] < ToSeq(start)[ToSeq(rsrc)[i] + 1]),
                                         [[ToSeq(rsrc)[i]]])))
        x = rsrc[j]                          # the claimed source
        k = rk[j]                            # the claimed transition
        # Math: rs[j] = x ∧ rk[j] = k
        # Why (hint): the list reads, as sequence entries (the terms the invariant uses).
        Assert(ToSeq(rsrc)[j] == x and ToSeq(rk)[j] == k)
        if x < 0 or x >= n or k < 0 or k >= T:   # Math: x ∈ [0,n) ∧ k ∈ [0,T), else reject
            return False
        # Math: |start| = n+1 ∧ start[x+1] ≤ T
        # Why (hint): blocks_ok at x (mentioning start[x + 1] triggers it), so the reads below
        #      are in bounds.
        Assert(len(start) == n + 1 and start[x + 1] <= T)
        if k < start[x] or k >= start[x + 1]:    # Math: k ∈ block(x), else reject
            return False
        # Math: st[x] ≤ k < st[x+1]
        # Why (hint): the check above, as sequence entries.
        Assert(ToSeq(start)[x] <= k and k < ToSeq(start)[x + 1])
        nj = j + 1                           # the next position (a variable: the int note)
        j = nj
    # Math: src_ok(n, st, T, rk, rs)
    # Why (hint): the loop invariant at j = T is the body of src_ok.
    Assert(src_ok(n, ToSeq(start), T, ToSeq(rk), ToSeq(rsrc)))
    return True


# check_tgt: for each target y, each reverse position in rblock(y).
def check_tgt(n: int, dst: List[int], rstart: List[int], rk: List[int]) -> bool:
    """True only if tgt_ok."""
    # Why: read access.
    Requires(Acc(list_pred(dst), 1 / 4) and Acc(list_pred(rstart), 1 / 4)
             and Acc(list_pred(rk), 1 / 4))
    # Math: termination measure 3.
    # Why: two nested loops, no calls.
    Requires(MustTerminate(3))
    # Math: blocks_ok(n, rstart, |rk|)
    # Why: rblock(y) is a valid range of reverse positions.
    Requires(blocks_ok(n, rstart, len(rk)))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(dst), 1 / 4) and Acc(list_pred(rstart), 1 / 4)
            and Acc(list_pred(rk), 1 / 4))
    # Math: Result → tgt_ok(rst, ds, rk)
    # Why: the fact checked.
    Ensures(Implies(Result(), tgt_ok(ToSeq(rstart), ToSeq(dst), ToSeq(rk))))
    y = 0                                    # the target state
    while y < n:                             # each target
        # Why: read access, kept through the loop.
        Invariant(Acc(list_pred(dst), 1 / 4) and Acc(list_pred(rstart), 1 / 4)
                  and Acc(list_pred(rk), 1 / 4))
        # Math: measure n - y + 2 (> the inner loop's).
        # Why: y goes up by 1.
        Invariant(MustTerminate(n - y + 2))
        # Math: blocks_ok(n, rstart, |rk|) ∧ 0 ≤ y ≤ n
        # Why: the precondition, kept; y in range.
        Invariant(blocks_ok(n, rstart, len(rk)) and 0 <= y and y <= n)
        # Math: ∀ j ∈ [0,|rk|). ∀ z < y. j ∈ rblock(z) → rk[j] ∈ [0,T) ∧ dst[rk[j]] = z
        # Why: tgt_ok for the targets checked so far. Triggers as in tgt_ok.
        Invariant(Forall(int, lambda j: (Implies(
            0 <= j and j < len(ToSeq(rk)),
            Forall(int, lambda z: (Implies(in_blk(ToSeq(rstart), z, j) and z < y,
                                           0 <= ToSeq(rk)[j] and ToSeq(rk)[j] < len(ToSeq(dst))
                                           and ToSeq(dst)[ToSeq(rk)[j]] == z),
                                   [[in_blk(ToSeq(rstart), z, j)]]))),
            [[ToSeq(rk)[j]]])))
        # Math: |rstart| = n+1 ∧ 0 ≤ rstart[y] ≤ rstart[y+1] ≤ |rk|
        # Why (hint): blocks_ok at y, so rblock(y) is a valid range of rk. rstart[y + 1] comes
        #      first: it is the trigger of blocks_ok's ∀.
        Assert(len(rstart) == n + 1 and rstart[y + 1] <= len(rk) and 0 <= rstart[y]
               and rstart[y] <= rstart[y + 1])
        j = rstart[y]                        # first reverse position into y
        hi = rstart[y + 1]                   # one past the last
        while j < hi:                        # each transition into y
            # Why: read access, kept through the loop.
            Invariant(Acc(list_pred(dst), 1 / 4) and Acc(list_pred(rstart), 1 / 4)
                      and Acc(list_pred(rk), 1 / 4))
            # Math: measure hi - j + 1.
            # Why: j goes up by 1, up to hi.
            Invariant(MustTerminate(hi - j + 1))
            # Math: blocks_ok ∧ y ∈ [0,n) ∧ rstart[y] ≤ j ≤ hi = rstart[y+1] ≤ |rk|
            # Why: the outer facts, kept; j inside rblock(y).
            Invariant(blocks_ok(n, rstart, len(rk)) and 0 <= y and y < n
                      and len(rstart) == n + 1 and rstart[y] <= j and j <= hi
                      and hi == rstart[y + 1] and hi <= len(rk) and 0 <= rstart[y])
            # Math: ∀ i ∈ [0,|rk|). ∀ z. i ∈ rblock(z) ∧ (z < y ∨ (z = y ∧ i < j))
            #                              → rk[i] ∈ [0,T) ∧ dst[rk[i]] = z
            # Why: the targets before y, and rblock(y) up to j. Triggers as in tgt_ok.
            Invariant(Forall(int, lambda i: (Implies(
                0 <= i and i < len(ToSeq(rk)),
                Forall(int, lambda z: (Implies(in_blk(ToSeq(rstart), z, i)
                                               and (z < y or (z == y and i < j)),
                                               0 <= ToSeq(rk)[i] and ToSeq(rk)[i] < len(ToSeq(dst))
                                               and ToSeq(dst)[ToSeq(rk)[i]] == z),
                                       [[in_blk(ToSeq(rstart), z, i)]]))),
                [[ToSeq(rk)[i]]])))
            k = rk[j]                        # the transition at reverse position j
            if k < 0 or k >= len(dst):       # Math: k ∈ [0,T), else reject
                return False
            if dst[k] != y:                  # Math: dst[k] = y, else reject
                return False
            # Math: rk[j] = k ∧ ds[k] = y
            # Why (hint): the list reads, as sequence entries (the terms the invariant uses).
            Assert(ToSeq(rk)[j] == k and ToSeq(dst)[k] == y)
            nj = j + 1                       # the next position (a variable: the int note)
            j = nj
        ny = y + 1                           # the next target (a variable: the int note)
        # Math: ∀ i ∈ [0,|rk|). ∀ z < ny. i ∈ rblock(z) → rk[i] ∈ [0,T) ∧ dst[rk[i]] = z
        # Why (hint): z < y is the old part; z = y: i ∈ rblock(y) means i < rstart[y+1] = j.
        Assert(Forall(int, lambda i: (Implies(
            0 <= i and i < len(ToSeq(rk)),
            Forall(int, lambda z: (Implies(in_blk(ToSeq(rstart), z, i) and z < ny,
                                           0 <= ToSeq(rk)[i] and ToSeq(rk)[i] < len(ToSeq(dst))
                                           and ToSeq(dst)[ToSeq(rk)[i]] == z),
                                   [[in_blk(ToSeq(rstart), z, i)]]))),
            [[ToSeq(rk)[i]]])))
        y = ny
    # Math: tgt_ok(rst, ds, rk)
    # Why (hint): at y = n every block counts (in_blk(rst, z, j) gives z + 1 < n + 1).
    Assert(tgt_ok(ToSeq(rstart), ToSeq(dst), ToSeq(rk)))
    return True


# check_pos: one pass over the transitions.
def check_pos(n: int, dst: List[int], rstart: List[int], rk: List[int], pos: List[int]) -> bool:
    """True only if pos_ok."""
    # Why: read access.
    Requires(Acc(list_pred(dst), 1 / 4) and Acc(list_pred(rstart), 1 / 4)
             and Acc(list_pred(rk), 1 / 4) and Acc(list_pred(pos), 1 / 4))
    # Math: termination measure 2.
    # Why: one loop, no calls.
    Requires(MustTerminate(2))
    # Math: |rstart| = n+1 ∧ ∀ k ∈ [0,T): dst[k] ∈ [0,n)
    # Why: so rstart[dst[k]] and rstart[dst[k]+1] are valid reads.
    Requires(len(rstart) == n + 1)
    Requires(Forall(int, lambda k: (Implies(0 <= k and k < len(dst),
                                            0 <= dst[k] and dst[k] < n), [[dst[k]]])))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(dst), 1 / 4) and Acc(list_pred(rstart), 1 / 4)
            and Acc(list_pred(rk), 1 / 4) and Acc(list_pred(pos), 1 / 4))
    # Math: Result → pos_ok(rst, ds, rk, ps)
    # Why: the fact checked.
    Ensures(Implies(Result(), pos_ok(ToSeq(rstart), ToSeq(dst), ToSeq(rk), ToSeq(pos))))
    if len(pos) != len(dst):                 # Math: |pos| = T, else reject
        return False
    k = 0                                    # the transition
    while k < len(dst):                      # each transition
        # Why: read access, kept through the loop.
        Invariant(Acc(list_pred(dst), 1 / 4) and Acc(list_pred(rstart), 1 / 4)
                  and Acc(list_pred(rk), 1 / 4) and Acc(list_pred(pos), 1 / 4))
        # Math: measure T - k + 1.
        # Why: k goes up by 1.
        Invariant(MustTerminate(len(dst) - k + 1))
        # Math: 0 ≤ k ≤ T ∧ |pos| = T ∧ |rstart| = n+1 ∧ ∀ i: dst[i] ∈ [0,n)
        # Why: the preconditions and the length, kept.
        Invariant(0 <= k and k <= len(dst) and len(pos) == len(dst) and len(rstart) == n + 1)
        Invariant(Forall(int, lambda i: (Implies(0 <= i and i < len(dst),
                                                 0 <= dst[i] and dst[i] < n), [[dst[i]]])))
        # Math: ∀ i ∈ [0,k): ps[i] ∈ [0,|rk|) ∧ rk[ps[i]] = i ∧ ps[i] ∈ rblock(dst[i])
        # Why: pos_ok for the transitions checked so far. Trigger ps[i], as in pos_ok.
        Invariant(Forall(int, lambda i: (Implies(0 <= i and i < k,
                                                 0 <= ToSeq(pos)[i] and ToSeq(pos)[i] < len(rk)
                                                 and ToSeq(rk)[ToSeq(pos)[i]] == i
                                                 and in_blk(ToSeq(rstart), ToSeq(dst)[i],
                                                            ToSeq(pos)[i])),
                                         [[ToSeq(pos)[i]]])))
        j = pos[k]                           # the claimed reverse position of k
        y = dst[k]                           # the target of k
        # Math: ps[k] = j ∧ ds[k] = y
        # Why (hint): the list reads, as sequence entries (the terms the invariant uses).
        Assert(ToSeq(pos)[k] == j and ToSeq(dst)[k] == y)
        if j < 0 or j >= len(rk):            # Math: j ∈ [0,|rk|), else reject
            return False
        if rk[j] != k:                       # Math: rk[j] = k, else reject
            return False
        # Math: rk[j] = k
        # Why (hint): as a sequence entry.
        Assert(ToSeq(rk)[j] == k)
        if j < rstart[y] or j >= rstart[y + 1]:   # Math: j ∈ rblock(y), else reject
            return False
        # Math: in_blk(rst, dst[k], ps[k])
        # Why (hint): the check above, as the term the invariant uses.
        Assert(in_blk(ToSeq(rstart), y, j))
        nk = k + 1                           # the next transition (a variable: the int note)
        k = nk
    return True


# check_own: for each source x, each transition in block(x).
def check_own(n: int, start: List[int], rsrc: List[int], pos: List[int]) -> bool:
    """True only if own_ok."""
    # Why: read access.
    Requires(Acc(list_pred(start), 1 / 4) and Acc(list_pred(rsrc), 1 / 4)
             and Acc(list_pred(pos), 1 / 4))
    # Math: termination measure 3.
    # Why: two nested loops, no calls.
    Requires(MustTerminate(3))
    # Math: blocks_ok(n, start, |pos|)
    # Why: block(x) is a valid range of positions of pos.
    Requires(blocks_ok(n, start, len(pos)))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 4) and Acc(list_pred(rsrc), 1 / 4)
            and Acc(list_pred(pos), 1 / 4))
    # Math: Result → own_ok(st, rs, ps)
    # Why: the fact checked.
    Ensures(Implies(Result(), own_ok(ToSeq(start), ToSeq(rsrc), ToSeq(pos))))
    x = 0                                    # the source state
    while x < n:                             # each source
        # Why: read access, kept through the loop.
        Invariant(Acc(list_pred(start), 1 / 4) and Acc(list_pred(rsrc), 1 / 4)
                  and Acc(list_pred(pos), 1 / 4))
        # Math: measure n - x + 2 (> the inner loop's).
        # Why: x goes up by 1.
        Invariant(MustTerminate(n - x + 2))
        # Math: blocks_ok(n, start, |pos|) ∧ 0 ≤ x ≤ n
        # Why: the precondition, kept; x in range.
        Invariant(blocks_ok(n, start, len(pos)) and 0 <= x and x <= n)
        # Math: ∀ k ∈ [0,|ps|). ∀ z < x. k ∈ block(z) → ps[k] ∈ [0,|rs|) ∧ rs[ps[k]] = z
        # Why: own_ok for the sources checked so far. Triggers as in own_ok.
        Invariant(Forall(int, lambda k: (Implies(
            0 <= k and k < len(ToSeq(pos)),
            Forall(int, lambda z: (Implies(in_blk(ToSeq(start), z, k) and z < x,
                                           0 <= ToSeq(pos)[k] and ToSeq(pos)[k] < len(ToSeq(rsrc))
                                           and ToSeq(rsrc)[ToSeq(pos)[k]] == z),
                                   [[in_blk(ToSeq(start), z, k)]]))),
            [[ToSeq(pos)[k]]])))
        # Math: |start| = n+1 ∧ 0 ≤ start[x] ≤ start[x+1] ≤ |pos|
        # Why (hint): blocks_ok at x, so block(x) is a valid range of pos. start[x + 1] comes
        #      first: it is the trigger of blocks_ok's ∀.
        Assert(len(start) == n + 1 and start[x + 1] <= len(pos) and 0 <= start[x]
               and start[x] <= start[x + 1])
        k = start[x]                         # first transition of x
        hi = start[x + 1]                    # one past the last
        while k < hi:                        # each transition of x
            # Why: read access, kept through the loop.
            Invariant(Acc(list_pred(start), 1 / 4) and Acc(list_pred(rsrc), 1 / 4)
                      and Acc(list_pred(pos), 1 / 4))
            # Math: measure hi - k + 1.
            # Why: k goes up by 1, up to hi.
            Invariant(MustTerminate(hi - k + 1))
            # Math: blocks_ok ∧ x ∈ [0,n) ∧ start[x] ≤ k ≤ hi = start[x+1] ≤ |pos|
            # Why: the outer facts, kept; k inside block(x).
            Invariant(blocks_ok(n, start, len(pos)) and 0 <= x and x < n
                      and len(start) == n + 1 and start[x] <= k and k <= hi
                      and hi == start[x + 1] and hi <= len(pos) and 0 <= start[x])
            # Math: ∀ i ∈ [0,|ps|). ∀ z. i ∈ block(z) ∧ (z < x ∨ (z = x ∧ i < k))
            #                              → ps[i] ∈ [0,|rs|) ∧ rs[ps[i]] = z
            # Why: the sources before x, and block(x) up to k. Triggers as in own_ok.
            Invariant(Forall(int, lambda i: (Implies(
                0 <= i and i < len(ToSeq(pos)),
                Forall(int, lambda z: (Implies(in_blk(ToSeq(start), z, i)
                                               and (z < x or (z == x and i < k)),
                                               0 <= ToSeq(pos)[i] and ToSeq(pos)[i] < len(ToSeq(rsrc))
                                               and ToSeq(rsrc)[ToSeq(pos)[i]] == z),
                                       [[in_blk(ToSeq(start), z, i)]]))),
                [[ToSeq(pos)[i]]])))
            j = pos[k]                       # the reverse position of k
            if j < 0 or j >= len(rsrc):      # Math: j ∈ [0,|rs|), else reject
                return False
            if rsrc[j] != x:                 # Math: rs[j] = x, else reject
                return False
            # Math: ps[k] = j ∧ rs[j] = x
            # Why (hint): the list reads, as sequence entries (the terms the invariant uses).
            Assert(ToSeq(pos)[k] == j and ToSeq(rsrc)[j] == x)
            nk = k + 1                       # the next transition (a variable: the int note)
            k = nk
        nx = x + 1                           # the next source (a variable: the int note)
        # Math: ∀ i ∈ [0,|ps|). ∀ z < nx. i ∈ block(z) → ps[i] ∈ [0,|rs|) ∧ rs[ps[i]] = z
        # Why (hint): z < x is the old part; z = x: i ∈ block(x) means i < start[x+1] = k.
        Assert(Forall(int, lambda i: (Implies(
            0 <= i and i < len(ToSeq(pos)),
            Forall(int, lambda z: (Implies(in_blk(ToSeq(start), z, i) and z < nx,
                                           0 <= ToSeq(pos)[i] and ToSeq(pos)[i] < len(ToSeq(rsrc))
                                           and ToSeq(rsrc)[ToSeq(pos)[i]] == z),
                                   [[in_blk(ToSeq(start), z, i)]]))),
            [[ToSeq(pos)[i]]])))
        x = nx
    # Math: own_ok(st, rs, ps)
    # Why (hint): at x = n every block counts (in_blk(st, z, k) gives z + 1 < n + 1).
    Assert(own_ok(ToSeq(start), ToSeq(rsrc), ToSeq(pos)))
    return True


# --- the whole check -------------------------------------------------------------------------


# check_reverse: accepts the reverse index only if all four facts hold and rstart is a valid
# block structure over the T reverse positions. Called by the trusted builder
# (core_aut/trusted/reverse_index.py) before a ValidAutomaton keeps the index.
def check_reverse(n: int, start: List[int], dst: List[int], rstart: List[int], rk: List[int],
                  rsrc: List[int], pos: List[int]) -> bool:
    """True only if (rstart, rk, rsrc, pos) is a correct reverse index of (start, dst)."""
    # Why: read access.
    Requires(Acc(list_pred(start), 1 / 2) and Acc(list_pred(dst), 1 / 2)
             and Acc(list_pred(rstart), 1 / 2) and Acc(list_pred(rk), 1 / 2)
             and Acc(list_pred(rsrc), 1 / 2) and Acc(list_pred(pos), 1 / 2))
    # Math: termination measure 4.
    # Why: calls the checkers (measures 2 and 3).
    Requires(MustTerminate(4))
    # Math: blocks_ok(n, start, T) ∧ ∀ k ∈ [0,T): dst[k] ∈ [0,n)
    # Why: a validated automaton (check_automaton proves both).
    Requires(blocks_ok(n, start, len(dst)))
    Requires(Forall(int, lambda k: (Implies(0 <= k and k < len(dst),
                                            0 <= dst[k] and dst[k] < n), [[dst[k]]])))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 2) and Acc(list_pred(dst), 1 / 2)
            and Acc(list_pred(rstart), 1 / 2) and Acc(list_pred(rk), 1 / 2)
            and Acc(list_pred(rsrc), 1 / 2) and Acc(list_pred(pos), 1 / 2))
    # Math: Result → blocks_ok(n, rstart, |rsrc|) ∧ |rk| = |rsrc| = |pos| = T
    # Why: rstart splits the reverse positions into one block per state (the reversed search
    #      needs it, stated with |rsrc|: the "dst" of the reversed automaton).
    Ensures(Implies(Result(), blocks_ok(n, rstart, len(rsrc)) and len(rk) == len(dst)
                    and len(rsrc) == len(dst) and len(pos) == len(dst)))
    # Math: Result → src_ok ∧ tgt_ok ∧ pos_ok ∧ own_ok
    # Why: the four facts; coreachable translates the reversed search with them.
    Ensures(Implies(Result(), src_ok(n, ToSeq(start), len(dst), ToSeq(rk), ToSeq(rsrc))
                    and tgt_ok(ToSeq(rstart), ToSeq(dst), ToSeq(rk))
                    and pos_ok(ToSeq(rstart), ToSeq(dst), ToSeq(rk), ToSeq(pos))
                    and own_ok(ToSeq(start), ToSeq(rsrc), ToSeq(pos))))
    T = len(dst)                             # the number of transitions
    if len(rk) != T or len(rsrc) != T or len(pos) != T:   # Math: the lengths, else reject
        return False
    if not check_blocks(n, rstart, T):       # Math: blocks_ok(n, rstart, T), else reject
        return False
    if not check_src(n, start, T, rk, rsrc):     # Math: src_ok, else reject
        return False
    if not check_tgt(n, dst, rstart, rk):    # Math: tgt_ok, else reject
        return False
    if not check_pos(n, dst, rstart, rk, pos):   # Math: pos_ok, else reject
        return False
    if not check_own(n, start, rsrc, pos):   # Math: own_ok, else reject
        return False
    # Math: blocks_ok(n, rstart, |rsrc|)
    # Why (hint): the same as blocks_ok(n, rstart, T) with |rsrc| = T (written with |rsrc|,
    #      a different term for the same number).
    Assert(blocks_ok(n, rstart, len(rsrc)))
    return True
