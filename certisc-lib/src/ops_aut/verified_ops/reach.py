"""
Verified reachability on an encoded automaton (certisc-proof/spec/reach.md).

- reachable  the states reachable from a list of start states S (Lean: `reach f S`), each once,
             with witnesses: each reached state has a parent and a transition (breadth-first).

Encoding as in core_aut/verified_core/check.py: states 0 .. n-1; state x owns the transition
positions block(x) = [start[x], start[x+1]) of dst. Events are not read: reachability follows
every transition (the event of transition k is evt[k], so a witness also gives the event).

Verify, from certisc-lib/ (Python >= 3.12, `verify` extra, Java):

    nagini src/ops_aut/verified_ops/reach.py

Math notation used in the comments:
    [a, b)       the integers a, a+1, ..., b-1
    |l|          the length of list (or sequence) l
    T            |dst|, the number of transitions
    block(x)     [start[x], start[x+1]), the positions of the transitions of state x
    mk           the marks, as a sequence: mk[y] = position of y in out, or -1 (not reached)
    o, p, v      out, par, via, as sequences
    l_old        the value of l when the method was called (Old(...))

How to read the contracts (all removed before the code runs; core_aut/trusted/_strip.py):
- Requires(P) / Ensures(P)   precondition (the caller makes P true) / postcondition.
- Invariant(P)               loop invariant: true before the loop and kept by each iteration.
- Assert(P)                  a proof step, checked by Nagini. "Why (hint)": a fact Nagini can
                             prove but would not find by itself.
- Acc(list_pred(l), q)       permission to use list l: q = 1 read and write; q < 1 read only.
                             A caller that passes only part of its share knows the list is
                             unchanged after the call.
- MustTerminate(t)           the method (loop) terminates; t goes down; a method only calls
                             methods with a smaller t.
- Decreases(t)               the same, for a recursive @Pure function.
- ToSeq(l)                   the contents of list l as a value (a sequence).
- Old(e)                     e when the method was called.
- Forall(int, lambda i: (P, [[t]]))   ∀ i ∈ ℤ: P; Nagini uses it for an i where the term t
                             appears (the trigger).
- @Pure                      a side-effect-free function, usable in contracts (a definition).
- Lemma                      a method that only proves a fact (no runtime effect; its calls are
                             removed before running). A recursive lemma is a proof by induction.

Note on ints: Nagini treats ints as objects, so from i == j it does not conclude f(i) == f(j)
for a function f (list reads do compare by value). Lemmas therefore take the exact variables
their callers use later (e.g. K, nh), never a recomputed expression.
"""

from typing import List

from nagini_contracts.contracts import *
from nagini_contracts.obligations import MustTerminate

# The well-formedness of the blocks, from the verified validity checker (needs core_aut/py.typed).
from core_aut.verified_core.check import blocks_ok


# --- specification ---------------------------------------------------------------------------
# Definitions used in the contracts. They say what "correct" means; they run no code.


@Pure
def targets_ok(n: int, dst: List[int]) -> bool:
    """Every transition goes to a state."""
    # Why: read access.
    Requires(Acc(list_pred(dst), 1 / 8))
    # Math: ∀ k ∈ [0,T): dst[k] ∈ [0,n)
    # Why: part of transitions_ok (check_automaton); so marks can be indexed by targets.
    return Forall(int, lambda k: (Implies(0 <= k and k < len(dst),
                                          0 <= dst[k] and dst[k] < n), [[dst[k]]]))


@Pure
def in_blk(st: PSeq[int], x: int, k: int) -> bool:
    """Position k is a transition of the state x (st = ToSeq(start))."""
    # Math: x ∈ [0,|start|-1) ∧ k ∈ block(x)
    # Why: the bounds first, so start[x], start[x+1] are valid reads.
    return 0 <= x and x + 1 < len(st) and st[x] <= k and k < st[x + 1]


@Pure
def marks_ok(mk: PSeq[int], o: PSeq[int]) -> bool:
    """mark and out agree: o[i] is marked with its position i, and each marked y is the entry of
    o at its mark. Hence no duplicates in o (as in basic_ops.active_events)."""
    # Math (1): ∀ i ∈ [0,|o|): o[i] ∈ [0,|mk|) ∧ mk[o[i]] = i
    # Why: in range, and o[i] = o[i'] gives i = mk[o[i]] = i': no duplicates.
    return (Forall(int, lambda i: (Implies(0 <= i and i < len(o),
                                           0 <= o[i] and o[i] < len(mk) and mk[o[i]] == i),
                                   [[o[i]]]))
            # Math (2): ∀ y ∈ [0,|mk|): mk[y] ≠ -1 → mk[y] ∈ [0,|o|) ∧ o[mk[y]] = y
            # Why: "y is marked" ⟹ "y is in out" (at position mk[y]).
            and Forall(int, lambda y: (Implies(0 <= y and y < len(mk) and mk[y] != -1,
                                               0 <= mk[y] and mk[y] < len(o) and o[mk[y]] == y),
                                       [[mk[y]]])))


@Pure
def nmarked(mk: PSeq[int], i: int) -> int:
    """The number of marked states among 0 .. i-1."""
    # Math: 0 ≤ i ≤ |mk|
    Requires(0 <= i and i <= len(mk))
    # Math: termination measure i (the recursion goes down to 0).
    Decreases(i)
    # Math: nmarked(mk, 0) = 0;  nmarked(mk, i) = nmarked(mk, i-1) + [mk[i-1] ≠ -1]
    # Why: counting gives |out| ≤ n (no two entries of out are equal), which bounds the loop.
    if i == 0:
        return 0
    if mk[i - 1] == -1:
        return nmarked(mk, i - 1)
    return nmarked(mk, i - 1) + 1


# The witness and start-state predicates take sequences (ToSeq(S), ToSeq(start), ToSeq(dst)),
# not lists: they are then plain functions of values, and their bodies compare entries by value.


@Pure
def wit_init(Sq: PSeq[int], j: int, y: int) -> bool:
    """y is the start state S[j]."""
    # Math: j ∈ [0,|S|) ∧ S[j] = y
    return 0 <= j and j < len(Sq) and Sq[j] == y


@Pure
def wit_step(st: PSeq[int], ds: PSeq[int], x: int, k: int, y: int) -> bool:
    """Transition k goes from x to y."""
    # Math: x ∈ [0,|start|-1) ∧ k ∈ block(x) ∧ k ∈ [0,T) ∧ dst[k] = y      (x --evt[k]-->_k y)
    return (0 <= x and x + 1 < len(st) and st[x] <= k and k < st[x + 1]
            and 0 <= k and k < len(ds) and ds[k] == y)


@Pure
def wit_ok(st: PSeq[int], ds: PSeq[int], Sq: PSeq[int], o: PSeq[int], p: PSeq[int],
           v: PSeq[int]) -> bool:
    """Each entry of out is a start state, or is reached by a transition from an earlier entry."""
    # Math: |p| = |o| ∧ |v| = |o|
    Requires(len(p) == len(o) and len(v) == len(o))
    # Math: ∀ i ∈ [0,|o|): (p[i] = -1 → S[v[i]] = o[i])
    #                     ∧ (p[i] ≠ -1 → 0 ≤ p[i] < i ∧ o[p[i]] --evt[v[i]]-->_{v[i]} o[i])
    # Why: the witnesses of lemma R2 (Lean: mem_reach_of_witness), stored, so no "∃" is needed.
    #      Written out (not with wit_init / wit_step), so entries compare by value. Trigger v[i],
    #      not o[i]: the body reads o at p[i], and an o-trigger would chain along the parents
    #      (o[p[i]], o[p[p[i]]], ...), a matching loop.
    return Forall(int, lambda i: (Implies(
        0 <= i and i < len(o),
        Implies(p[i] == -1, 0 <= v[i] and v[i] < len(Sq) and Sq[v[i]] == o[i])
        and Implies(p[i] != -1,
                    0 <= p[i] and p[i] < i and 0 <= o[p[i]] and o[p[i]] + 1 < len(st)
                    and st[o[p[i]]] <= v[i] and v[i] < st[o[p[i]] + 1]
                    and 0 <= v[i] and v[i] < len(ds) and ds[v[i]] == o[i])),
        [[v[i]]]))


@Pure
def contains_S(Sq: PSeq[int], mk: PSeq[int], J: int) -> bool:
    """The start states S[0 .. J-1] are marked."""
    # Math: ∀ j ∈ [0, min(J,|S|)): S[j] ∈ [0,|mk|) ∧ mk[S[j]] ≥ 0
    # Why: with J = |S|: "out contains S" (by marks_ok, a marked state is in out).
    return Forall(int, lambda j: (Implies(0 <= j and j < J and j < len(Sq),
                                          0 <= Sq[j] and Sq[j] < len(mk) and mk[Sq[j]] >= 0),
                                  [[Sq[j]]]))


@Pure
def closed_upto(st: PSeq[int], ds: PSeq[int], mk: PSeq[int], h: int, K: int) -> bool:
    """Every transition of a state at a position < h of out, or of the state at position h
    before K, goes to a marked state."""
    # Math: ∀ k ∈ [0,T). ∀ x. k ∈ block(x) ∧ x < |mk| ∧ (mk[x] ∈ [0,h) ∨ (mk[x] = h ∧ k < K))
    #                          → dst[k] ∈ [0,|mk|) ∧ mk[dst[k]] ≥ 0
    # Why: "the loop has followed transition k" ⟹ "its target is marked". A state's mark is its
    #      position in out, so mk[x] < h means "x was already processed".
    return Forall(int, lambda k: (Implies(
        0 <= k and k < len(ds),
        Forall(int, lambda x: (Implies(
            in_blk(st, x, k) and x < len(mk)
            and ((0 <= mk[x] and mk[x] < h) or (mk[x] == h and k < K)),
            0 <= ds[k] and ds[k] < len(mk) and mk[ds[k]] >= 0),
            [[in_blk(st, x, k)]]))),
        [[ds[k]]]))


@Pure
def closed_all(st: PSeq[int], ds: PSeq[int], mk: PSeq[int]) -> bool:
    """Every transition of a marked state goes to a marked state."""
    # Math: ∀ k ∈ [0,T). ∀ x. k ∈ block(x) ∧ x < |mk| ∧ mk[x] ≥ 0 → dst[k] ∈ [0,|mk|) ∧ mk[dst[k]] ≥ 0
    # Why: "closed" of lemma R1 (Lean: reach_subset_of_closed), for R = the marked states.
    return Forall(int, lambda k: (Implies(
        0 <= k and k < len(ds),
        Forall(int, lambda x: (Implies(
            in_blk(st, x, k) and x < len(mk) and mk[x] >= 0,
            0 <= ds[k] and ds[k] < len(mk) and mk[ds[k]] >= 0),
            [[in_blk(st, x, k)]]))),
        [[ds[k]]]))


# --- lemmas ----------------------------------------------------------------------------------
# Methods with no runtime effect: each proves one small fact in a small context.


def count_clear(mk: PSeq[int], i: int) -> None:
    """Lemma: with nothing marked, the count is 0 (induction on i)."""
    # Math: termination measure i + 1 (the recursive call has measure i).
    Requires(MustTerminate(i + 1))
    # Math: 0 ≤ i ≤ |mk| ∧ ∀ y ∈ [0,|mk|): mk[y] = -1
    Requires(0 <= i and i <= len(mk))
    Requires(Forall(int, lambda y: (Implies(0 <= y and y < len(mk), mk[y] == -1), [[mk[y]]])))
    # Math: nmarked(mk, i) = 0
    Ensures(nmarked(mk, i) == 0)
    if i > 0:
        count_clear(mk, i - 1)          # induction hypothesis: nmarked(mk, i-1) = 0


def count_mark(a: PSeq[int], b: PSeq[int], y: int, i: int) -> None:
    """Lemma: marking one more state y (a → b) adds one to the count (induction on i)."""
    # Math: termination measure i + 1.
    Requires(MustTerminate(i + 1))
    # Math: |a| = |b| ∧ 0 ≤ i ≤ |a| ∧ y ∈ [0,|a|) ∧ a[y] = -1 ∧ b[y] ≠ -1
    Requires(len(a) == len(b) and 0 <= i and i <= len(a) and 0 <= y and y < len(a))
    Requires(a[y] == -1 and b[y] != -1)
    # Math: ∀ z ∈ [0,|a|), z ≠ y: b[z] = a[z]
    # Why: b is a with only y changed.
    Requires(Forall(int, lambda z: (Implies(0 <= z and z < len(a) and z != y, b[z] == a[z]),
                                    [[b[z]]])))
    # Math: i ≤ y → nmarked(b, i) = nmarked(a, i) ≤ i
    Ensures(Implies(i <= y, nmarked(b, i) == nmarked(a, i) and nmarked(a, i) <= i))
    # Math: y < i → nmarked(b, i) = nmarked(a, i) + 1 ≤ i
    # Why: with i = n: one more marked state, and at most n of them.
    Ensures(Implies(y < i, nmarked(b, i) == nmarked(a, i) + 1 and nmarked(b, i) <= i))
    if i > 0:
        count_mark(a, b, y, i - 1)      # induction hypothesis at i - 1


def block_range(n: int, start: List[int], dst: List[int], x: int) -> None:
    """Lemma: the block of a state is a valid range of positions."""
    # Why: read access (1/8: the caller keeps a share).
    Requires(Acc(list_pred(start), 1 / 8) and Acc(list_pred(dst), 1 / 8))
    # Math: termination measure 1.
    Requires(MustTerminate(1))
    # Math: blocks_ok(n, start, T) ∧ x ∈ [0,n)
    Requires(blocks_ok(n, start, len(dst)) and 0 <= x and x < n)
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 8) and Acc(list_pred(dst), 1 / 8))
    # Math: |start| = n+1 ∧ 0 ≤ start[x] ≤ start[x+1] ≤ T
    Ensures(len(start) == n + 1 and 0 <= start[x] and start[x] <= start[x + 1]
            and start[x + 1] <= len(dst))
    # Math: start[x+1] ≤ T
    # Why (hint): mentioning start[x + 1] triggers blocks_ok's quantifier at x.
    Assert(start[x + 1] <= len(dst))


def contains_all(Sq: PSeq[int], mk: PSeq[int], J: int, L: int) -> None:
    """Lemma: contains_S up to J is contains_S up to L when J = L = |S| (different terms for the
    same number: Nagini compares ints as objects inside function arguments)."""
    # Math: termination measure 1.
    Requires(MustTerminate(1))
    # Math: J = L = |S| ∧ contains_S(mk, J)
    Requires(J == L and L == len(Sq) and contains_S(Sq, mk, J))
    # Math: contains_S(mk, L)
    Ensures(contains_S(Sq, mk, L))
    # Math: the body of contains_S(mk, L).
    # Why (hint): written out; the bounds compare by value.
    Assert(Forall(int, lambda j: (Implies(0 <= j and j < L and j < len(Sq),
                                          0 <= Sq[j] and Sq[j] < len(mk)
                                          and mk[Sq[j]] >= 0),
                                  [[Sq[j]]])))


def closed_enter(st: PSeq[int], ds: PSeq[int], mk: PSeq[int], o: PSeq[int], h: int,
                 x: int, K: int) -> None:
    """Lemma: positions before block(x) are not x's, so (h, 0) covers as much as (h, start[x]),
    when x = o[h] is the only state with mark h."""
    # Math: termination measure 1.
    Requires(MustTerminate(1))
    # Math: marks_ok(mk, o) ∧ h ∈ [0,|o|) ∧ o[h] = x ∧ x ∈ [0,|start|-1) ∧ K = start[x]
    Requires(marks_ok(mk, o) and 0 <= h and h < len(o) and o[h] == x
             and 0 <= x and x + 1 < len(st) and K == st[x])
    # Math: closed_upto(mk, h, 0)
    Requires(closed_upto(st, ds, mk, h, 0))
    # Math: closed_upto(mk, h, K)
    Ensures(closed_upto(st, ds, mk, h, K))
    # Math: ∀ z ∈ [0,|mk|): mk[z] = h → z = x
    # Why (hint): marks_ok (2): o[mk[z]] = z, so o[h] = z, and o[h] = x.
    Assert(Forall(int, lambda z: (Implies(0 <= z and z < len(mk) and mk[z] == h, z == x),
                                  [[mk[z]]])))
    # Math: the body of closed_upto(mk, h, K).
    # Why (hint): a position k < K = start[x] with mark h would be in block(x), impossible.
    Assert(Forall(int, lambda k: (Implies(
        0 <= k and k < len(ds),
        Forall(int, lambda z: (Implies(
            in_blk(st, z, k) and z < len(mk)
            and ((0 <= mk[z] and mk[z] < h) or (mk[z] == h and k < K)),
            0 <= ds[k] and ds[k] < len(mk) and mk[ds[k]] >= 0),
            [[in_blk(st, z, k)]]))),
        [[ds[k]]])))


def closed_step(st: PSeq[int], ds: PSeq[int], mk: PSeq[int], h: int, k: int,
                nk: int) -> None:
    """Lemma: once the target of transition k is marked, (h, k) extends to (h, k+1)."""
    # Math: termination measure 1.
    Requires(MustTerminate(1))
    # Math: nk = k+1 ∧ k ∈ [0,T) ∧ dst[k] ∈ [0,|mk|) ∧ mk[dst[k]] ≥ 0 ∧ closed_upto(mk, h, k)
    Requires(nk == k + 1 and 0 <= k and k < len(ds) and 0 <= ds[k] and ds[k] < len(mk)
             and mk[ds[k]] >= 0 and closed_upto(st, ds, mk, h, k))
    # Math: closed_upto(mk, h, nk)
    Ensures(closed_upto(st, ds, mk, h, nk))
    # Math: the body of closed_upto(mk, h, nk).
    # Why (hint): the only new position is k, whose target is marked.
    Assert(Forall(int, lambda kk: (Implies(
        0 <= kk and kk < len(ds),
        Forall(int, lambda z: (Implies(
            in_blk(st, z, kk) and z < len(mk)
            and ((0 <= mk[z] and mk[z] < h) or (mk[z] == h and kk < nk)),
            0 <= ds[kk] and ds[kk] < len(mk) and mk[ds[kk]] >= 0),
            [[in_blk(st, z, kk)]]))),
        [[ds[kk]]])))


def closed_next(st: PSeq[int], ds: PSeq[int], mk: PSeq[int], o: PSeq[int], h: int,
                x: int, K: int, nh: int) -> None:
    """Lemma: once the whole block of x = o[h] is followed, move on to h + 1."""
    # Math: termination measure 1.
    Requires(MustTerminate(1))
    # Math: marks_ok(mk, o) ∧ h ∈ [0,|o|) ∧ o[h] = x ∧ x ∈ [0,|start|-1) ∧ K = start[x+1]
    #       ∧ nh = h+1
    Requires(marks_ok(mk, o) and 0 <= h and h < len(o) and o[h] == x
             and 0 <= x and x + 1 < len(st) and K == st[x + 1] and nh == h + 1)
    # Math: closed_upto(mk, h, K)
    Requires(closed_upto(st, ds, mk, h, K))
    # Math: closed_upto(mk, nh, 0)
    Ensures(closed_upto(st, ds, mk, nh, 0))
    # Math: ∀ z ∈ [0,|mk|): mk[z] = h → z = x
    # Why (hint): marks_ok (2), as in closed_enter.
    Assert(Forall(int, lambda z: (Implies(0 <= z and z < len(mk) and mk[z] == h, z == x),
                                  [[mk[z]]])))
    # Math: the body of closed_upto(mk, nh, 0).
    # Why (hint): mark h is x, and all of block(x) (positions < K) is followed.
    Assert(Forall(int, lambda k: (Implies(
        0 <= k and k < len(ds),
        Forall(int, lambda z: (Implies(
            in_blk(st, z, k) and z < len(mk)
            and ((0 <= mk[z] and mk[z] < nh) or (mk[z] == nh and k < 0)),
            0 <= ds[k] and ds[k] < len(mk) and mk[ds[k]] >= 0),
            [[in_blk(st, z, k)]]))),
        [[ds[k]]])))


def closed_final(st: PSeq[int], ds: PSeq[int], mk: PSeq[int], o: PSeq[int],
                 h: int) -> None:
    """Lemma: when every entry of out is processed (h = |o|), every marked state is closed."""
    # Math: termination measure 1.
    Requires(MustTerminate(1))
    # Math: marks_ok(mk, o) ∧ h = |o| ∧ closed_upto(mk, h, 0)
    Requires(marks_ok(mk, o) and h == len(o) and closed_upto(st, ds, mk, h, 0))
    # Math: closed_all(mk)
    Ensures(closed_all(st, ds, mk))
    # Math: ∀ z ∈ [0,|mk|): mk[z] ≥ 0 → mk[z] < h
    # Why (hint): marks_ok (2): a mark is a position in o, and h = |o|.
    Assert(Forall(int, lambda z: (Implies(0 <= z and z < len(mk) and mk[z] >= 0, mk[z] < h),
                                  [[mk[z]]])))
    # Math: the body of closed_all(mk).
    Assert(Forall(int, lambda k: (Implies(
        0 <= k and k < len(ds),
        Forall(int, lambda z: (Implies(
            in_blk(st, z, k) and z < len(mk) and mk[z] >= 0,
            0 <= ds[k] and ds[k] < len(mk) and mk[ds[k]] >= 0),
            [[in_blk(st, z, k)]]))),
        [[ds[k]]])))


# --- the update of add_state ----------------------------------------------------------------
# add_state appends y to out (o0 → o) and marks it (mk0 → mk). Each lemma below carries one
# invariant across that update. The update itself is described by `appended` and `marked`.


@Pure
def appended(o0: PSeq[int], o: PSeq[int], y: int) -> bool:
    """o is o0 with y appended."""
    # Math: |o| = |o0| + 1 ∧ ∀ t ∈ [0,|o0|): o[t] = o0[t] ∧ o[|o0|] = y
    return (len(o) == len(o0) + 1
            and Forall(int, lambda t: (Implies(0 <= t and t < len(o0), o[t] == o0[t]), [[o[t]]]))
            and o[len(o0)] == y)


@Pure
def marked(mk0: PSeq[int], mk: PSeq[int], y: int, i: int) -> bool:
    """mk is mk0 with the unmarked y now marked i."""
    # Math: |mk| = |mk0| ∧ y ∈ [0,|mk|) ∧ mk0[y] = -1 ∧ mk[y] = i ∧ ∀ z ≠ y: mk[z] = mk0[z]
    return (len(mk) == len(mk0) and 0 <= y and y < len(mk) and mk0[y] == -1 and mk[y] == i
            and Forall(int, lambda z: (Implies(0 <= z and z < len(mk) and z != y,
                                               mk[z] == mk0[z]), [[mk[z]]])))


def keep_marks(mk0: PSeq[int], o0: PSeq[int], mk: PSeq[int], o: PSeq[int], y: int) -> None:
    """Lemma: marks_ok survives the update (y gets mark |o0|, its position in o)."""
    # Math: termination measure 1.
    Requires(MustTerminate(1))
    # Math: marks_ok(mk0, o0) ∧ appended(o0, o, y) ∧ marked(mk0, mk, y, |o0|)
    Requires(marks_ok(mk0, o0) and appended(o0, o, y) and marked(mk0, mk, y, len(o0)))
    # Math: marks_ok(mk, o)
    Ensures(marks_ok(mk, o))
    # Math: ∀ t ∈ [0,|o|): o[t] ∈ [0,|mk|) ∧ mk[o[t]] = t                      (part 1)
    # Why (hint): old entries keep their marks (o[t] ≠ y, as y was unmarked); the new one is y.
    Assert(Forall(int, lambda t: (Implies(0 <= t and t < len(o),
                                          0 <= o[t] and o[t] < len(mk) and mk[o[t]] == t),
                                  [[o[t]]])))
    # Math: ∀ z ∈ [0,|mk|): mk[z] ≠ -1 → mk[z] ∈ [0,|o|) ∧ o[mk[z]] = z          (part 2)
    Assert(Forall(int, lambda z: (Implies(0 <= z and z < len(mk) and mk[z] != -1,
                                          0 <= mk[z] and mk[z] < len(o) and o[mk[z]] == z),
                                  [[mk[z]]])))


def keep_wit(st: PSeq[int], ds: PSeq[int], Sq: PSeq[int], o0: PSeq[int], p0: PSeq[int],
             v0: PSeq[int], o: PSeq[int], p: PSeq[int], v: PSeq[int], y: int, pp: int,
             vv: int) -> None:
    """Lemma: wit_ok survives the update, given the new entry's witness (pp, vv)."""
    # Math: termination measure 1.
    Requires(MustTerminate(1))
    # Math: |p0| = |v0| = |o0| ∧ wit_ok(o0, p0, v0)
    Requires(len(p0) == len(o0) and len(v0) == len(o0) and wit_ok(st, ds, Sq, o0, p0, v0))
    # Math: appended(o0, o, y) ∧ appended(p0, p, pp) ∧ appended(v0, v, vv)
    Requires(appended(o0, o, y) and appended(p0, p, pp) and appended(v0, v, vv))
    # Math: (pp = -1 ∧ S[vv] = y) ∨ (pp ∈ [0,|o0|) ∧ o0[pp] --_vv--> y)
    Requires((pp == -1 and wit_init(Sq, vv, y))
             or (0 <= pp and pp < len(o0) and wit_step(st, ds, o0[pp], vv, y)))
    # Math: |p| = |v| = |o| ∧ wit_ok(o, p, v)
    Ensures(len(p) == len(o) and len(v) == len(o) and wit_ok(st, ds, Sq, o, p, v))
    # Math: o[pp] = o0[pp] when pp ∈ [0,|o0|)
    # Why (hint): the parent is an old entry, unchanged by the append.
    Assert(Implies(0 <= pp and pp < len(o0), o[pp] == o0[pp]))
    # Math: the new entry's witness, in terms of o: (pp = -1 ∧ S[vv] = y) ∨ (0 ≤ pp < |o0| ∧ o[pp] --_vv--> y)
    Assert((pp == -1 and wit_init(Sq, vv, y))
           or (0 <= pp and pp < len(o0) and wit_step(st, ds, o[pp], vv, y)))
    # Math: the body of wit_ok(o, p, v).
    # Why (hint): old entries keep their witnesses (o[p[t]] = o0[p0[t]], as p[t] < t < |o0|).
    Assert(Forall(int, lambda t: (Implies(
        0 <= t and t < len(o),
        Implies(p[t] == -1, 0 <= v[t] and v[t] < len(Sq) and Sq[v[t]] == o[t])
        and Implies(p[t] != -1,
                    0 <= p[t] and p[t] < t and 0 <= o[p[t]] and o[p[t]] + 1 < len(st)
                    and st[o[p[t]]] <= v[t] and v[t] < st[o[p[t]] + 1]
                    and 0 <= v[t] and v[t] < len(ds) and ds[v[t]] == o[t])),
        [[v[t]]])))


def keep_contains(Sq: PSeq[int], mk0: PSeq[int], mk: PSeq[int], y: int, i: int, J: int) -> None:
    """Lemma: contains_S survives the update (marks only go from -1 to a position)."""
    # Math: termination measure 1.
    Requires(MustTerminate(1))
    # Math: contains_S(mk0, J) ∧ marked(mk0, mk, y, i) ∧ i ≥ 0
    Requires(contains_S(Sq, mk0, J) and marked(mk0, mk, y, i) and i >= 0)
    # Math: contains_S(mk, J)
    Ensures(contains_S(Sq, mk, J))
    # Math: the body of contains_S(mk, J).
    Assert(Forall(int, lambda j: (Implies(0 <= j and j < J and j < len(Sq),
                                          0 <= Sq[j] and Sq[j] < len(mk)
                                          and mk[Sq[j]] >= 0),
                                  [[Sq[j]]])))


def keep_closed(st: PSeq[int], ds: PSeq[int], mk0: PSeq[int], mk: PSeq[int], y: int,
                i: int, h: int, K: int) -> None:
    """Lemma: closed_upto survives the update: the new mark i is not processed."""
    # Math: termination measure 1.
    Requires(MustTerminate(1))
    # Math: closed_upto(mk0, h, K) ∧ marked(mk0, mk, y, i) ∧ 0 ≤ h ≤ i ∧ (h < i ∨ K ≤ 0)
    # Why: i ≥ h, and i = h only before any position of out[h] is followed.
    Requires(closed_upto(st, ds, mk0, h, K) and marked(mk0, mk, y, i))
    Requires(0 <= h and h <= i and (h < i or K <= 0))
    # Math: closed_upto(mk, h, K)
    Ensures(closed_upto(st, ds, mk, h, K))
    # Math: the body of closed_upto(mk, h, K).
    # Why (hint): a state other than y kept its mark; y's mark i is neither < h nor (= h with a
    #      followed position); targets marked before are still marked.
    Assert(Forall(int, lambda k: (Implies(
        0 <= k and k < len(ds),
        Forall(int, lambda z: (Implies(
            in_blk(st, z, k) and z < len(mk)
            and ((0 <= mk[z] and mk[z] < h) or (mk[z] == h and k < K)),
            0 <= ds[k] and ds[k] < len(mk) and mk[ds[k]] >= 0),
            [[in_blk(st, z, k)]]))),
        [[ds[k]]])))


# --- one new state ---------------------------------------------------------------------------


def add_state(n: int, st: PSeq[int], ds: PSeq[int], Sq: PSeq[int], mark: List[int],
              out: List[int], par: List[int], via: List[int], y: int, p: int, v: int,
              J: int, h: int, K: int) -> None:
    """Add the unmarked state y to out, with its witness (p, v): p = -1 and y = S[v] (a start
    state), or y is the target of transition v of the state out[p].

    st, ds, Sq are ToSeq(start), ToSeq(dst), ToSeq(S): the inputs as values, used only in the
    contracts (at runtime ToSeq returns None and they are not read). Passing values, not the
    lists, keeps the inputs framed: Nagini cannot rule out that two list arguments are the same
    list, so after the appends it would no longer know the input lists unchanged."""
    # Why: write access to mark and the three outputs.
    Requires(Acc(list_pred(mark)) and Acc(list_pred(out)) and Acc(list_pred(par))
             and Acc(list_pred(via)))
    # Math: termination measure n + 3 (calls count_mark, measure n + 1, the update lemmas and
    #       append).
    Requires(MustTerminate(n + 3))
    # Math: |mark| = n ∧ |start| = n+1 ∧ |par| = |via| = |out|
    Requires(len(mark) == n and len(st) == n + 1 and len(par) == len(out)
             and len(via) == len(out))
    # Math: y ∈ [0,n) ∧ mk[y] = -1
    # Why: y is a state, not reached yet.
    Requires(0 <= y and y < n and ToSeq(mark)[y] == -1)
    # Math: marks_ok(mk, o) ∧ |o| = nmarked(mk, n) ∧ wit_ok(o, p, v)
    # Why: the invariants of the caller's loops.
    Requires(marks_ok(ToSeq(mark), ToSeq(out)) and len(out) == nmarked(ToSeq(mark), n))
    Requires(wit_ok(st, ds, Sq, ToSeq(out), ToSeq(par), ToSeq(via)))
    # Math: (p = -1 ∧ S[v] = y) ∨ (p ∈ [0,|o|) ∧ o[p] --_v--> y)
    # Why: the witness of the new entry.
    Requires((p == -1 and wit_init(Sq, v, y))
             or (0 <= p and p < len(out) and wit_step(st, ds, ToSeq(out)[p], v, y)))
    # Math: contains_S(mk, J) ∧ 0 ≤ h ≤ |o| ∧ (h < |o| ∨ K ≤ 0) ∧ closed_upto(mk, h, K)
    # Why: also invariants of the caller; the new mark |o| is not "processed" (not < h, and
    #      equal to h only when no position is followed yet, K ≤ 0).
    Requires(contains_S(Sq, ToSeq(mark), J))
    Requires(0 <= h and h <= len(out) and (h < len(out) or K <= 0)
             and closed_upto(st, ds, ToSeq(mark), h, K))
    Ensures(Acc(list_pred(mark)) and Acc(list_pred(out)) and Acc(list_pred(par))
            and Acc(list_pred(via)))
    # Math: sizes; |o| = |o_old| + 1 ≤ n; mk[y] = |o_old|
    Ensures(len(mark) == n and len(par) == len(out) and len(via) == len(out)
            and len(out) == Old(len(out)) + 1 and len(out) <= n)
    Ensures(ToSeq(mark)[y] == Old(len(out)))
    # Math: ∀ z ∈ [0,n), z ≠ y: mk[z] = mk_old[z]
    # Why: only y's mark changed (the caller's facts about other states remain).
    Ensures(Forall(int, lambda z: (Implies(0 <= z and z < n and z != y,
                                           ToSeq(mark)[z] == Old(ToSeq(mark))[z]),
                                   [[ToSeq(mark)[z]]])))
    # Math: ∀ t ∈ [0,|o_old|): o[t] = o_old[t]
    # Why: the old entries of out stay (the caller reads out[h]).
    Ensures(Forall(int, lambda t: (Implies(0 <= t and t < Old(len(out)),
                                           ToSeq(out)[t] == Old(ToSeq(out))[t]),
                                   [[ToSeq(out)[t]]])))
    # Math: the invariants hold again.
    Ensures(marks_ok(ToSeq(mark), ToSeq(out)) and len(out) == nmarked(ToSeq(mark), n))
    Ensures(wit_ok(st, ds, Sq, ToSeq(out), ToSeq(par), ToSeq(via)))
    Ensures(contains_S(Sq, ToSeq(mark), J))
    Ensures(closed_upto(st, ds, ToSeq(mark), h, K))
    i = len(out)                     # the position y will have
    out.append(y)                    # add y ...
    par.append(p)                    # ... with its parent's position (or -1) ...
    via.append(v)                    # ... and the transition (or the index in S)
    mark[y] = i                      # remember y's position
    # Math: appended(o_old, o, y) ∧ appended(p_old, p, pp) ∧ appended(v_old, v, vv)
    # Why (hint): the three appends, as one fact each (the update lemmas use them).
    Assert(appended(Old(ToSeq(out)), ToSeq(out), y) and appended(Old(ToSeq(par)), ToSeq(par), p)
           and appended(Old(ToSeq(via)), ToSeq(via), v))
    # Math: marked(mk_old, mk, y, i)
    # Why (hint): the write changed only mark[y], from -1 to i.
    Assert(marked(Old(ToSeq(mark)), ToSeq(mark), y, i))
    count_mark(Old(ToSeq(mark)), ToSeq(mark), y, n)                       # |o| = nmarked ≤ n
    keep_marks(Old(ToSeq(mark)), Old(ToSeq(out)), ToSeq(mark), ToSeq(out), y)   # marks_ok
    keep_wit(st, ds, Sq, Old(ToSeq(out)), Old(ToSeq(par)), Old(ToSeq(via)),
             ToSeq(out), ToSeq(par), ToSeq(via), y, p, v)                     # wit_ok
    keep_contains(Sq, Old(ToSeq(mark)), ToSeq(mark), y, i, J)                 # contains_S
    keep_closed(st, ds, Old(ToSeq(mark)), ToSeq(mark), y, i, h, K)       # closed_upto


# --- one state of out ------------------------------------------------------------------------


def rc_scan(n: int, start: List[int], dst: List[int], S: List[int], mark: List[int],
            out: List[int], par: List[int], via: List[int], h: int, nh: int) -> None:
    """Follow every transition of the state out[h]: mark and add each new target."""
    # Why: read access (1/4: the caller keeps 1/4, so the inputs are known unchanged after).
    Requires(Acc(list_pred(start), 1 / 4) and Acc(list_pred(dst), 1 / 4)
             and Acc(list_pred(S), 1 / 4))
    # Why: write access to mark and the three outputs.
    Requires(Acc(list_pred(mark)) and Acc(list_pred(out)) and Acc(list_pred(par))
             and Acc(list_pred(via)))
    # Math: termination measure n + 5 (calls add_state, measure n + 3).
    Requires(MustTerminate(n + 5))
    # Math: blocks_ok(n, start, T) ∧ targets_ok(n, dst)
    Requires(blocks_ok(n, start, len(dst)) and targets_ok(n, dst))
    # Math: sizes ∧ h ∈ [0,|o|) ∧ nh = h+1 ∧ |o| ≤ n
    Requires(len(mark) == n and len(par) == len(out) and len(via) == len(out))
    Requires(0 <= h and h < len(out) and nh == h + 1 and len(out) <= n)
    # Math: marks_ok ∧ |o| = nmarked(mk, n) ∧ wit_ok ∧ contains_S(mk, |S|) ∧ closed_upto(mk, h, 0)
    # Why: the outer loop's invariants at the start of out[h].
    Requires(marks_ok(ToSeq(mark), ToSeq(out)) and len(out) == nmarked(ToSeq(mark), n))
    Requires(wit_ok(ToSeq(start), ToSeq(dst), ToSeq(S), ToSeq(out), ToSeq(par), ToSeq(via)))
    Requires(contains_S(ToSeq(S), ToSeq(mark), len(S)))
    Requires(closed_upto(ToSeq(start), ToSeq(dst), ToSeq(mark), h, 0))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 4) and Acc(list_pred(dst), 1 / 4)
            and Acc(list_pred(S), 1 / 4))
    Ensures(Acc(list_pred(mark)) and Acc(list_pred(out)) and Acc(list_pred(par))
            and Acc(list_pred(via)))
    # Math: sizes ∧ nh ≤ |o| ≤ n
    Ensures(len(mark) == n and len(par) == len(out) and len(via) == len(out))
    Ensures(nh <= len(out) and len(out) <= n)
    # Math: the invariants, with out[h] now processed: closed_upto(mk, nh, 0)
    Ensures(marks_ok(ToSeq(mark), ToSeq(out)) and len(out) == nmarked(ToSeq(mark), n))
    Ensures(wit_ok(ToSeq(start), ToSeq(dst), ToSeq(S), ToSeq(out), ToSeq(par), ToSeq(via)))
    Ensures(contains_S(ToSeq(S), ToSeq(mark), len(S)))
    Ensures(closed_upto(ToSeq(start), ToSeq(dst), ToSeq(mark), nh, 0))
    x = out[h]                               # the state to process
    # Math: o[h] = x
    # Why (hint): the list read, as a sequence entry (the term marks_ok's trigger needs).
    Assert(ToSeq(out)[h] == x)
    # Math: x ∈ [0,n) ∧ mk[x] = h
    # Why (hint): marks_ok (1) at h.
    Assert(0 <= x and x < n and ToSeq(mark)[x] == h)
    block_range(n, start, dst, x)            # lemma: block(x) is a valid range
    lo = start[x]                            # first transition of x
    hi = start[x + 1]                        # one past its last transition
    closed_enter(ToSeq(start), ToSeq(dst), ToSeq(mark), ToSeq(out), h, x, lo)   # lemma: followed up to (h, lo)
    k = lo
    while k < hi:                            # each transition of x
        # Why: permissions.
        Invariant(Acc(list_pred(start), 1 / 4) and Acc(list_pred(dst), 1 / 4)
                  and Acc(list_pred(S), 1 / 4))
        Invariant(Acc(list_pred(mark)) and Acc(list_pred(out)) and Acc(list_pred(par))
                  and Acc(list_pred(via)))
        # Math: measure hi - k + n + 4, decreasing (> n + 3: calls add_state).
        Invariant(MustTerminate(hi - k + n + 4))
        # Math: start, dst, S unchanged.
        Invariant(ToSeq(start) == Old(ToSeq(start)) and ToSeq(dst) == Old(ToSeq(dst))
                  and ToSeq(S) == Old(ToSeq(S)))
        # Math: targets_ok(n, dst)
        # Why: the targets are states (to index mark).
        Invariant(targets_ok(n, dst))
        # Math: |start| = n+1 ∧ x ∈ [0,n) ∧ lo = start[x] ≤ k ≤ hi = start[x+1] ≤ T ∧ 0 ≤ lo
        Invariant(len(start) == n + 1 and 0 <= x and x < n and lo == start[x]
                  and hi == start[x + 1] and 0 <= lo and lo <= k and k <= hi
                  and hi <= len(dst))
        # Math: sizes ∧ h ∈ [0,|o|) ∧ |o| ≤ n ∧ o[h] = x ∧ mk[x] = h
        Invariant(len(mark) == n and len(par) == len(out) and len(via) == len(out))
        Invariant(0 <= h and h < len(out) and len(out) <= n)
        Invariant(ToSeq(out)[h] == x and ToSeq(mark)[x] == h)
        # Math: marks_ok ∧ count ∧ wit_ok ∧ contains_S(mk, |S|) ∧ closed_upto(mk, h, k)
        Invariant(marks_ok(ToSeq(mark), ToSeq(out)) and len(out) == nmarked(ToSeq(mark), n))
        Invariant(wit_ok(ToSeq(start), ToSeq(dst), ToSeq(S), ToSeq(out), ToSeq(par), ToSeq(via)))
        Invariant(contains_S(ToSeq(S), ToSeq(mark), len(S)))
        Invariant(closed_upto(ToSeq(start), ToSeq(dst), ToSeq(mark), h, k))
        y = dst[k]                           # the target of transition k
        # Math: y ∈ [0,n)
        # Why (hint): targets_ok at k.
        Assert(0 <= y and y < n)
        if mark[y] == -1:                    # not reached yet: add it, reached from x by k
            add_state(n, ToSeq(start), ToSeq(dst), ToSeq(S), mark, out, par, via, y, h, k, len(S), h, k)
        # Math: mk[y] ≥ 0
        # Why (hint): just marked, or marked before (marks_ok (2): a mark is a position).
        Assert(ToSeq(mark)[y] >= 0)
        nk = k + 1
        closed_step(ToSeq(start), ToSeq(dst), ToSeq(mark), h, k, nk)   # lemma: followed up to (h, k+1)
        k = nk
    closed_next(ToSeq(start), ToSeq(dst), ToSeq(mark), ToSeq(out), h, x, k, nh)   # lemma: on to (h+1, 0)


# --- the operation ---------------------------------------------------------------------------


def reachable(n: int, start: List[int], dst: List[int], S: List[int], mark: List[int],
              out: List[int], par: List[int], via: List[int]) -> None:
    """The states reachable from the start states S, breadth-first.

    The caller passes `mark`, n entries all -1, and three empty lists. On return: out lists the
    reachable states, each once, in breadth-first order; mark[y] is the position of y in out, or
    -1 (not reachable). Witnesses: if par[i] = -1, out[i] = S[via[i]] (a start state);
    otherwise transition via[i] goes from out[par[i]] (with par[i] < i) to out[i].

    Proved (spec: certisc-proof/spec/reach.md):
    - in range and no duplicates (marks_ok);
    - contains S;
    - closed: every transition of a reached state goes to a reached state;
    - witnesses: each entry is in S or reached from an earlier entry.
    With the Lean theorem reach_eq_of_certificate: the entries of out are exactly reach f S."""
    # Why: read access to the automaton and to S.
    Requires(Acc(list_pred(start), 1 / 2) and Acc(list_pred(dst), 1 / 2)
             and Acc(list_pred(S), 1 / 2))
    # Why: write access to mark and the three outputs.
    Requires(Acc(list_pred(mark)) and Acc(list_pred(out)) and Acc(list_pred(par))
             and Acc(list_pred(via)))
    # Math: termination measure n + 6 (calls rc_scan, measure n + 5).
    Requires(MustTerminate(n + 6))
    # Math: blocks_ok(n, start, T) ∧ targets_ok(n, dst)
    # Why: a validated automaton (check_automaton: blocks_ok and transitions_ok, with T = |evt|
    #      = |dst|).
    Requires(blocks_ok(n, start, len(dst)) and targets_ok(n, dst))
    # Math: ∀ j ∈ [0,|S|): S[j] ∈ [0,n)
    # Why: "start states in range". Repeats are allowed.
    Requires(Forall(int, lambda j: (Implies(0 <= j and j < len(S), 0 <= S[j] and S[j] < n),
                                    [[S[j]]])))
    # Math: |mark| = n ∧ ∀ y ∈ [0,n): mark[y] = -1 ∧ |out| = |par| = |via| = 0
    Requires(len(mark) == n)
    Requires(Forall(int, lambda y: (Implies(0 <= y and y < len(mark), ToSeq(mark)[y] == -1),
                                    [[ToSeq(mark)[y]]])))
    Requires(len(out) == 0 and len(par) == 0 and len(via) == 0)
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 2) and Acc(list_pred(dst), 1 / 2)
            and Acc(list_pred(S), 1 / 2))
    Ensures(Acc(list_pred(mark)) and Acc(list_pred(out)) and Acc(list_pred(par))
            and Acc(list_pred(via)))
    # Math: |mark| = n ∧ |par| = |via| = |out| ≤ n
    Ensures(len(mark) == n and len(par) == len(out) and len(via) == len(out)
            and len(out) <= n)
    # THE RESULT.
    # Math: ∀ i: out[i] ∈ [0,n) ∧ mark[out[i]] = i;  ∀ y: mark[y] ≠ -1 → out[mark[y]] = y
    # Why: in range, no duplicates, and "marked" = "in out".
    Ensures(marks_ok(ToSeq(mark), ToSeq(out)))
    # Math: ∀ j ∈ [0,|S|): mark[S[j]] ≥ 0                                    (contains S)
    Ensures(contains_S(ToSeq(S), ToSeq(mark), len(S)))
    # Math: ∀ x, k ∈ block(x): mark[x] ≥ 0 → mark[dst[k]] ≥ 0                (closed)
    Ensures(closed_all(ToSeq(start), ToSeq(dst), ToSeq(mark)))
    # Math: ∀ i: out[i] = S[via[i]] (par[i] = -1) ∨ out[par[i]] --_{via[i]}--> out[i], par[i] < i
    Ensures(wit_ok(ToSeq(start), ToSeq(dst), ToSeq(S), ToSeq(out), ToSeq(par), ToSeq(via)))
    count_clear(ToSeq(mark), n)              # lemma: nmarked(mk, n) = 0 = |out|
    # Math: |start| = n+1
    # Why (hint): from blocks_ok (add_state needs it).
    Assert(len(start) == n + 1)
    # Math: closed_upto(mk, 0, 0)
    # Why (hint): nothing processed yet: no mark is < 0, and no position is < 0.
    Assert(closed_upto(ToSeq(start), ToSeq(dst), ToSeq(mark), 0, 0))
    j = 0                                    # position in S
    while j < len(S):                        # mark each start state (once)
        # Why: permissions.
        Invariant(Acc(list_pred(start), 1 / 2) and Acc(list_pred(dst), 1 / 2)
                  and Acc(list_pred(S), 1 / 2))
        Invariant(Acc(list_pred(mark)) and Acc(list_pred(out)) and Acc(list_pred(par))
                  and Acc(list_pred(via)))
        # Math: measure |S| - j + n + 4, decreasing (> n + 3: calls add_state).
        Invariant(MustTerminate(len(S) - j + n + 4))
        # Math: start, dst, S unchanged; blocks_ok; targets_ok; S in range; |start| = n+1
        Invariant(ToSeq(start) == Old(ToSeq(start)) and ToSeq(dst) == Old(ToSeq(dst))
                  and ToSeq(S) == Old(ToSeq(S)))
        Invariant(blocks_ok(n, start, len(dst)) and targets_ok(n, dst) and len(start) == n + 1)
        Invariant(Forall(int, lambda jj: (Implies(0 <= jj and jj < len(S),
                                                  0 <= S[jj] and S[jj] < n), [[S[jj]]])))
        # Math: 0 ≤ j ≤ |S| ∧ sizes ∧ |o| ≤ n
        Invariant(0 <= j and j <= len(S))
        Invariant(len(mark) == n and len(par) == len(out) and len(via) == len(out)
                  and len(out) <= n)
        # Math: marks_ok ∧ count ∧ wit_ok ∧ contains_S(mk, j) ∧ closed_upto(mk, 0, 0)
        Invariant(marks_ok(ToSeq(mark), ToSeq(out)) and len(out) == nmarked(ToSeq(mark), n))
        Invariant(wit_ok(ToSeq(start), ToSeq(dst), ToSeq(S), ToSeq(out), ToSeq(par), ToSeq(via)))
        Invariant(contains_S(ToSeq(S), ToSeq(mark), j))
        Invariant(closed_upto(ToSeq(start), ToSeq(dst), ToSeq(mark), 0, 0))
        y = S[j]                             # a start state
        if mark[y] == -1:                    # not marked yet: add it (witness: S[j])
            add_state(n, ToSeq(start), ToSeq(dst), ToSeq(S), mark, out, par, via, y, -1, j, j, 0, 0)
        # Math: mk[y] ≥ 0
        # Why (hint): just marked, or marked before (marks_ok (2)).
        Assert(ToSeq(mark)[y] >= 0)
        nj = j + 1
        # Math: contains_S(mk, nj)
        # Why (hint): written out with nj (the same object j becomes below).
        Assert(Forall(int, lambda jj: (Implies(0 <= jj and jj < nj and jj < len(ToSeq(S)),
                                               0 <= ToSeq(S)[jj] and ToSeq(S)[jj] < len(mark)
                                               and ToSeq(mark)[ToSeq(S)[jj]] >= 0),
                                       [[ToSeq(S)[jj]]])))
        j = nj
    contains_all(ToSeq(S), ToSeq(mark), j, len(S))  # lemma: contains_S(mk, j) with j = |S|
    h = 0                                    # position in out (the queue)
    while h < len(out):                      # process each reached state, breadth-first
        # Why: permissions.
        Invariant(Acc(list_pred(start), 1 / 2) and Acc(list_pred(dst), 1 / 2)
                  and Acc(list_pred(S), 1 / 2))
        Invariant(Acc(list_pred(mark)) and Acc(list_pred(out)) and Acc(list_pred(par))
                  and Acc(list_pred(via)))
        # Math: measure 2n - h + 6, decreasing; > n + 5 since h ≤ |o| ≤ n.
        # Why: out grows, but at most to n (|o| = nmarked(mk, n) ≤ n), so h catches up.
        Invariant(MustTerminate(2 * n - h + 6))
        # Math: start, dst, S unchanged; blocks_ok; targets_ok
        Invariant(ToSeq(start) == Old(ToSeq(start)) and ToSeq(dst) == Old(ToSeq(dst))
                  and ToSeq(S) == Old(ToSeq(S)))
        Invariant(blocks_ok(n, start, len(dst)) and targets_ok(n, dst))
        # Math: 0 ≤ h ≤ |o| ≤ n ∧ sizes
        Invariant(0 <= h and h <= len(out) and len(out) <= n)
        Invariant(len(mark) == n and len(par) == len(out) and len(via) == len(out))
        # Math: marks_ok ∧ count ∧ wit_ok ∧ contains_S(mk, |S|) ∧ closed_upto(mk, h, 0)
        Invariant(marks_ok(ToSeq(mark), ToSeq(out)) and len(out) == nmarked(ToSeq(mark), n))
        Invariant(wit_ok(ToSeq(start), ToSeq(dst), ToSeq(S), ToSeq(out), ToSeq(par), ToSeq(via)))
        Invariant(contains_S(ToSeq(S), ToSeq(mark), len(S)))
        Invariant(closed_upto(ToSeq(start), ToSeq(dst), ToSeq(mark), h, 0))
        nh = h + 1
        rc_scan(n, start, dst, S, mark, out, par, via, h, nh)   # follow out[h]'s transitions
        h = nh
    closed_final(ToSeq(start), ToSeq(dst), ToSeq(mark), ToSeq(out), h)      # lemma: every marked state closed
