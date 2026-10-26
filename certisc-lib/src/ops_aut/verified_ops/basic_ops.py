"""
Verified basic operations on an encoded automaton (certisc-proof/spec/basic_ops.md).

The automaton is encoded as in core_aut/verified_core/check.py: states 0 .. n-1, events 0 .. m-1, transitions
grouped by source state (state x owns positions start[x] .. start[x+1]-1 of evt / dst; position k
is the transition x --evt[k]--> dst[k]).

- next_states    the states reached from a list of states S by one event e (Lean: `step f S e`)
- active_events  the events enabled at some state of S (Lean: `active f S`)

Outputs: `out`, the reached states, each once; the witnesses `src`, `via` (out[i] is reached from
S[src[i]] by transition via[i]); and `pos`, a dict y -> position of y in out. All four are new
for each call (cost: the size of the result), so nothing is kept between calls. The public
interface (later, over Automaton objects) decides which of them to return.

Verify with Nagini, from certisc-lib/ (Python >= 3.12, `verify` extra, Java):

    nagini src/ops_aut/verified_ops/basic_ops.py

Math notation used in the comments:
    [a, b)              the integers a, a+1, ..., b-1
    |l|                 length of list l (or number of keys of a dict)
    T                   |evt|, the number of transitions
    block(x)            [start[x], start[x+1]), the positions of the transitions of state x
    x --e-->_k y        transition k goes from x to y on event e:
                        k ∈ block(x) ∧ evt[k] = e ∧ dst[k] = y
    keys(pos)           the keys of dict pos
    l_old               the value of l when the method was called (Old(...))

How to read the contracts (all of them are removed before the code runs; they cost nothing):
- Requires(P)       precondition: the caller must make P true; the body may assume it.
- Ensures(P)        postcondition: the body must make P true; the caller may assume it.
- Invariant(P)      loop invariant: true before the loop, and kept by every iteration.
- Assert(P)         a step of the proof: Nagini checks P here, then may use it. Most Asserts
                    below are hints, facts Nagini can prove but would not find by itself.
- Acc(list_pred(l), q) / Acc(dict_pred(d), q)
                    permission to use list l / dict d. q = 1 (or omitted): read and write. A
                    fraction such as 1/2: read only. A method gives the permission back in its
                    Ensures. A caller that passes only part of its share keeps the rest, and
                    Nagini then knows the callee did not change it. Acc has no mathematical
                    content: it is about who may touch the memory, not about values.
- MustTerminate(t)  the method (or loop) terminates; for a loop, t must go down each
                    iteration. A method can only call methods with a smaller t.
- ToSeq(l)          the contents of list l as a mathematical sequence (a value, not an object).
- Old(x)            the value of x when the method was called.
- Forall(int, lambda i: (P, [[t]]))
                    ∀ i ∈ ℤ: P. [[t]] is the trigger: Nagini uses the fact for an i only when
                    the term t appears in the proof for that i (no mathematical content).
- Forall(d, lambda y: P)
                    ∀ y ∈ keys(d): P.
- @Pure             a side-effect-free function, usable inside contracts (a definition).
"""

from typing import Dict, List

from nagini_contracts.contracts import *
from nagini_contracts.obligations import MustTerminate

# The well-formedness predicates of the verified validity checker (needs core_aut/py.typed).
from core_aut.verified_core.check import block_sorted, blocks_ok, sorted_ok, transitions_ok
# The active-event index (verified checker: core_aut/verified_core/active_index.py).
from core_aut.verified_core.active_index import nxt, run_ok, seg_ok


# --- specification ---------------------------------------------------------------------------
# Definitions used in the contracts. They run no code at runtime; they say what "correct" means.


@Pure
def input_ok(n: int, m: int, start: List[int], evt: List[int], dst: List[int],
             in_E: List[bool]) -> bool:
    """The transition structure is well formed (core_aut/verified_core/check.py). A precondition, not a
    check: the caller passes a validated automaton."""
    # Why: read access to the four lists (1/8: a small share; the caller keeps the rest).
    Requires(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
             and Acc(list_pred(dst), 1 / 8) and Acc(list_pred(in_E), 1 / 8))
    # Math: input_ok ⟺ blocks_ok(n, start, T) ∧ sorted_ok(n, start, evt)
    #                   ∧ transitions_ok(n, m, in_E, evt, dst), where
    #   blocks_ok:      |start| = n+1, start[0] = 0, start[n] = T,
    #                   ∀ x ∈ [0,n): 0 ≤ start[x] ≤ start[x+1] ≤ T
    #   sorted_ok:      ∀ x ∈ [0,n). ∀ j < i in block(x): evt[j] ≤ evt[i]
    #   transitions_ok: |in_E| = m, |dst| = T, ∀ k ∈ [0,T): evt[k] ∈ [0,m) ∧ in_E[evt[k]]
    #                   ∧ dst[k] ∈ [0,n)
    # Why: the blocks give safe indexing; sorted blocks allow binary search; "dst[k] ∈ [0,n)"
    #      makes the result's states in range. All three are guaranteed by check_automaton.
    return (blocks_ok(n, start, len(evt)) and sorted_ok(n, start, evt)
            and transitions_ok(n, m, in_E, evt, dst))


@Pure
def move(start: List[int], evt: List[int], dst: List[int], S: List[int], e: int,
         j: int, k: int, y: int) -> bool:
    """Transition k is x --e--> y for the state x = S[j] of the list S."""
    # Why: read access to the lists the definition looks at.
    Requires(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
             and Acc(list_pred(dst), 1 / 8) and Acc(list_pred(S), 1 / 8))
    # Math: move(j, k, y) ⟺ j ∈ [0,|S|) ∧ S[j] ∈ [0, |start|-1)
    #                        ∧ k ∈ block(S[j]) ∧ k ∈ [0,T) ∧ k < |dst| ∧ evt[k] = e ∧ dst[k] = y
    #       i.e. S[j] --e-->_k y.
    # Why: the bounds first, so every index in the formula is valid (Nagini checks that).
    return (0 <= j and j < len(S) and 0 <= S[j] and S[j] + 1 < len(start)
            and start[S[j]] <= k and k < start[S[j] + 1] and 0 <= k and k < len(evt)
            and k < len(dst) and evt[k] == e and dst[k] == y)


@Pure
def pos_ok(pos: Dict[int, int], o: PSeq[int]) -> bool:
    """pos and the result agree: each result entry o[i] maps to its position i, and each key y
    of pos is the result entry at pos[y]. Hence no duplicates in o, and keys(pos) = set(o)."""
    # Why: read access to the dict (the result list comes in as a sequence value).
    Requires(Acc(dict_pred(pos), 1 / 8))
    # Math (1): ∀ i ∈ [0,|o|): o[i] ∈ keys(pos) ∧ pos[o[i]] = i
    # Why: if o[i] = o[i'] then i = pos[o[i]] = i': no duplicates. Trigger: the term o[i].
    return (Forall(int, lambda i: (Implies(0 <= i and i < len(o),
                                           o[i] in pos and pos[o[i]] == i), [[o[i]]]))
            # Math (2): ∀ y ∈ keys(pos): pos[y] ∈ [0,|o|) ∧ o[pos[y]] = y
            # Why: "y is a key" ⟹ "y is in the result" (at position pos[y]).
            and Forall(pos, lambda y: (0 <= pos[y] and pos[y] < len(o) and o[pos[y]] == y)))


@Pure
def sound(start: List[int], evt: List[int], dst: List[int], S: List[int], e: int,
          o: PSeq[int], sj: PSeq[int], v: PSeq[int]) -> bool:
    """Each result entry o[i] is reached from the state S[sj[i]] by transition v[i]."""
    # Why: read access to the input lists (the result lists come in as sequences).
    Requires(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
             and Acc(list_pred(dst), 1 / 8) and Acc(list_pred(S), 1 / 8))
    # Math: |sj| = |o| ∧ |v| = |o|
    # Why: one witness of each kind per result entry.
    Requires(len(sj) == len(o) and len(v) == len(o))
    # Math: ∀ i ∈ [0,|o|): S[sj[i]] --e-->_{v[i]} o[i]
    # Why: the witnesses sj[i], v[i] are stored, so no "∃" is needed (easy for Nagini).
    return Forall(int, lambda i: (Implies(0 <= i and i < len(o),
                                          move(start, evt, dst, S, e, sj[i], v[i], o[i])),
                                  [[o[i]]]))


@Pure
def complete_upto(start: List[int], evt: List[int], dst: List[int], S: List[int], e: int,
                  pos: Dict[int, int], J: int, K: int) -> bool:
    """Every move from S[j] with j < J, or from S[J] at a position k < K, has its target in
    pos (so, by pos_ok, in the result)."""
    # Why: read access to the input lists and the dict.
    Requires(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
             and Acc(list_pred(dst), 1 / 8) and Acc(list_pred(S), 1 / 8)
             and Acc(dict_pred(pos), 1 / 8))
    # Math: ∀ k ∈ [0,T). ∀ j. (S[j] --e-->_k dst[k]) ∧ (j < J ∨ (j = J ∧ k < K))
    #                          → dst[k] ∈ keys(pos)
    # Why: "(j, k) already visited by the loops" ⟹ "its target is in the result". With J = |S|,
    #      K = 0 this is completeness.
    return Forall(int, lambda k: (Implies(
        0 <= k and k < len(evt) and k < len(dst),
        Forall(int, lambda jj: (Implies(
            move(start, evt, dst, S, e, jj, k, dst[k]) and (jj < J or (jj == J and k < K)),
            dst[k] in pos),
            [[move(start, evt, dst, S, e, jj, k, dst[k])]]))),   # trigger for jj
        [[dst[k]]]))                                              # trigger for k


# --- lemmas ----------------------------------------------------------------------------------
# Methods with no runtime effect: each proves one small fact in a small context, which Nagini
# finds much easier than the same fact inside the big loop. Calling one = using the fact.


def block_of(n: int, m: int, start: List[int], evt: List[int], dst: List[int], in_E: List[bool],
             x: int) -> None:
    """Lemma: the block of a state lies within the transition lists."""
    # Why: read access; the caller keeps the rest of its share, so the lists are known unchanged.
    Requires(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
             and Acc(list_pred(dst), 1 / 8) and Acc(list_pred(in_E), 1 / 8))
    # Math: termination measure 1.
    # Why: no loops; any caller with a larger measure may call it.
    Requires(MustTerminate(1))
    # Math: input_ok ∧ x ∈ [0,n)
    # Why: a well-formed automaton and a state x.
    Requires(input_ok(n, m, start, evt, dst, in_E) and 0 <= x and x < n)
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
            and Acc(list_pred(dst), 1 / 8) and Acc(list_pred(in_E), 1 / 8))
    # Math: input_ok
    # Why: restated so the caller still has it (a postcondition is checked after the call).
    Ensures(input_ok(n, m, start, evt, dst, in_E))
    # Math: |start| = n+1 ∧ |dst| = T ∧ 0 ≤ start[x] ≤ start[x+1] ≤ T
    # Why: the fact itself: block(x) is a valid range inside evt and dst.
    Ensures(len(start) == n + 1 and len(dst) == len(evt) and 0 <= start[x]
            and start[x] <= start[x + 1] and start[x + 1] <= len(evt))
    # Math: ∀ j < i in block(x): evt[j] ≤ evt[i]
    # Why: block(x) is sorted (from sorted_ok at x), for the binary searches.
    Ensures(block_sorted(start[x], start[x + 1], evt))
    # Math: start[x+1] ≤ T
    # Why (hint): mentioning start[x + 1] triggers blocks_ok's quantifier at x.
    Assert(start[x + 1] <= len(evt))
    # Math: block_sorted(start[x], start[x+1], evt)
    # Why (hint): mentioning the term triggers sorted_ok's quantifier at x.
    Assert(block_sorted(start[x], start[x + 1], evt))


def target_of(n: int, m: int, start: List[int], evt: List[int], dst: List[int],
              in_E: List[bool], k: int) -> None:
    """Lemma: the target of a transition is a state."""
    # Why: read access, as in block_of.
    Requires(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
             and Acc(list_pred(dst), 1 / 8) and Acc(list_pred(in_E), 1 / 8))
    # Math: termination measure 1.
    Requires(MustTerminate(1))
    # Math: input_ok ∧ k ∈ [0,T)
    # Why: a well-formed automaton and a transition position k.
    Requires(input_ok(n, m, start, evt, dst, in_E) and 0 <= k and k < len(evt))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
            and Acc(list_pred(dst), 1 / 8) and Acc(list_pred(in_E), 1 / 8))
    # Math: input_ok
    # Why: restated for the caller.
    Ensures(input_ok(n, m, start, evt, dst, in_E))
    # Math: k < |dst| ∧ dst[k] ∈ [0,n) ∧ evt[k] ∈ [0,m)
    # Why: the facts themselves: the target of k is a state, and its event is an event number.
    Ensures(k < len(dst) and 0 <= dst[k] and dst[k] < n and 0 <= evt[k] and evt[k] < m)
    # Math: dst[k] ∈ [0,n) ∧ evt[k] ∈ [0,m)
    # Why (hint): mentioning dst[k] and evt[k] triggers transitions_ok's quantifier at k.
    Assert(0 <= dst[k] and dst[k] < n and 0 <= evt[k] and evt[k] < m)


def skip_range(start: List[int], evt: List[int], dst: List[int], S: List[int], e: int,
               pos: Dict[int, int], j: int, K1: int, K2: int) -> None:
    """Lemma: positions K1 .. K2-1 hold no e-move of S[j], so they need nothing."""
    # Why: read access to the input lists and the dict.
    Requires(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
             and Acc(list_pred(dst), 1 / 8) and Acc(list_pred(S), 1 / 8)
             and Acc(dict_pred(pos), 1 / 8))
    # Math: termination measure 1.
    Requires(MustTerminate(1))
    # Math: 0 ≤ K1 ≤ K2 ≤ T ∧ |dst| = T
    Requires(0 <= K1 and K1 <= K2 and K2 <= len(evt) and len(dst) == len(evt))
    # Math: ∀ k ∈ [K1,K2): ¬(S[j] --e-->_k dst[k])
    # Why: none of these positions is an e-move of S[j] (the caller knows why: outside the
    #      block, or the event is < e or > e).
    Requires(Forall(int, lambda k: (Implies(K1 <= k and k < K2,
                                            not move(start, evt, dst, S, e, j, k, dst[k])),
                                    [[dst[k]]])))
    # Math: complete_upto(pos, j, K1)
    # Why: everything visited before (j, K1) is covered.
    Requires(complete_upto(start, evt, dst, S, e, pos, j, K1))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
            and Acc(list_pred(dst), 1 / 8) and Acc(list_pred(S), 1 / 8)
            and Acc(dict_pred(pos), 1 / 8))
    # Math: complete_upto(pos, j, K2)
    # Why: positions K1 .. K2-1 add nothing to check.
    Ensures(complete_upto(start, evt, dst, S, e, pos, j, K2))
    # Math: the body of complete_upto(pos, j, K2).
    # Why (hint): written out, because Nagini does not unfold the function by itself here.
    Assert(Forall(int, lambda kk: (Implies(
        0 <= kk and kk < len(evt) and kk < len(dst),
        Forall(int, lambda jj: (Implies(
            move(start, evt, dst, S, e, jj, kk, dst[kk]) and (jj < j or (jj == j and kk < K2)),
            dst[kk] in pos),
            [[move(start, evt, dst, S, e, jj, kk, dst[kk])]]))),
        [[dst[kk]]])))


def lower_bound(evt: List[int], lo: int, hi: int, e: int) -> int:
    """Binary search in a sorted block: the first position a in lo .. hi with evt[a] >= e."""
    # Math: termination measure 2.
    Requires(MustTerminate(2))
    # Why: read access to evt.
    Requires(Acc(list_pred(evt), 1 / 8))
    # Math: 0 ≤ lo ≤ hi ≤ |evt| ∧ ∀ j < i in [lo,hi): evt[j] ≤ evt[i]
    # Why: a valid, sorted range (block_of gives both).
    Requires(0 <= lo and lo <= hi and hi <= len(evt) and block_sorted(lo, hi, evt))
    # Why: gives the permission back.
    Ensures(Acc(list_pred(evt), 1 / 8))
    # Math: lo ≤ a ≤ hi ≤ |evt|
    # Why: hi ≤ |evt| restated, so evt[k] below can be read after the call.
    Ensures(lo <= Result() and Result() <= hi and hi <= len(evt))
    # Math: ∀ k ∈ [lo,a): evt[k] < e
    # Why: everything before a is on a smaller event.
    Ensures(Forall(int, lambda k: (Implies(lo <= k and k < Result(), evt[k] < e), [[evt[k]]])))
    # Math: ∀ k ∈ [a,hi): evt[k] ≥ e
    # Why: everything from a on is on e or a larger event.
    Ensures(Forall(int, lambda k: (Implies(Result() <= k and k < hi, evt[k] >= e), [[evt[k]]])))
    l = lo
    r = hi
    while l < r:
        # Math: termination measure r - l + 2, decreasing (the range halves).
        Invariant(MustTerminate(r - l + 2))
        # Why: read access; evt unchanged.
        Invariant(Acc(list_pred(evt), 1 / 8))
        Invariant(ToSeq(evt) == Old(ToSeq(evt)))
        # Math: lo ≤ l ≤ r ≤ hi ≤ |evt| ∧ block_sorted(lo, hi, evt)
        Invariant(lo <= l and l <= r and r <= hi and hi <= len(evt) and block_sorted(lo, hi, evt))
        # Math: ∀ k ∈ [lo,l): evt[k] < e   and   ∀ k ∈ [r,hi): evt[k] ≥ e
        # Why: the answer is in [l, r]; outside it the comparison with e is known.
        Invariant(Forall(int, lambda k: (Implies(lo <= k and k < l, evt[k] < e), [[evt[k]]])))
        Invariant(Forall(int, lambda k: (Implies(r <= k and k < hi, evt[k] >= e), [[evt[k]]])))
        mid = (l + r) // 2           # l ≤ mid < r
        if evt[mid] < e:
            # Math: ∀ k ∈ [l,mid]: evt[k] ≤ evt[mid] < e
            # Why (hint): sorted, so everything up to mid is < e too.
            Assert(Forall(int, lambda k: (Implies(lo <= k and k <= mid, evt[k] <= evt[mid]),
                                          [[evt[k]]])))
            l = mid + 1
        else:
            # Math: ∀ k ∈ [mid,hi): evt[k] ≥ evt[mid] ≥ e
            # Why (hint): sorted, so everything from mid on is ≥ e too.
            Assert(Forall(int, lambda k: (Implies(mid <= k and k < hi, evt[mid] <= evt[k]),
                                          [[evt[k]]])))
            r = mid
    return l


def upper_bound(evt: List[int], lo: int, hi: int, a: int, e: int) -> int:
    """Binary search in a sorted block, from a: the first position b in a .. hi with
    evt[b] > e."""
    # Math: termination measure 2.
    Requires(MustTerminate(2))
    # Why: read access to evt.
    Requires(Acc(list_pred(evt), 1 / 8))
    # Math: 0 ≤ lo ≤ a ≤ hi ≤ |evt| ∧ ∀ j < i in [lo,hi): evt[j] ≤ evt[i]
    Requires(0 <= lo and lo <= a and a <= hi and hi <= len(evt) and block_sorted(lo, hi, evt))
    # Why: gives the permission back.
    Ensures(Acc(list_pred(evt), 1 / 8))
    # Math: a ≤ b ≤ hi ≤ |evt|
    # Why: hi ≤ |evt| restated, so evt[k] below can be read after the call.
    Ensures(a <= Result() and Result() <= hi and hi <= len(evt))
    # Math: ∀ k ∈ [a,b): evt[k] ≤ e
    Ensures(Forall(int, lambda k: (Implies(a <= k and k < Result(), evt[k] <= e), [[evt[k]]])))
    # Math: ∀ k ∈ [b,hi): evt[k] > e
    # Why: everything from b on is on a larger event.
    Ensures(Forall(int, lambda k: (Implies(Result() <= k and k < hi, evt[k] > e), [[evt[k]]])))
    l = a
    r = hi
    while l < r:
        # Math: termination measure r - l + 2, decreasing.
        Invariant(MustTerminate(r - l + 2))
        # Why: read access; evt unchanged.
        Invariant(Acc(list_pred(evt), 1 / 8))
        Invariant(ToSeq(evt) == Old(ToSeq(evt)))
        # Math: lo ≤ a ≤ l ≤ r ≤ hi ≤ |evt| ∧ block_sorted(lo, hi, evt)
        Invariant(lo <= a and a <= l and l <= r and r <= hi and hi <= len(evt)
                  and block_sorted(lo, hi, evt))
        # Math: ∀ k ∈ [a,l): evt[k] ≤ e   and   ∀ k ∈ [r,hi): evt[k] > e
        Invariant(Forall(int, lambda k: (Implies(a <= k and k < l, evt[k] <= e), [[evt[k]]])))
        Invariant(Forall(int, lambda k: (Implies(r <= k and k < hi, evt[k] > e), [[evt[k]]])))
        mid = (l + r) // 2           # l ≤ mid < r
        if evt[mid] <= e:
            # Math: ∀ k ∈ [a,mid]: evt[k] ≤ evt[mid] ≤ e
            # Why (hint): sorted, so everything up to mid is ≤ e too.
            Assert(Forall(int, lambda k: (Implies(lo <= k and k <= mid, evt[k] <= evt[mid]),
                                          [[evt[k]]])))
            l = mid + 1
        else:
            # Math: ∀ k ∈ [mid,hi): evt[k] ≥ evt[mid] > e
            # Why (hint): sorted, so everything from mid on is > e too.
            Assert(Forall(int, lambda k: (Implies(mid <= k and k < hi, evt[mid] <= evt[k]),
                                          [[evt[k]]])))
            r = mid
    return l


def next_j(start: List[int], evt: List[int], dst: List[int], S: List[int], e: int,
           pos: Dict[int, int], j: int, K: int, nj: int) -> None:
    """Lemma: once the whole block of S[j] is covered, move on to j + 1."""
    # Why: read access to the input lists and the dict.
    Requires(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
             and Acc(list_pred(dst), 1 / 8) and Acc(list_pred(S), 1 / 8)
             and Acc(dict_pred(pos), 1 / 8))
    # Math: termination measure 1.
    Requires(MustTerminate(1))
    # Math: nj = j+1 ∧ j ∈ [0,|S|) ∧ S[j] ∈ [0,|start|-1) ∧ K = start[S[j]+1]
    # Why: K is the end of block(S[j]): the inner loop has finished.
    Requires(nj == j + 1 and 0 <= j and j < len(S) and 0 <= S[j] and S[j] + 1 < len(start)
             and K == start[S[j] + 1])
    # Math: complete_upto(pos, j, K)
    # Why: all moves before (j, K) are covered, i.e. all moves of S[0], ..., S[j].
    Requires(complete_upto(start, evt, dst, S, e, pos, j, K))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
            and Acc(list_pred(dst), 1 / 8) and Acc(list_pred(S), 1 / 8)
            and Acc(dict_pred(pos), 1 / 8))
    # Math: complete_upto(pos, j+1, 0)
    # Why: the same set of moves, described as "before (j+1, 0)".
    Ensures(complete_upto(start, evt, dst, S, e, pos, nj, 0))
    # Math: the body of complete_upto(pos, nj, 0).
    # Why (hint): written out, so Nagini rechecks the quantifier.
    Assert(Forall(int, lambda kk: (Implies(
        0 <= kk and kk < len(evt) and kk < len(dst),
        Forall(int, lambda jj: (Implies(
            move(start, evt, dst, S, e, jj, kk, dst[kk]) and (jj < nj or (jj == nj and kk < 0)),
            dst[kk] in pos),
            [[move(start, evt, dst, S, e, jj, kk, dst[kk])]]))),
        [[dst[kk]]])))


# --- one transition --------------------------------------------------------------------------


def visit(start: List[int], evt: List[int], dst: List[int], S: List[int], e: int,
          pos: Dict[int, int], out: List[int], src: List[int], via: List[int],
          j: int, k: int) -> None:
    """Transition k is a move from S[j]: add its target to the result unless it is there."""
    # Why: read access to the inputs (a small share: the caller's share keeps them unchanged).
    Requires(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
             and Acc(list_pred(dst), 1 / 8) and Acc(list_pred(S), 1 / 8))
    # Why: write access to pos and the three result lists.
    Requires(Acc(dict_pred(pos)) and Acc(list_pred(out)) and Acc(list_pred(src))
             and Acc(list_pred(via)))
    # Math: termination measure 2.
    # Why: 2 because it calls append (measure 1).
    Requires(MustTerminate(2))
    # Math: |src| = |out| ∧ |via| = |out|
    Requires(len(src) == len(out) and len(via) == len(out))
    # Math: k ∈ [0,T) ∧ k < |dst|
    # Why: stated first, so that dst[k] below can be read.
    Requires(0 <= k and k < len(evt) and k < len(dst))
    # Math: S[j] --e-->_k dst[k]
    # Why: k is an e-move from S[j].
    Requires(move(start, evt, dst, S, e, j, k, dst[k]))
    # Math: pos_ok(pos, out) ∧ sound(out, src, via) ∧ complete_upto(pos, j, k)
    # Why: the three loop invariants of next_states, at this point of the loop.
    Requires(pos_ok(pos, ToSeq(out)))
    Requires(sound(start, evt, dst, S, e, ToSeq(out), ToSeq(src), ToSeq(via)))
    Requires(complete_upto(start, evt, dst, S, e, pos, j, k))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
            and Acc(list_pred(dst), 1 / 8) and Acc(list_pred(S), 1 / 8))
    Ensures(Acc(dict_pred(pos)) and Acc(list_pred(out)) and Acc(list_pred(src))
            and Acc(list_pred(via)))
    # Math: |src| = |out| ∧ |via| = |out|
    Ensures(len(src) == len(out) and len(via) == len(out))
    # Math: pos_ok(pos, out) ∧ sound(out, src, via) ∧ complete_upto(pos, j, k+1)
    # Why: the invariants still hold, and transition k is now covered too.
    Ensures(pos_ok(pos, ToSeq(out)))
    Ensures(sound(start, evt, dst, S, e, ToSeq(out), ToSeq(src), ToSeq(via)))
    Ensures(complete_upto(start, evt, dst, S, e, pos, j, k + 1))
    y = dst[k]                       # the target of transition k
    if y not in pos:                 # y is not in the result yet
        i = len(out)                 # the position y will have
        out.append(y)                # add y ...
        src.append(j)                # ... reached from S[j] (witness)
        via.append(k)                # ... by transition k (witness)
        pos[y] = i                   # remember y's position: "y is in the result, at i"
        # Math: ∀ t ∈ [0,i): out[t] = out_old[t] ∧ src[t] = src_old[t] ∧ via[t] = via_old[t]
        # Why (hint): the appends keep the old entries.
        Assert(Forall(int, lambda t: (Implies(0 <= t and t < i,
                                              ToSeq(out)[t] == Old(ToSeq(out))[t]
                                              and ToSeq(src)[t] == Old(ToSeq(src))[t]
                                              and ToSeq(via)[t] == Old(ToSeq(via))[t]),
                                      [[ToSeq(out)[t]]])))
        # Math: out[i] = y ∧ src[i] = j ∧ via[i] = k ∧ pos[y] = i
        # Why (hint): the new entries are what we just wrote.
        Assert(ToSeq(out)[i] == y and ToSeq(src)[i] == j and ToSeq(via)[i] == k and pos[y] == i)
    # (else: y is already in the result; nothing to write.)
    # The next four Asserts are the bodies of the three postconditions, written out, so Nagini
    # rechecks each quantifier with the facts above instead of unfolding the functions itself.
    # Math: ∀ t ∈ [0,|out|): out[t] ∈ keys(pos) ∧ pos[out[t]] = t             (pos_ok, part 1)
    Assert(Forall(int, lambda t: (Implies(0 <= t and t < len(out),
                                          ToSeq(out)[t] in pos and pos[ToSeq(out)[t]] == t),
                                  [[ToSeq(out)[t]]])))
    # Math: ∀ z ∈ keys(pos): pos[z] ∈ [0,|out|) ∧ out[pos[z]] = z               (pos_ok, part 2)
    Assert(Forall(pos, lambda z: (0 <= pos[z] and pos[z] < len(out) and ToSeq(out)[pos[z]] == z)))
    # Math: ∀ t ∈ [0,|out|): S[src[t]] --e-->_{via[t]} out[t]                (sound)
    Assert(Forall(int, lambda t: (Implies(0 <= t and t < len(out),
                                          move(start, evt, dst, S, e, ToSeq(src)[t],
                                               ToSeq(via)[t], ToSeq(out)[t])),
                                  [[ToSeq(out)[t]]])))
    # Math: complete_upto(pos, j, k+1)                                        (complete so far)
    Assert(Forall(int, lambda kk: (Implies(
        0 <= kk and kk < len(evt) and kk < len(dst),
        Forall(int, lambda jj: (Implies(
            move(start, evt, dst, S, e, jj, kk, dst[kk]) and (jj < j or (jj == j and kk < k + 1)),
            dst[kk] in pos),
            [[move(start, evt, dst, S, e, jj, kk, dst[kk])]]))),
        [[dst[kk]]])))


# --- the operation ---------------------------------------------------------------------------


def next_states(n: int, m: int, start: List[int], evt: List[int], dst: List[int],
                in_E: List[bool], S: List[int], e: int, out: List[int], src: List[int],
                via: List[int], pos: Dict[int, int]) -> None:
    """The states reached from the states in S by event e.

    The caller passes four new, empty containers. On return: out lists the reached states,
    each once; out[i] is reached from S[src[i]] by transition via[i]; pos[y] is the position of
    y in out (y in pos ⟺ y is reached).

    Proved (spec: basic_ops.md):
    - in range: every entry of out is a state;
    - no duplicates (pos_ok);
    - sound: every entry of out is reached from S by e (the witnesses src, via);
    - complete: for every x in S and transition x --e--> y, y is in pos, hence in out.
    Together: the set of entries of out = the union over x in S of f(x, e)."""
    # Why: read access to the automaton and to S (half: the caller may keep the other half).
    Requires(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2)
             and Acc(list_pred(dst), 1 / 2) and Acc(list_pred(in_E), 1 / 2)
             and Acc(list_pred(S), 1 / 2))
    # Why: write access to the four outputs.
    Requires(Acc(list_pred(out)) and Acc(list_pred(src)) and Acc(list_pred(via))
             and Acc(dict_pred(pos)))
    # Math: termination, measure |S| + T + 6.
    # Why: bounds both loops (|S| states, at most T transitions).
    Requires(MustTerminate(len(S) + len(evt) + 6))
    # Math: input_ok ∧ e ∈ [0,m)
    # Why: a well-formed (validated) automaton, and "event in range".
    Requires(input_ok(n, m, start, evt, dst, in_E) and 0 <= e and e < m)
    # Math: ∀ j ∈ [0,|S|): S[j] ∈ [0,n)
    # Why: "states in range". Repeats are allowed.
    Requires(Forall(int, lambda j: (Implies(0 <= j and j < len(S), 0 <= S[j] and S[j] < n),
                                    [[S[j]]])))
    # Math: |out| = |src| = |via| = |pos| = 0
    # Why: the outputs start empty (new for each call).
    Requires(len(out) == 0 and len(src) == 0 and len(via) == 0 and len(pos) == 0)
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2)
            and Acc(list_pred(dst), 1 / 2) and Acc(list_pred(in_E), 1 / 2)
            and Acc(list_pred(S), 1 / 2))
    Ensures(Acc(list_pred(out)) and Acc(list_pred(src)) and Acc(list_pred(via))
            and Acc(dict_pred(pos)))
    # Math: input_ok
    # Why: restated for the caller.
    Ensures(input_ok(n, m, start, evt, dst, in_E))
    # Math: |src| = |out| ∧ |via| = |out|
    Ensures(len(src) == len(out) and len(via) == len(out))
    # THE RESULT.
    # Math: ∀ i ∈ [0,|out|): out[i] ∈ [0,n)
    # Why: output in range.
    Ensures(Forall(int, lambda i: (Implies(0 <= i and i < len(out),
                                           0 <= ToSeq(out)[i] and ToSeq(out)[i] < n),
                                   [[ToSeq(out)[i]]])))
    # Math: ∀ i: pos[out[i]] = i;  ∀ y ∈ keys(pos): out[pos[y]] = y
    # Why: no duplicates, and y ∈ keys(pos) ⟺ y ∈ out.
    Ensures(pos_ok(pos, ToSeq(out)))
    # Math: ∀ i ∈ [0,|out|): S[src[i]] --e-->_{via[i]} out[i]
    # Why: sound: every result state is reached from S by e.
    Ensures(sound(start, evt, dst, S, e, ToSeq(out), ToSeq(src), ToSeq(via)))
    # Math: ∀ j ∈ [0,|S|). ∀ k. S[j] --e-->_k dst[k] → dst[k] ∈ keys(pos)
    # Why: complete: every e-move from every state of S has its target in the result.
    Ensures(complete_upto(start, evt, dst, S, e, pos, len(S), 0))
    j = 0                                        # position in S
    while j < len(S):                            # for each state of S
        # Why: the loop keeps its permissions.
        Invariant(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2)
                  and Acc(list_pred(dst), 1 / 2) and Acc(list_pred(in_E), 1 / 2)
                  and Acc(list_pred(S), 1 / 2))
        Invariant(Acc(list_pred(out)) and Acc(list_pred(src)) and Acc(list_pred(via))
                  and Acc(dict_pred(pos)))
        # Math: measure |S| - j + 4, decreasing.
        # Why: the loop terminates.
        Invariant(MustTerminate(len(S) - j + 4))
        # Math: start = start_old ∧ evt = evt_old ∧ dst = dst_old ∧ in_E = in_E_old ∧ S = S_old
        # Why: a loop forgets list contents unless told they don't change.
        Invariant(ToSeq(start) == Old(ToSeq(start)) and ToSeq(evt) == Old(ToSeq(evt))
                  and ToSeq(dst) == Old(ToSeq(dst)) and ToSeq(in_E) == Old(ToSeq(in_E))
                  and ToSeq(S) == Old(ToSeq(S)))
        # Math: input_ok ∧ e ∈ [0,m) ∧ ∀ j' ∈ [0,|S|): S[j'] ∈ [0,n)
        # Why: the preconditions, carried through the loop.
        Invariant(input_ok(n, m, start, evt, dst, in_E) and 0 <= e and e < m)
        Invariant(Forall(int, lambda jj: (Implies(0 <= jj and jj < len(S),
                                                  0 <= S[jj] and S[jj] < n), [[S[jj]]])))
        # Math: 0 ≤ j ≤ |S|
        Invariant(0 <= j and j <= len(S))
        # Math: |src| = |out| ∧ |via| = |out|
        Invariant(len(src) == len(out) and len(via) == len(out))
        # Math: pos_ok(pos, out) ∧ sound(out, src, via)
        # Why: the result so far is consistent with pos, and sound.
        Invariant(pos_ok(pos, ToSeq(out)))
        Invariant(sound(start, evt, dst, S, e, ToSeq(out), ToSeq(src), ToSeq(via)))
        # Math: complete_upto(pos, j, 0)
        # Why: all moves from S[0], ..., S[j-1] are covered.
        Invariant(complete_upto(start, evt, dst, S, e, pos, j, 0))
        x = S[j]                                 # the current state
        block_of(n, m, start, evt, dst, in_E, x)  # lemma: block(x) is a valid range
        lo = start[x]                            # first transition of x
        hi = start[x + 1]                        # one past its last transition
        a = lower_bound(evt, lo, hi, e)          # first e-transition of x (or later event)
        b = upper_bound(evt, lo, hi, a, e)       # one past the last e-transition of x
        # Math: ∀ k ∈ [0,a): ¬(x --e-->_k dst[k])
        # Why (hint): before block(x) a position is not x's; in [lo,a) the event is < e.
        Assert(Forall(int, lambda kk: (Implies(0 <= kk and kk < a,
                                               not move(start, evt, dst, S, e, j, kk, dst[kk])),
                                       [[dst[kk]]])))
        skip_range(start, evt, dst, S, e, pos, j, 0, a)      # lemma: [0, a) needs nothing
        k = a
        while k < b:                             # exactly the e-transitions of x
            # Why: permissions, as in the outer loop.
            Invariant(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2)
                      and Acc(list_pred(dst), 1 / 2) and Acc(list_pred(in_E), 1 / 2)
                      and Acc(list_pred(S), 1 / 2))
            Invariant(Acc(list_pred(out)) and Acc(list_pred(src)) and Acc(list_pred(via))
                      and Acc(dict_pred(pos)))
            # Math: measure b - k + 3, decreasing.
            Invariant(MustTerminate(b - k + 3))
            # Math: the input lists are unchanged (as in the outer loop).
            Invariant(ToSeq(start) == Old(ToSeq(start)) and ToSeq(evt) == Old(ToSeq(evt))
                      and ToSeq(dst) == Old(ToSeq(dst)) and ToSeq(in_E) == Old(ToSeq(in_E))
                      and ToSeq(S) == Old(ToSeq(S)))
            # Math: input_ok ∧ e ∈ [0,m) ∧ ∀ j' ∈ [0,|S|): S[j'] ∈ [0,n)
            Invariant(input_ok(n, m, start, evt, dst, in_E) and 0 <= e and e < m)
            Invariant(Forall(int, lambda jj: (Implies(0 <= jj and jj < len(S),
                                                      0 <= S[jj] and S[jj] < n), [[S[jj]]])))
            # Math: j ∈ [0,|S|) ∧ x = S[j] ∈ [0,n)
            Invariant(0 <= j and j < len(S) and x == S[j] and 0 <= x and x < n)
            # Math: |start| = n+1 ∧ |dst| = T
            Invariant(len(start) == n + 1 and len(dst) == len(evt))
            # Math: lo = start[x] ≤ a ≤ k ≤ b ≤ hi = start[x+1] ≤ T
            # Why: k runs over [a, b) inside block(x).
            Invariant(lo == start[x] and hi == start[x + 1] and lo <= a and a <= k
                      and k <= b and b <= hi and hi <= len(evt))
            # Math: ∀ t ∈ [a,b): evt[t] = e
            # Why: every position visited is an e-transition (from the two searches).
            Invariant(Forall(int, lambda t: (Implies(a <= t and t < b, evt[t] == e), [[evt[t]]])))
            # Math: ∀ t ∈ [b,hi): evt[t] > e
            # Why: kept for the skip after the loop.
            Invariant(Forall(int, lambda t: (Implies(b <= t and t < hi, evt[t] > e), [[evt[t]]])))
            # Math: sizes, pos_ok, sound (as in the outer loop)
            Invariant(len(src) == len(out) and len(via) == len(out))
            Invariant(pos_ok(pos, ToSeq(out)))
            Invariant(sound(start, evt, dst, S, e, ToSeq(out), ToSeq(src), ToSeq(via)))
            # Math: complete_upto(pos, j, k)
            # Why: all moves before (j, k) are covered.
            Invariant(complete_upto(start, evt, dst, S, e, pos, j, k))
            target_of(n, m, start, evt, dst, in_E, k)                 # lemma: dst[k] ∈ [0,n)
            visit(start, evt, dst, S, e, pos, out, src, via, j, k)    # add dst[k] if new
            k += 1
        # Math: ∀ k ∈ [b,hi): ¬(x --e-->_k dst[k])
        # Why (hint): from b on the event is > e.
        Assert(Forall(int, lambda kk: (Implies(b <= kk and kk < hi,
                                               not move(start, evt, dst, S, e, j, kk, dst[kk])),
                                       [[dst[kk]]])))
        skip_range(start, evt, dst, S, e, pos, j, b, hi)     # lemma: [b, hi) needs nothing
        next_j(start, evt, dst, S, e, pos, j, hi, j + 1)         # lemma: x is fully covered
        j += 1


# =============================================================================================
# active_events: the events enabled at some state of S                    (Lean: active f S)
# =============================================================================================
#
# Same scalability choices as next_states: S is a list of states; the result is a list with
# witnesses instead of "there exists". Blocks are sorted by event, so the transitions on one event
# are consecutive: the loop reads the first transition of each run and jumps past the run with
# upper_bound. Positions of the events are kept in a list `emark` of m entries (event -> position
# in out, or -1), not in a dict: Nagini compares dict keys by object, so it cannot conclude
# `evt[t] in pos` from `evt[t] == e` and `e in pos`; list indices compare by value. m is the
# alphabet size (small), so allocating it per call keeps the cost independent of n.


@Pure
def in_block(start: List[int], evt: List[int], S: List[int], j: int, k: int) -> bool:
    """Position k is a transition of the state S[j]."""
    # Why: read access to the lists the definition looks at.
    Requires(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
             and Acc(list_pred(S), 1 / 8))
    # Math: in_block(j, k) ⟺ j ∈ [0,|S|) ∧ S[j] ∈ [0,|start|-1) ∧ k ∈ block(S[j]) ∧ k ∈ [0,T)
    # Why: the bounds first, so every index in the formula is valid.
    return (0 <= j and j < len(S) and 0 <= S[j] and S[j] + 1 < len(start)
            and start[S[j]] <= k and k < start[S[j] + 1] and 0 <= k and k < len(evt))


@Pure
def ev_at(start: List[int], evt: List[int], S: List[int], j: int, k: int, e: int) -> bool:
    """Transition k is a transition of the state S[j], on event e."""
    # Why: read access to the lists the definition looks at.
    Requires(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
             and Acc(list_pred(S), 1 / 8))
    # Math: ev_at(j, k, e) ⟺ in_block(j, k) ∧ evt[k] = e
    # Why: one function for the whole fact (as `move` in next_states), so Nagini matches the
    #      same term in the postcondition and in the hint.
    return in_block(start, evt, S, j, k) and evt[k] == e


@Pure
def ev_sound(start: List[int], evt: List[int], S: List[int], o: PSeq[int], sj: PSeq[int],
             v: PSeq[int]) -> bool:
    """Each result entry o[i] is the event of transition v[i] of the state S[sj[i]]."""
    # Why: read access to the input lists (the result lists come in as sequences).
    Requires(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
             and Acc(list_pred(S), 1 / 8))
    # Math: |sj| = |o| ∧ |v| = |o|
    Requires(len(sj) == len(o) and len(v) == len(o))
    # Math: ∀ i ∈ [0,|o|): ev_at(sj[i], v[i], o[i])
    # Why: sound with witnesses: event o[i] really occurs at a state of S.
    return Forall(int, lambda i: (Implies(0 <= i and i < len(o),
                                          ev_at(start, evt, S, sj[i], v[i], o[i])),
                                  [[o[i]]]))


@Pure
def marks_ok(mk: PSeq[int], o: PSeq[int]) -> bool:
    """mark and the result agree: each result entry o[i] is marked with its position i, and
    each marked entry y is the result entry at its mark. Hence no duplicates in o."""
    # Math (1): ∀ i ∈ [0,|o|): o[i] ∈ [0,|mk|) ∧ mk[o[i]] = i
    # Why: in range, and o[i] = o[i'] gives i = mk[o[i]] = i': no duplicates.
    return (Forall(int, lambda i: (Implies(0 <= i and i < len(o),
                                           0 <= o[i] and o[i] < len(mk) and mk[o[i]] == i),
                                   [[o[i]]]))
            # Math (2): ∀ y ∈ [0,|mk|): mk[y] ≠ -1 → mk[y] ∈ [0,|o|) ∧ o[mk[y]] = y
            # Why: "y is marked" ⟹ "y is in the result" (at position mk[y]).
            and Forall(int, lambda y: (Implies(0 <= y and y < len(mk) and mk[y] != -1,
                                               0 <= mk[y] and mk[y] < len(o) and o[mk[y]] == y),
                                       [[mk[y]]])))


@Pure
def all_clear(mk: PSeq[int]) -> bool:
    # Math: ∀ y ∈ [0,|mk|): mk[y] = -1
    # Why: nothing marked yet (required on entry).
    return Forall(int, lambda y: (Implies(0 <= y and y < len(mk), mk[y] == -1), [[mk[y]]]))


@Pure
def ev_complete_upto(start: List[int], evt: List[int], S: List[int], mk: PSeq[int],
                     J: int, K: int) -> bool:
    """The event of every transition of S[j] with j < J, or of S[J] at a position k < K, is
    marked (so, by marks_ok, in the result)."""
    # Why: read access to the input lists (the marks come in as a sequence).
    Requires(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
             and Acc(list_pred(S), 1 / 8))
    # Math: ∀ k. ∀ j. in_block(j, k) ∧ (j < J ∨ (j = J ∧ k < K))
    #                 → evt[k] ∈ [0,|mk|) ∧ mk[evt[k]] ≥ 0
    # Why: "(j, k) already covered by the loops" ⟹ "its event is in the result". With J = |S|,
    #      K = 0 this is completeness.
    return Forall(int, lambda k: (Implies(
        0 <= k and k < len(evt),
        Forall(int, lambda jj: (Implies(
            in_block(start, evt, S, jj, k) and (jj < J or (jj == J and k < K)),
            0 <= evt[k] and evt[k] < len(mk) and mk[evt[k]] >= 0),
            [[in_block(start, evt, S, jj, k)]]))),
        [[evt[k]]]))


def ev_next_j(start: List[int], evt: List[int], S: List[int], mk: PSeq[int],
              j: int, K: int, nj: int) -> None:
    """Lemma: once the whole block of S[j] is covered, move on to j + 1."""
    # Why: read access to the input lists (the marks come in as a sequence).
    Requires(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
             and Acc(list_pred(S), 1 / 8))
    # Math: termination measure 1.
    Requires(MustTerminate(1))
    # Math: nj = j+1 ∧ j ∈ [0,|S|) ∧ S[j] ∈ [0,|start|-1) ∧ K = start[S[j]+1]
    # Why: K is the end of block(S[j]).
    Requires(nj == j + 1 and 0 <= j and j < len(S) and 0 <= S[j] and S[j] + 1 < len(start)
             and K == start[S[j] + 1])
    # Math: ev_complete_upto(mk, j, K)
    Requires(ev_complete_upto(start, evt, S, mk, j, K))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
            and Acc(list_pred(S), 1 / 8))
    # Math: ev_complete_upto(mk, j+1, 0)
    # Why: the same positions, described as "before (j+1, 0)".
    Ensures(ev_complete_upto(start, evt, S, mk, nj, 0))
    # Math: the body of ev_complete_upto(mk, nj, 0).
    # Why (hint): written out, so Nagini rechecks the quantifier.
    Assert(Forall(int, lambda kk: (Implies(
        0 <= kk and kk < len(evt),
        Forall(int, lambda jj: (Implies(
            in_block(start, evt, S, jj, kk) and (jj < nj or (jj == nj and kk < 0)),
            0 <= evt[kk] and evt[kk] < len(mk) and mk[evt[kk]] >= 0),
            [[in_block(start, evt, S, jj, kk)]]))),
        [[evt[kk]]])))


def ev_enter(start: List[int], evt: List[int], S: List[int], mk: PSeq[int],
             j: int) -> None:
    """Lemma: positions before block(S[j]) are not S[j]'s, so (j, 0) covers as much as
    (j, start[S[j]])."""
    # Why: read access to the input lists (the marks come in as a sequence).
    Requires(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
             and Acc(list_pred(S), 1 / 8))
    # Math: termination measure 1.
    Requires(MustTerminate(1))
    # Math: j ∈ [0,|S|) ∧ S[j] ∈ [0,|start|-1) ∧ 0 ≤ start[S[j]] ≤ T
    Requires(0 <= j and j < len(S) and 0 <= S[j] and S[j] + 1 < len(start)
             and 0 <= start[S[j]] and start[S[j]] <= len(evt))
    # Math: ev_complete_upto(mk, j, 0)
    Requires(ev_complete_upto(start, evt, S, mk, j, 0))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
            and Acc(list_pred(S), 1 / 8))
    # Math: j ∈ [0,|S|) ∧ S[j] ∈ [0,|start|-1)
    # Why: restated so start[S[j]] can be read in the postcondition below (post-state).
    Ensures(0 <= j and j < len(S) and 0 <= S[j] and S[j] + 1 < len(start))
    # Math: ev_complete_upto(mk, j, start[S[j]])
    Ensures(ev_complete_upto(start, evt, S, mk, j, start[S[j]]))
    lo = start[S[j]]
    # Math: ∀ t ∈ [0,lo): ¬in_block(j, t)
    # Why (hint): a position before block(S[j]) is not one of its transitions.
    Assert(Forall(int, lambda t: (Implies(0 <= t and t < lo,
                                          not in_block(start, evt, S, j, t)), [[evt[t]]])))
    # Math: the body of ev_complete_upto(mk, j, lo).
    # Why (hint): with the facts above, written out (as in ev_extend).
    Assert(Forall(int, lambda kk: (Implies(
        0 <= kk and kk < len(evt),
        Forall(int, lambda jj: (Implies(
            in_block(start, evt, S, jj, kk) and (jj < j or (jj == j and kk < lo)),
            0 <= evt[kk] and evt[kk] < len(mk) and mk[evt[kk]] >= 0),
            [[in_block(start, evt, S, jj, kk)]]))),
        [[evt[kk]]])))


def ev_run(start: List[int], evt: List[int], S: List[int], mk: PSeq[int],
           lo: int, hi: int, j: int, k: int, b: int, e: int) -> None:
    """Lemma: the run [k, b) of event e (found by upper_bound) is covered once e is marked."""
    # Why: read access to the input lists (the marks come in as a sequence).
    Requires(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
             and Acc(list_pred(S), 1 / 8))
    # Math: termination measure 1.
    Requires(MustTerminate(1))
    # Math: 0 ≤ lo ≤ k < hi ≤ T ∧ k ≤ b ≤ hi ∧ block_sorted(lo, hi)
    Requires(0 <= lo and lo <= k and k < hi and hi <= len(evt) and k <= b and b <= hi
             and block_sorted(lo, hi, evt))
    # Math: evt[k] = e ∧ e ∈ [0,|mk|) ∧ mk[e] ≥ 0
    # Why: the run starts at k with event e, which visit_event just marked.
    Requires(evt[k] == e and 0 <= e and e < len(mk) and mk[e] >= 0)
    # Math: ∀ t ∈ [k,b): evt[t] ≤ e   ∧   ∀ t ∈ [b,hi): evt[t] > e
    # Why: what upper_bound returned.
    Requires(Forall(int, lambda t: (Implies(k <= t and t < b, evt[t] <= e), [[evt[t]]])))
    Requires(Forall(int, lambda t: (Implies(b <= t and t < hi, evt[t] > e), [[evt[t]]])))
    # Math: ev_complete_upto(mk, j, k)
    Requires(ev_complete_upto(start, evt, S, mk, j, k))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
            and Acc(list_pred(S), 1 / 8))
    # Math: k < b ∧ ev_complete_upto(mk, j, b)
    # Why: the run is not empty (so the loop advances), and it is covered.
    Ensures(k < b and ev_complete_upto(start, evt, S, mk, j, b))
    # Math: ∀ t ∈ [k,b): evt[k] ≤ evt[t]
    # Why (hint): the block is sorted, so with evt[t] ≤ e = evt[k] every event in the run is e.
    Assert(Forall(int, lambda t: (Implies(k <= t and t < b, evt[k] <= evt[t]), [[evt[t]]])))
    # Math: ∀ t ∈ [k,b): evt[t] = e
    # Why (hint): e = evt[k] ≤ evt[t] ≤ e.
    Assert(Forall(int, lambda t: (Implies(k <= t and t < b, evt[t] == e), [[evt[t]]])))
    # Math: ∀ t ∈ [k,b): mk[evt[t]] ≥ 0
    # Why (hint): every event of the run is e, and mk[e] ≥ 0: what ev_extend needs.
    Assert(Forall(int, lambda t: (Implies(k <= t and t < b,
                                          0 <= evt[t] and evt[t] < len(mk) and mk[evt[t]] >= 0),
                                  [[evt[t]]])))
    # Math: k < b
    # Why (hint): evt[k] = e is not > e, so b ≠ k.
    Assert(k < b)
    # Math: the body of ev_complete_upto(mk, j, b).
    # Why (hint): with the facts above, written out (as in ev_extend).
    Assert(Forall(int, lambda kk: (Implies(
        0 <= kk and kk < len(evt),
        Forall(int, lambda jj: (Implies(
            in_block(start, evt, S, jj, kk) and (jj < j or (jj == j and kk < b)),
            0 <= evt[kk] and evt[kk] < len(mk) and mk[evt[kk]] >= 0),
            [[in_block(start, evt, S, jj, kk)]]))),
        [[evt[kk]]])))


def visit_event(start: List[int], evt: List[int], S: List[int], m: int, emark: List[int],
                out: List[int], src: List[int], via: List[int], j: int, k: int) -> None:
    """Transition k is a transition of S[j]: add its event to the result unless it is marked."""
    # Why: read access to the inputs (a small share: the caller's share keeps them unchanged).
    Requires(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
             and Acc(list_pred(S), 1 / 8))
    # Why: write access to emark and the three result lists.
    Requires(Acc(list_pred(emark)) and Acc(list_pred(out)) and Acc(list_pred(src))
             and Acc(list_pred(via)))
    # Math: termination measure 2 (calls append).
    Requires(MustTerminate(2))
    # Math: |src| = |out| ∧ |via| = |out| ∧ |emark| = m
    Requires(len(src) == len(out) and len(via) == len(out) and len(emark) == m)
    # Math: in_block(j, k) ∧ evt[k] ∈ [0,m)
    # Why: k is a transition of S[j], on an event number (target_of gives the range).
    Requires(in_block(start, evt, S, j, k) and 0 <= evt[k] and evt[k] < m)
    # Math: marks_ok(emark, out) ∧ ev_sound(out, src, via) ∧ ev_complete_upto(emark, j, k)
    # Why: the loop invariants of active_events, at this point of the loop.
    Requires(marks_ok(ToSeq(emark), ToSeq(out)))
    Requires(ev_sound(start, evt, S, ToSeq(out), ToSeq(src), ToSeq(via)))
    Requires(ev_complete_upto(start, evt, S, ToSeq(emark), j, k))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
            and Acc(list_pred(S), 1 / 8))
    Ensures(Acc(list_pred(emark)) and Acc(list_pred(out)) and Acc(list_pred(src))
            and Acc(list_pred(via)))
    # Math: |src| = |out| ∧ |via| = |out| ∧ |emark| = m ∧ k < T ∧ evt[k] ∈ [0,m)
    Ensures(len(src) == len(out) and len(via) == len(out) and len(emark) == m
            and k < len(evt) and 0 <= evt[k] and evt[k] < m)
    # Math: the invariants still hold, and emark[evt[k]] ≥ 0
    # Why: the event of k is now in the result; the covered part is unchanged (marks only
    #      went from -1 to a position).
    Ensures(marks_ok(ToSeq(emark), ToSeq(out)))
    Ensures(ev_sound(start, evt, S, ToSeq(out), ToSeq(src), ToSeq(via)))
    Ensures(ev_complete_upto(start, evt, S, ToSeq(emark), j, k))
    Ensures(ToSeq(emark)[evt[k]] >= 0)
    e = evt[k]                       # the event of transition k
    if emark[e] == -1:               # not in the result yet
        i = len(out)                 # the position e will have
        out.append(e)                # add e ...
        src.append(j)                # ... occurring at S[j] (witness)
        via.append(k)                # ... by transition k (witness)
        emark[e] = i                 # remember e's position
        # Math: ∀ t ∈ [0,i): out[t] = out_old[t] ∧ src[t] = src_old[t] ∧ via[t] = via_old[t]
        # Why (hint): the appends keep the old entries.
        Assert(Forall(int, lambda t: (Implies(0 <= t and t < i,
                                              ToSeq(out)[t] == Old(ToSeq(out))[t]
                                              and ToSeq(src)[t] == Old(ToSeq(src))[t]
                                              and ToSeq(via)[t] == Old(ToSeq(via))[t]),
                                      [[ToSeq(out)[t]]])))
        # Math: ∀ z ∈ [0,m), z ≠ e: emark[z] = emark_old[z]
        # Why (hint): the write changed only emark[e].
        Assert(Forall(int, lambda z: (Implies(0 <= z and z < len(emark) and z != e,
                                              ToSeq(emark)[z] == Old(ToSeq(emark))[z]),
                                      [[ToSeq(emark)[z]]])))
        # Math: out[i] = e ∧ src[i] = j ∧ via[i] = k ∧ emark[e] = i ∧ ev_at(j, k, e)
        # Why (hint): the new entries are what we just wrote, and they are a real occurrence.
        Assert(ToSeq(out)[i] == e and ToSeq(src)[i] == j and ToSeq(via)[i] == k
               and ToSeq(emark)[e] == i)
        Assert(ev_at(start, evt, S, j, k, e))
    # (else: e is already in the result; nothing to write.)
    # Hints: the bodies of the postconditions, written out (as in visit).
    # Math: ∀ t ∈ [0,|out|): out[t] ∈ [0,m) ∧ emark[out[t]] = t              (marks_ok, part 1)
    Assert(Forall(int, lambda t: (Implies(0 <= t and t < len(out),
                                          0 <= ToSeq(out)[t] and ToSeq(out)[t] < len(emark)
                                          and ToSeq(emark)[ToSeq(out)[t]] == t),
                                  [[ToSeq(out)[t]]])))
    # Math: ∀ z ∈ [0,m): emark[z] ≠ -1 → emark[z] ∈ [0,|out|) ∧ out[emark[z]] = z  (part 2)
    Assert(Forall(int, lambda z: (Implies(0 <= z and z < len(emark) and ToSeq(emark)[z] != -1,
                                          0 <= ToSeq(emark)[z] and ToSeq(emark)[z] < len(out)
                                          and ToSeq(out)[ToSeq(emark)[z]] == z),
                                  [[ToSeq(emark)[z]]])))
    # Math: ∀ t ∈ [0,|out|): ev_at(src[t], via[t], out[t])                    (ev_sound)
    Assert(Forall(int, lambda t: (Implies(0 <= t and t < len(out),
                                          ev_at(start, evt, S, ToSeq(src)[t], ToSeq(via)[t],
                                                ToSeq(out)[t])),
                                  [[ToSeq(out)[t]]])))
    # Math: ev_complete_upto(emark, j, k)                (marks only grew: still covered)
    Assert(Forall(int, lambda kk: (Implies(
        0 <= kk and kk < len(evt),
        Forall(int, lambda jj: (Implies(
            in_block(start, evt, S, jj, kk) and (jj < j or (jj == j and kk < k)),
            0 <= evt[kk] and evt[kk] < len(emark) and ToSeq(emark)[evt[kk]] >= 0),
            [[in_block(start, evt, S, jj, kk)]]))),
        [[evt[kk]]])))


def block_events(n: int, m: int, start: List[int], evt: List[int], dst: List[int],
                 in_E: List[bool], x: int) -> None:
    """Lemma: every transition in the block of a state has an event number."""
    # Why: read access.
    Requires(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
             and Acc(list_pred(dst), 1 / 8) and Acc(list_pred(in_E), 1 / 8))
    # Math: termination measure 1.
    Requires(MustTerminate(1))
    # Math: input_ok ∧ x ∈ [0,n)
    Requires(input_ok(n, m, start, evt, dst, in_E) and 0 <= x and x < n)
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
            and Acc(list_pred(dst), 1 / 8) and Acc(list_pred(in_E), 1 / 8))
    # Math: |start| = n+1 ∧ 0 ≤ start[x] ≤ start[x+1] ≤ T ∧ block_sorted(start[x], start[x+1])
    Ensures(len(start) == n + 1 and 0 <= start[x] and start[x] <= start[x + 1]
            and start[x + 1] <= len(evt) and block_sorted(start[x], start[x + 1], evt))
    # Math: ∀ t ∈ block(x): evt[t] ∈ [0,m)
    # Why: so the scan of the block does not need input_ok (a large predicate) in its loop.
    Ensures(Forall(int, lambda t: (Implies(start[x] <= t and t < start[x + 1],
                                           0 <= evt[t] and evt[t] < m), [[evt[t]]])))
    # Math: start[x+1] ≤ T ∧ block_sorted(...)
    # Why (hint): triggers blocks_ok's and sorted_ok's quantifiers at x.
    Assert(start[x + 1] <= len(evt))
    Assert(block_sorted(start[x], start[x + 1], evt))
    # Math: ∀ t ∈ block(x): evt[t] ∈ [0,m)
    # Why (hint): transitions_ok at every t of the block.
    Assert(Forall(int, lambda t: (Implies(start[x] <= t and t < start[x + 1],
                                          0 <= evt[t] and evt[t] < m), [[evt[t]]])))


def ev_scan(n: int, m: int, start: List[int], evt: List[int], dst: List[int], in_E: List[bool],
            S: List[int], emark: List[int], out: List[int], src: List[int], via: List[int],
            j: int) -> None:
    """Cover the block of the state S[j]: add the event of each run, jumping past the run."""
    # Why: read access (1/4: the caller keeps 1/4, so the inputs are known unchanged after).
    Requires(Acc(list_pred(start), 1 / 4) and Acc(list_pred(evt), 1 / 4)
             and Acc(list_pred(dst), 1 / 4) and Acc(list_pred(in_E), 1 / 4)
             and Acc(list_pred(S), 1 / 4))
    # Why: write access to emark and the three result lists.
    Requires(Acc(list_pred(emark)) and Acc(list_pred(out)) and Acc(list_pred(src))
             and Acc(list_pred(via)))
    # Math: termination measure 4 (calls ev_enter, measure 2).
    Requires(MustTerminate(4))
    # Math: input_ok ∧ ∀ j' ∈ [0,|S|): S[j'] ∈ [0,n) ∧ j ∈ [0,|S|)
    Requires(input_ok(n, m, start, evt, dst, in_E))
    Requires(Forall(int, lambda jj: (Implies(0 <= jj and jj < len(S),
                                             0 <= S[jj] and S[jj] < n), [[S[jj]]])))
    Requires(0 <= j and j < len(S))
    # Math: sizes ∧ marks_ok(emark, out) ∧ ev_sound(out, src, via) ∧ ev_complete_upto(emark, j, 0)
    # Why: the outer loop's invariants at the start of S[j].
    Requires(len(emark) == m and len(src) == len(out) and len(via) == len(out))
    Requires(marks_ok(ToSeq(emark), ToSeq(out)))
    Requires(ev_sound(start, evt, S, ToSeq(out), ToSeq(src), ToSeq(via)))
    Requires(ev_complete_upto(start, evt, S, ToSeq(emark), j, 0))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 4) and Acc(list_pred(evt), 1 / 4)
            and Acc(list_pred(dst), 1 / 4) and Acc(list_pred(in_E), 1 / 4)
            and Acc(list_pred(S), 1 / 4))
    Ensures(Acc(list_pred(emark)) and Acc(list_pred(out)) and Acc(list_pred(src))
            and Acc(list_pred(via)))
    # Math: j ∈ [0,|S|) ∧ S[j] ∈ [0,|start|-1)
    # Why: so start[S[j] + 1] can be read below. (input_ok is not restated: the caller keeps a
    #      share of the lists, so it still holds there.)
    Ensures(0 <= j and j < len(S) and 0 <= S[j] and S[j] + 1 < len(start))
    # Math: sizes ∧ marks_ok ∧ ev_sound ∧ ev_complete_upto(emark, j, start[S[j]+1])
    # Why: the whole block of S[j] is now covered.
    Ensures(len(emark) == m and len(src) == len(out) and len(via) == len(out))
    Ensures(marks_ok(ToSeq(emark), ToSeq(out)))
    Ensures(ev_sound(start, evt, S, ToSeq(out), ToSeq(src), ToSeq(via)))
    Ensures(ev_complete_upto(start, evt, S, ToSeq(emark), j, start[S[j] + 1]))
    x = S[j]                                 # the current state
    block_events(n, m, start, evt, dst, in_E, x)   # lemma: block(x) valid, sorted, events < m
    lo = start[x]                            # first transition of x
    hi = start[x + 1]                        # one past its last transition
    ev_enter(start, evt, S, ToSeq(emark), j)          # lemma: covered up to (j, lo)
    k = lo
    while k < hi:                            # for each run of one event in block(x)
        # Why: permissions (input_ok is not carried: the facts needed are below).
        Invariant(Acc(list_pred(start), 1 / 4) and Acc(list_pred(evt), 1 / 4)
                  and Acc(list_pred(dst), 1 / 4) and Acc(list_pred(in_E), 1 / 4)
                  and Acc(list_pred(S), 1 / 4))
        Invariant(Acc(list_pred(emark)) and Acc(list_pred(out)) and Acc(list_pred(src))
                  and Acc(list_pred(via)))
        # Math: measure hi - k + 3, decreasing (each run is non-empty).
        Invariant(MustTerminate(hi - k + 3))
        # Math: start, evt, S unchanged.
        Invariant(ToSeq(start) == Old(ToSeq(start)) and ToSeq(evt) == Old(ToSeq(evt))
                  and ToSeq(S) == Old(ToSeq(S)))
        # Math: ∀ t ∈ [lo,hi): evt[t] ∈ [0,m)
        # Why: from block_events; replaces input_ok and target_of in the loop.
        Invariant(Forall(int, lambda t: (Implies(lo <= t and t < hi, 0 <= evt[t] and evt[t] < m),
                                         [[evt[t]]])))
        # Math: j ∈ [0,|S|) ∧ x = S[j] ∈ [0,n) ∧ |start| = n+1
        Invariant(0 <= j and j < len(S) and x == S[j] and 0 <= x and x < n)
        Invariant(len(start) == n + 1)
        # Math: lo = start[x] ≤ k ≤ hi = start[x+1] ≤ T ∧ block_sorted(lo, hi)
        # Why: k runs over block(x), which is sorted (for the run jumps).
        Invariant(lo == start[x] and hi == start[x + 1] and lo <= k and k <= hi
                  and hi <= len(evt) and block_sorted(lo, hi, evt))
        # Math: sizes; marks_ok; ev_sound; ev_complete_upto(emark, j, k)
        Invariant(len(emark) == m and len(src) == len(out) and len(via) == len(out))
        Invariant(marks_ok(ToSeq(emark), ToSeq(out)))
        Invariant(ev_sound(start, evt, S, ToSeq(out), ToSeq(src), ToSeq(via)))
        Invariant(ev_complete_upto(start, evt, S, ToSeq(emark), j, k))
        e = evt[k]                                                # the event of this run
        visit_event(start, evt, S, m, emark, out, src, via, j, k)  # add e if new
        b = upper_bound(evt, lo, hi, k, e)                        # one past the e-run
        ev_run(start, evt, S, ToSeq(emark), lo, hi, j, k, b, e)           # lemma: run covered, k < b
        k = b


def active_events(n: int, m: int, start: List[int], evt: List[int], dst: List[int],
                  in_E: List[bool], S: List[int], emark: List[int], out: List[int],
                  src: List[int], via: List[int]) -> None:
    """The events enabled at some state of S (event numbers).

    The caller passes `emark`, m entries all -1 (cost m, the alphabet size), and three empty
    lists. On return: out lists the enabled events, each once; event out[i] is the event of
    transition via[i] of the state S[src[i]]; emark[e] is the position of e in out, or -1
    (emark[e] ≥ 0 ⟺ e is enabled at some state of S).

    Proved (spec: basic_ops.md §2):
    - in range: every entry of out is an event number;
    - no duplicates (marks_ok);
    - sound: every entry of out occurs at a state of S (the witnesses src, via);
    - complete: the event of every transition of every state of S is marked, hence in out.
    Together: the set of entries of out = active f S (Lean)."""
    # Why: read access to the automaton and to S.
    Requires(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2)
             and Acc(list_pred(dst), 1 / 2) and Acc(list_pred(in_E), 1 / 2)
             and Acc(list_pred(S), 1 / 2))
    # Why: write access to emark and the three outputs.
    Requires(Acc(list_pred(emark)) and Acc(list_pred(out)) and Acc(list_pred(src))
             and Acc(list_pred(via)))
    # Math: termination, measure |S| + T + 6.
    Requires(MustTerminate(len(S) + 8))
    # Math: input_ok
    # Why: a well-formed (validated) automaton, blocks sorted.
    Requires(input_ok(n, m, start, evt, dst, in_E))
    # Math: ∀ j ∈ [0,|S|): S[j] ∈ [0,n)
    # Why: "states in range". Repeats are allowed.
    Requires(Forall(int, lambda j: (Implies(0 <= j and j < len(S), 0 <= S[j] and S[j] < n),
                                    [[S[j]]])))
    # Math: |emark| = m ∧ ∀ e ∈ [0,m): emark[e] = -1 ∧ |out| = |src| = |via| = 0
    # Why: nothing marked yet; the result lists start empty.
    Requires(len(emark) == m and all_clear(ToSeq(emark)))
    Requires(len(out) == 0 and len(src) == 0 and len(via) == 0)
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2)
            and Acc(list_pred(dst), 1 / 2) and Acc(list_pred(in_E), 1 / 2)
            and Acc(list_pred(S), 1 / 2))
    Ensures(Acc(list_pred(emark)) and Acc(list_pred(out)) and Acc(list_pred(src))
            and Acc(list_pred(via)))
    # Math: input_ok ∧ |emark| = m ∧ |src| = |out| ∧ |via| = |out|
    Ensures(input_ok(n, m, start, evt, dst, in_E))
    Ensures(len(emark) == m and len(src) == len(out) and len(via) == len(out))
    # THE RESULT.
    # Math: ∀ i: out[i] ∈ [0,m)                                         (in range)
    # Math: ∀ i: emark[out[i]] = i;  ∀ e: emark[e] ≠ -1 → out[emark[e]] = e   (no duplicates)
    Ensures(marks_ok(ToSeq(emark), ToSeq(out)))
    # Math: ∀ i: ev_at(src[i], via[i], out[i]), i.e. S[src[i]] has transition via[i] on out[i]
    Ensures(ev_sound(start, evt, S, ToSeq(out), ToSeq(src), ToSeq(via)))
    # Math: ∀ j ∈ [0,|S|). ∀ k ∈ block(S[j]): emark[evt[k]] ≥ 0          (complete)
    Ensures(ev_complete_upto(start, evt, S, ToSeq(emark), len(S), 0))
    # Math: ∀ e ∈ [0,|emark|): emark[e] = -1
    # Why (hint): all_clear written out, so that marks_ok holds before the loop (empty result).
    Assert(Forall(int, lambda y: (Implies(0 <= y and y < len(emark), ToSeq(emark)[y] == -1),
                                  [[ToSeq(emark)[y]]])))
    j = 0                                        # position in S
    while j < len(S):                            # for each state of S
        # Why: the loop keeps its permissions.
        Invariant(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2)
                  and Acc(list_pred(dst), 1 / 2) and Acc(list_pred(in_E), 1 / 2)
                  and Acc(list_pred(S), 1 / 2))
        Invariant(Acc(list_pred(emark)) and Acc(list_pred(out)) and Acc(list_pred(src))
                  and Acc(list_pred(via)))
        # Math: measure |S| - j + 4, decreasing.
        Invariant(MustTerminate(len(S) - j + 6))
        # Math: the input lists are unchanged.
        # Why: a loop forgets list contents unless told they don't change.
        Invariant(ToSeq(start) == Old(ToSeq(start)) and ToSeq(evt) == Old(ToSeq(evt))
                  and ToSeq(dst) == Old(ToSeq(dst)) and ToSeq(in_E) == Old(ToSeq(in_E))
                  and ToSeq(S) == Old(ToSeq(S)))
        # Math: input_ok ∧ ∀ j' ∈ [0,|S|): S[j'] ∈ [0,n) ∧ 0 ≤ j ≤ |S|
        Invariant(input_ok(n, m, start, evt, dst, in_E))
        Invariant(Forall(int, lambda jj: (Implies(0 <= jj and jj < len(S),
                                                  0 <= S[jj] and S[jj] < n), [[S[jj]]])))
        Invariant(0 <= j and j <= len(S))
        # Math: sizes; marks_ok; ev_sound; ev_complete_upto(emark, j, 0)
        # Why: the result so far is consistent (hence in range), sound, and covers S[0 .. j-1].
        Invariant(len(emark) == m and len(src) == len(out) and len(via) == len(out))
        Invariant(marks_ok(ToSeq(emark), ToSeq(out)))
        Invariant(ev_sound(start, evt, S, ToSeq(out), ToSeq(src), ToSeq(via)))
        Invariant(ev_complete_upto(start, evt, S, ToSeq(emark), j, 0))
        ev_scan(n, m, start, evt, dst, in_E, S, emark, out, src, via, j)   # cover block(S[j])
        ev_next_j(start, evt, S, ToSeq(emark), j, start[S[j] + 1], j + 1)  # lemma: next j
        j += 1


# --- active_events over the index -------------------------------------------------------------
# The same operation and the same guarantees as active_events, but the runs of each block come
# from the active-event index (A, H) of the automaton, checked once by check_index, instead of a
# binary search per run: the run of head i ends at nxt(i) (H[i+1], or the end of the block).
# Notation: for x = S[j], lo = start[x], hi = start[x+1], a0 = A[x], a1 = A[x+1].


@Pure
def runs_ok(evt: List[int], H: List[int], lo: int, hi: int, a0: int, a1: int) -> bool:
    """Every head of the state is correct (the part of seg_ok the scan needs)."""
    # Why: read access.
    Requires(Acc(list_pred(evt), 1 / 8) and Acc(list_pred(H), 1 / 8))
    # Math: 0 ≤ a0 ≤ a1 ≤ |H|
    Requires(0 <= a0 and a0 <= a1 and a1 <= len(H))
    # Math: ∀ i ∈ [a0,a1): run_ok(lo, hi, a1, i)
    # Why: seg_ok without its pairwise part (increasing events), which the scan does not use;
    #      a lighter loop invariant (with seg_ok in the loop, Nagini ran over 15 minutes).
    return Forall(int, lambda i: (Implies(a0 <= i and i < a1, run_ok(evt, H, lo, hi, a1, i)),
                                  [[run_ok(evt, H, lo, hi, a1, i)]]))


def seg_runs(evt: List[int], H: List[int], lo: int, hi: int, a0: int, a1: int) -> None:
    """Lemma: seg_ok gives the facts the scan of one block needs."""
    # Why: read access (1/8: the caller keeps a share).
    Requires(Acc(list_pred(evt), 1 / 8) and Acc(list_pred(H), 1 / 8))
    # Math: termination measure 1.
    Requires(MustTerminate(1))
    # Math: 0 ≤ a0 ≤ a1 ≤ |H| ∧ seg_ok(lo, hi, a0, a1)
    Requires(0 <= a0 and a0 <= a1 and a1 <= len(H) and seg_ok(evt, H, lo, hi, a0, a1))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(evt), 1 / 8) and Acc(list_pred(H), 1 / 8))
    # Math: 0 ≤ a0 ≤ a1 ≤ |H| ∧ (a0 = a1 ⟺ lo = hi) ∧ (a0 < a1 → H[a0] = lo) ∧ runs_ok(lo, hi, a0, a1)
    # Why: where the scan starts (k = lo = H[a0]), and each head's run.
    Ensures(0 <= a0 and a0 <= a1 and a1 <= len(H))
    Ensures((a0 == a1) == (lo == hi) and Implies(a0 < a1, H[a0] == lo)
            and runs_ok(evt, H, lo, hi, a0, a1))


def ev_run_idx(start: List[int], evt: List[int], S: List[int], H: List[int], mk: PSeq[int],
               lo: int, hi: int, a1: int, i: int, j: int, k: int, b: int, e: int) -> None:
    """Lemma: the run of head i (positions k = H[i] .. b-1) is covered once its event is marked."""
    # Why: read access (1/8: the caller keeps a share).
    Requires(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
             and Acc(list_pred(S), 1 / 8) and Acc(list_pred(H), 1 / 8))
    # Math: termination measure 1.
    Requires(MustTerminate(1))
    # Math: 0 ≤ i < a1 ≤ |H| ∧ run_ok(lo, hi, a1, i) ∧ k = H[i] ∧ b = nxt(i)
    # Why: head i is correct (from the index), and [k, b) is its run.
    Requires(0 <= i and i < a1 and a1 <= len(H) and run_ok(evt, H, lo, hi, a1, i))
    Requires(k == H[i] and b == nxt(H, hi, a1, i))
    # Math: evt[k] = e ∧ e ∈ [0,|mk|) ∧ mk[e] ≥ 0 ∧ ev_complete_upto(mk, j, k)
    # Why: visit_event just marked the run's event; everything before k is covered.
    Requires(evt[k] == e and 0 <= e and e < len(mk) and mk[e] >= 0)
    Requires(ev_complete_upto(start, evt, S, mk, j, k))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 8) and Acc(list_pred(evt), 1 / 8)
            and Acc(list_pred(S), 1 / 8) and Acc(list_pred(H), 1 / 8))
    # Math: k < b ≤ hi ∧ ev_complete_upto(mk, j, b)
    # Why: the loop advances and stays in the block; the run is covered.
    Ensures(k < b and b <= hi and ev_complete_upto(start, evt, S, mk, j, b))
    # Math: ∀ t ∈ [k,b): evt[t] = e
    # Why (hint): run_ok: the run is constant, on evt[H[i]] = evt[k] = e.
    Assert(Forall(int, lambda t: (Implies(k <= t and t < b, evt[t] == e), [[evt[t]]])))
    # Math: ∀ t ∈ [k,b): mk[evt[t]] ≥ 0
    # Why (hint): every event of the run is e, which is marked.
    Assert(Forall(int, lambda t: (Implies(k <= t and t < b,
                                          0 <= evt[t] and evt[t] < len(mk) and mk[evt[t]] >= 0),
                                  [[evt[t]]])))
    # Math: the body of ev_complete_upto(mk, j, b).
    # Why (hint): with the facts above, written out (as in ev_run).
    Assert(Forall(int, lambda kk: (Implies(
        0 <= kk and kk < len(evt),
        Forall(int, lambda jj: (Implies(
            in_block(start, evt, S, jj, kk) and (jj < j or (jj == j and kk < b)),
            0 <= evt[kk] and evt[kk] < len(mk) and mk[evt[kk]] >= 0),
            [[in_block(start, evt, S, jj, kk)]]))),
        [[evt[kk]]])))


def ev_scan_idx(n: int, m: int, start: List[int], evt: List[int], dst: List[int],
                in_E: List[bool], A: List[int], H: List[int], S: List[int], emark: List[int],
                out: List[int], src: List[int], via: List[int], j: int,
                lo: int, hi: int, a0: int, a1: int) -> None:
    """Cover the block [lo, hi) of the state S[j]: add the event of each head of S[j] (heads
    a0 .. a1-1 of the index)."""
    # Why: read access (1/4: the caller keeps 1/4, so the inputs are known unchanged after).
    Requires(Acc(list_pred(start), 1 / 4) and Acc(list_pred(evt), 1 / 4)
             and Acc(list_pred(dst), 1 / 4) and Acc(list_pred(in_E), 1 / 4)
             and Acc(list_pred(S), 1 / 4) and Acc(list_pred(A), 1 / 4)
             and Acc(list_pred(H), 1 / 4))
    # Why: write access to emark and the three result lists.
    Requires(Acc(list_pred(emark)) and Acc(list_pred(out)) and Acc(list_pred(src))
             and Acc(list_pred(via)))
    # Math: termination measure 4 (calls visit_event, measure 2).
    Requires(MustTerminate(4))
    # Math: input_ok ∧ ∀ j' ∈ [0,|S|): S[j'] ∈ [0,n) ∧ j ∈ [0,|S|) ∧ |A| = n+1
    Requires(input_ok(n, m, start, evt, dst, in_E))
    Requires(Forall(int, lambda jj: (Implies(0 <= jj and jj < len(S),
                                             0 <= S[jj] and S[jj] < n), [[S[jj]]])))
    Requires(0 <= j and j < len(S) and len(A) == n + 1)
    # Math: lo = start[S[j]] ∧ hi = start[S[j]+1] ∧ a0 = A[S[j]] ∧ a1 = A[S[j]+1]
    # Why: the block and the heads of S[j], read by the caller.
    Requires(0 <= S[j] and S[j] < n and lo == start[S[j]] and hi == start[S[j] + 1]
             and a0 == A[S[j]] and a1 == A[S[j] + 1])
    # Math: 0 ≤ a0 ≤ a1 ≤ |H| ∧ (a0 = a1 ⟺ lo = hi) ∧ (a0 < a1 → H[a0] = lo) ∧ runs_ok(lo, hi, a0, a1)
    # Why: the index is correct for S[j] (seg_runs applied by the caller to index_ok at S[j]).
    #      Not seg_ok itself: its pairwise part, unfolded here, made the proof time out.
    Requires(0 <= a0 and a0 <= a1 and a1 <= len(H))
    Requires((a0 == a1) == (lo == hi) and Implies(a0 < a1, H[a0] == lo)
             and runs_ok(evt, H, lo, hi, a0, a1))
    # Math: sizes ∧ marks_ok(emark, out) ∧ ev_sound(out, src, via) ∧ ev_complete_upto(emark, j, 0)
    # Why: the outer loop's invariants at the start of S[j].
    Requires(len(emark) == m and len(src) == len(out) and len(via) == len(out))
    Requires(marks_ok(ToSeq(emark), ToSeq(out)))
    Requires(ev_sound(start, evt, S, ToSeq(out), ToSeq(src), ToSeq(via)))
    Requires(ev_complete_upto(start, evt, S, ToSeq(emark), j, 0))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 4) and Acc(list_pred(evt), 1 / 4)
            and Acc(list_pred(dst), 1 / 4) and Acc(list_pred(in_E), 1 / 4)
            and Acc(list_pred(S), 1 / 4) and Acc(list_pred(A), 1 / 4)
            and Acc(list_pred(H), 1 / 4))
    Ensures(Acc(list_pred(emark)) and Acc(list_pred(out)) and Acc(list_pred(src))
            and Acc(list_pred(via)))
    # Math: j ∈ [0,|S|) ∧ S[j] ∈ [0,|start|-1)
    # Why: so start[S[j] + 1] can be read below (post-state).
    Ensures(0 <= j and j < len(S) and 0 <= S[j] and S[j] + 1 < len(start))
    # Math: sizes ∧ marks_ok ∧ ev_sound ∧ ev_complete_upto(emark, j, start[S[j]+1])
    # Why: the whole block of S[j] is now covered.
    Ensures(len(emark) == m and len(src) == len(out) and len(via) == len(out))
    Ensures(marks_ok(ToSeq(emark), ToSeq(out)))
    Ensures(ev_sound(start, evt, S, ToSeq(out), ToSeq(src), ToSeq(via)))
    Ensures(ev_complete_upto(start, evt, S, ToSeq(emark), j, start[S[j] + 1]))
    x = S[j]                                 # the current state
    block_events(n, m, start, evt, dst, in_E, x)   # lemma: block(x) valid, events < m
    ev_enter(start, evt, S, ToSeq(emark), j)          # lemma: covered up to (j, lo)
    i = a0                                   # current head
    k = lo                                   # its position: H[i] (or hi once i = a1)
    while i < a1:                            # for each head of x: one run, one event
        # Why: permissions (input_ok is not carried: the facts needed are below).
        Invariant(Acc(list_pred(start), 1 / 4) and Acc(list_pred(evt), 1 / 4)
                  and Acc(list_pred(dst), 1 / 4) and Acc(list_pred(in_E), 1 / 4)
                  and Acc(list_pred(S), 1 / 4) and Acc(list_pred(A), 1 / 4)
                  and Acc(list_pred(H), 1 / 4))
        Invariant(Acc(list_pred(emark)) and Acc(list_pred(out)) and Acc(list_pred(src))
                  and Acc(list_pred(via)))
        # Math: measure a1 - i + 3, decreasing.
        Invariant(MustTerminate(a1 - i + 3))
        # Math: start, evt, S, H unchanged.
        Invariant(ToSeq(start) == Old(ToSeq(start)) and ToSeq(evt) == Old(ToSeq(evt))
                  and ToSeq(S) == Old(ToSeq(S)) and ToSeq(H) == Old(ToSeq(H)))
        # Math: ∀ t ∈ [lo,hi): evt[t] ∈ [0,m)
        # Why: from block_events; replaces input_ok in the loop.
        Invariant(Forall(int, lambda t: (Implies(lo <= t and t < hi, 0 <= evt[t] and evt[t] < m),
                                         [[evt[t]]])))
        # Math: j ∈ [0,|S|) ∧ x = S[j] ∈ [0,n) ∧ |start| = n+1 ∧ lo = start[x] ∧ hi = start[x+1]
        #       ∧ 0 ≤ lo ∧ hi ≤ T
        # Why: the block is a valid range of positions (so evt[k] can be read).
        Invariant(0 <= j and j < len(S) and x == S[j] and 0 <= x and x < n)
        Invariant(len(start) == n + 1 and lo == start[x] and hi == start[x + 1]
                  and 0 <= lo and hi <= len(evt))
        # Math: 0 ≤ a0 ≤ i ≤ a1 ≤ |H| ∧ runs_ok(lo, hi, a0, a1)
        Invariant(0 <= a0 and a0 <= i and i <= a1 and a1 <= len(H)
                  and runs_ok(evt, H, lo, hi, a0, a1))
        # Math: lo ≤ k ≤ hi ∧ (i < a1 → k = H[i]) ∧ (i = a1 → k = hi)
        # Why: k is where the current run starts; after the last head, the end of the block.
        Invariant(lo <= k and k <= hi and Implies(i < a1, k == H[i]) and Implies(i == a1, k == hi))
        # Math: sizes; marks_ok; ev_sound; ev_complete_upto(emark, j, k)
        Invariant(len(emark) == m and len(src) == len(out) and len(via) == len(out))
        Invariant(marks_ok(ToSeq(emark), ToSeq(out)))
        Invariant(ev_sound(start, evt, S, ToSeq(out), ToSeq(src), ToSeq(via)))
        Invariant(ev_complete_upto(start, evt, S, ToSeq(emark), j, k))
        # Math: run_ok(lo, hi, a1, i)
        # Why (hint): runs_ok at head i.
        Assert(run_ok(evt, H, lo, hi, a1, i))
        # Math: k = H[i] < nxt(i) ≤ hi
        # Why (hint): from run_ok, so k is a position of the block (evt[k] can be read).
        Assert(H[i] < nxt(H, hi, a1, i) and nxt(H, hi, a1, i) <= hi)
        e = evt[k]                                                # the event of this run
        visit_event(start, evt, S, m, emark, out, src, via, j, k)  # add e if new
        if i + 1 < a1:                       # b = nxt(i): one past the run
            b = H[i + 1]                     # the next head
        else:
            b = hi                           # the end of the block (last head)
        # Math: b = nxt(i)
        # Why (hint): joins the two branches into one fact (the rest of the proof has one path).
        Assert(b == nxt(H, hi, a1, i))
        ev_run_idx(start, evt, S, H, ToSeq(emark), lo, hi, a1, i, j, k, b, e)  # lemma: run covered
        k = b
        ni = i + 1
        i = ni


def active_events_idx(n: int, m: int, start: List[int], evt: List[int], dst: List[int],
                      in_E: List[bool], A: List[int], H: List[int], S: List[int],
                      emark: List[int], out: List[int], src: List[int], via: List[int]) -> None:
    """active_events, reading the runs from the active-event index (A, H).

    Same inputs and outputs as active_events, plus the index, which must be correct (index_ok,
    as check_index guarantees). Proved: the same four properties (spec: basic_ops.md §3)."""
    # Why: read access to the automaton, the index and S.
    Requires(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2)
             and Acc(list_pred(dst), 1 / 2) and Acc(list_pred(in_E), 1 / 2)
             and Acc(list_pred(A), 1 / 2) and Acc(list_pred(H), 1 / 2)
             and Acc(list_pred(S), 1 / 2))
    # Why: write access to emark and the three outputs.
    Requires(Acc(list_pred(emark)) and Acc(list_pred(out)) and Acc(list_pred(src))
             and Acc(list_pred(via)))
    # Math: termination measure |S| + 8.
    Requires(MustTerminate(len(S) + 8))
    # Math: input_ok
    Requires(input_ok(n, m, start, evt, dst, in_E))
    # Math: index_ok(n, start, evt, A, H) (active_index.py), the parts used: |A| = n+1 and
    #       ∀ y ∈ [0,n): 0 ≤ A[y] ≤ A[y+1] ≤ |H| ∧ seg_ok(start[y], start[y+1], A[y], A[y+1])
    # Why: the index is correct (what check_index guarantees).
    Requires(len(A) == n + 1 and len(start) == n + 1)
    Requires(Forall(int, lambda y: (
        Implies(0 <= y and y < n,
                0 <= A[y] and A[y] <= A[y + 1] and A[y + 1] <= len(H)
                and seg_ok(evt, H, start[y], start[y + 1], A[y], A[y + 1])),
        [[A[y + 1]]])))
    # Math: ∀ j ∈ [0,|S|): S[j] ∈ [0,n)
    Requires(Forall(int, lambda j: (Implies(0 <= j and j < len(S), 0 <= S[j] and S[j] < n),
                                    [[S[j]]])))
    # Math: |emark| = m ∧ ∀ e ∈ [0,m): emark[e] = -1 ∧ |out| = |src| = |via| = 0
    Requires(len(emark) == m and all_clear(ToSeq(emark)))
    Requires(len(out) == 0 and len(src) == 0 and len(via) == 0)
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2)
            and Acc(list_pred(dst), 1 / 2) and Acc(list_pred(in_E), 1 / 2)
            and Acc(list_pred(A), 1 / 2) and Acc(list_pred(H), 1 / 2)
            and Acc(list_pred(S), 1 / 2))
    Ensures(Acc(list_pred(emark)) and Acc(list_pred(out)) and Acc(list_pred(src))
            and Acc(list_pred(via)))
    # Math: input_ok ∧ |emark| = m ∧ |src| = |out| ∧ |via| = |out|
    Ensures(input_ok(n, m, start, evt, dst, in_E))
    Ensures(len(emark) == m and len(src) == len(out) and len(via) == len(out))
    # THE RESULT (as active_events).
    # Math: in range and no duplicates: marks_ok(emark, out)
    Ensures(marks_ok(ToSeq(emark), ToSeq(out)))
    # Math: sound: ∀ i: ev_at(src[i], via[i], out[i])
    Ensures(ev_sound(start, evt, S, ToSeq(out), ToSeq(src), ToSeq(via)))
    # Math: complete: ∀ j ∈ [0,|S|). ∀ k ∈ block(S[j]): emark[evt[k]] ≥ 0
    Ensures(ev_complete_upto(start, evt, S, ToSeq(emark), len(S), 0))
    # Math: ∀ e ∈ [0,|emark|): emark[e] = -1
    # Why (hint): all_clear written out, so that marks_ok holds before the loop (empty result).
    Assert(Forall(int, lambda y: (Implies(0 <= y and y < len(emark), ToSeq(emark)[y] == -1),
                                  [[ToSeq(emark)[y]]])))
    j = 0                                        # position in S
    while j < len(S):                            # for each state of S
        # Why: the loop keeps its permissions.
        Invariant(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2)
                  and Acc(list_pred(dst), 1 / 2) and Acc(list_pred(in_E), 1 / 2)
                  and Acc(list_pred(A), 1 / 2) and Acc(list_pred(H), 1 / 2)
                  and Acc(list_pred(S), 1 / 2))
        Invariant(Acc(list_pred(emark)) and Acc(list_pred(out)) and Acc(list_pred(src))
                  and Acc(list_pred(via)))
        # Math: measure |S| - j + 6, decreasing.
        Invariant(MustTerminate(len(S) - j + 6))
        # Math: the input lists are unchanged.
        Invariant(ToSeq(start) == Old(ToSeq(start)) and ToSeq(evt) == Old(ToSeq(evt))
                  and ToSeq(dst) == Old(ToSeq(dst)) and ToSeq(in_E) == Old(ToSeq(in_E))
                  and ToSeq(A) == Old(ToSeq(A)) and ToSeq(H) == Old(ToSeq(H))
                  and ToSeq(S) == Old(ToSeq(S)))
        # Math: input_ok ∧ index_ok (the parts used) ∧ S in range ∧ 0 ≤ j ≤ |S|
        Invariant(input_ok(n, m, start, evt, dst, in_E))
        Invariant(len(A) == n + 1 and len(start) == n + 1)
        Invariant(Forall(int, lambda y: (
            Implies(0 <= y and y < n,
                    0 <= A[y] and A[y] <= A[y + 1] and A[y + 1] <= len(H)
                    and seg_ok(evt, H, start[y], start[y + 1], A[y], A[y + 1])),
            [[A[y + 1]]])))
        Invariant(Forall(int, lambda jj: (Implies(0 <= jj and jj < len(S),
                                                  0 <= S[jj] and S[jj] < n), [[S[jj]]])))
        Invariant(0 <= j and j <= len(S))
        # Math: sizes; marks_ok; ev_sound; ev_complete_upto(emark, j, 0)
        Invariant(len(emark) == m and len(src) == len(out) and len(via) == len(out))
        Invariant(marks_ok(ToSeq(emark), ToSeq(out)))
        Invariant(ev_sound(start, evt, S, ToSeq(out), ToSeq(src), ToSeq(via)))
        Invariant(ev_complete_upto(start, evt, S, ToSeq(emark), j, 0))
        # Math: x = S[j]: 0 ≤ A[x] ≤ A[x+1] ≤ |H| ∧ seg_ok(start[x], start[x+1], A[x], A[x+1])
        # Why (hint): the index fact at y = S[j] (mentioning A[S[j]+1] triggers it).
        Assert(0 <= S[j] and S[j] < n and A[S[j] + 1] <= len(H))
        Assert(seg_ok(evt, H, start[S[j]], start[S[j] + 1], A[S[j]], A[S[j] + 1]))
        x = S[j]                                 # the current state
        lo = start[x]                            # its block: [lo, hi)
        hi = start[x + 1]
        a0 = A[x]                                # its heads: a0 .. a1-1 (in H)
        a1 = A[x + 1]
        seg_runs(evt, H, lo, hi, a0, a1)         # lemma: runs_ok, and lo starts the first run
        ev_scan_idx(n, m, start, evt, dst, in_E, A, H, S, emark, out, src, via, j,
                    lo, hi, a0, a1)              # cover block(S[j])
        ev_next_j(start, evt, S, ToSeq(emark), j, start[S[j] + 1], j + 1)          # lemma: next j
        j += 1
