"""
Verified basic operations on an encoded automaton (certisc-proof/spec/basic_ops.md).

The automaton is encoded as in core_aut/verified_core/check.py: states 0 .. n-1, events 0 .. m-1, transitions
grouped by source state (state x owns positions start[x] .. start[x+1]-1 of evt / dst; position k
is the transition x --evt[k]--> dst[k]).

- next_states   the states reached from a list of states S by one event e (Lean: `step f S e`)

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
    # Math: k < |dst| ∧ dst[k] ∈ [0,n)
    # Why: the fact itself: the target of k is a state.
    Ensures(k < len(dst) and 0 <= dst[k] and dst[k] < n)
    # Math: dst[k] ∈ [0,n)
    # Why (hint): mentioning dst[k] triggers transitions_ok's quantifier at k.
    Assert(0 <= dst[k] and dst[k] < n)


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
