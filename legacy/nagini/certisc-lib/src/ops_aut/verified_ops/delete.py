"""
Verified checker for deleting states (certisc-proof/spec/delete_states.md).

Deleting a set D of states keeps the other states, renumbered in their old order, with every
transition between two kept states and no other. Trusted code (core_aut/trusted/delete_states.py)
builds the result as lists; `check_delete` accepts it only if it is exactly that. The checked
facts are the list form of the Lean `Automaton.IsDeletion` (certisc-proof, Automaton.lean).

Verify, from certisc-lib/ (Python >= 3.12, `verify` extra, Java):

    nagini src/ops_aut/verified_ops/delete.py

The lists (old automaton: n, start, evt, dst, init, marked; result: the same names with a 2):
    dele[x]      True if state x is deleted (length n)
    new_of[x]    the new number of x, or -1 if x is deleted (length n)
    old_of[i]    the old number of new state i (length n' = the number of kept states)
    start2, evt2, dst2, init2, marked2   the result, encoded as the old automaton is
    src2[k']     the old transition that new transition k' copies (length T')
    pos2[k]      the new transition that copies old transition k, or -1 (length T)

Math notation used in the comments:
    [a, b)       the integers a, a+1, ..., b-1
    |l|          the length of list (or sequence) l
    T, T'        |dst|, |dst2|: the numbers of old and new transitions
    n'           |old_of|, the number of new states
    block(x)     [start[x], start[x+1]), the positions of the transitions out of x
    block2(i)    [start2[i], start2[i+1]), the same in the result
    st, ds, ev, dl, nw, od, st2, ev2, ds2, s2, p2, in, mk, in2, mk2
                 ToSeq of start, dst, evt, dele, new_of, old_of, start2, evt2, dst2, src2, pos2,
                 init, marked, init2, marked2 (values, not lists)

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
- PSeq[int], PSeq[bool]      the type of such a value.
- Implies(a, b)              a → b.
- Forall(int, lambda i: (P, [[t]]))   ∀ i ∈ ℤ: P; Nagini uses it for an i where the term t
                             appears (the trigger).
- Result()                   the method's return value.
- @Pure                      a side-effect-free function, usable in contracts (a definition).

Note on ints: Nagini treats ints as objects, so from i == j it does not conclude f(i) == f(j)
for a function f (list reads do compare by value). Loops therefore step with a new variable
(nx = x + 1; x = nx) and the invariants use the exact variables.

Why these facts give exactly "G with D deleted" (the Lean IsDeletion, by hand):
- renumbering (renum_ok, order_ok): old_of is increasing and hits exactly the kept states, and
  new_of is its inverse on them;
- flags (flag_ok, for init and for marked): init2[i] = init[old_of[i]], marked2[i] = marked[old_of[i]];
- y ∈ f'(i, e) → old_of[y] ∈ f(old_of[i], e): take k' ∈ block2(i) with evt2[k'] = e,
  dst2[k'] = y. own2_ok: k = src2[k'] ∈ block(old_of[i]); trans_ok: evt[k] = e and
  y = new_of[dst[k]] ≥ 0, so old_of[y] = dst[k] (renum_ok);
- old_of[y] ∈ f(old_of[i], e) → y ∈ f'(i, e): take k ∈ block(old_of[i]) with evt[k] = e,
  dst[k] = old_of[y]. Both ends are kept, so keep_ok: k' = pos2[k] ∈ block2(i); pos2_ok:
  src2[k'] = k; trans_ok at k': evt2[k'] = e, dst2[k'] = new_of[old_of[y]] = y.
The events (in_E, in_Euc, in_Euo) are copied unchanged by the trusted code, and the result is
then run through the verified validity checker (check_automaton) like any new automaton.

Map of the file:
- specification: renum_ok, order_ok, flag_ok, trans_ok, own2_ok, pos2_ok, keep_ok;
- one checker method per fact;
- check_delete: the whole check (the seven, plus the block structure of start2).
"""

from typing import List

from nagini_contracts.contracts import *
from nagini_contracts.obligations import MustTerminate

# blocks_ok and its checker, from the verified validity checker.
from core_aut.verified_core.check import blocks_ok, check_blocks
# in_blk: "k is in block x" (shared with reach.py, coreach.py and the reverse index).
from core_aut.verified_core.blocks import in_blk


# --- specification ---------------------------------------------------------------------------
# Definitions used in the contracts. They say what "correct" means; they run no code.


# renum_ok: new_of and old_of are inverse renumberings of the kept states.
@Pure
def renum_ok(n: int, dl: PSeq[bool], nw: PSeq[int], od: PSeq[int]) -> bool:
    """new_of[x] = -1 for a deleted x; otherwise old_of[new_of[x]] = x; and each old_of[i] is a
    state with new_of[old_of[i]] = i."""
    # Math: |dl| = |nw| = n
    #       ∧ ∀ x ∈ [0,n): (dl[x] → nw[x] = -1) ∧ (¬dl[x] → nw[x] ∈ [0,|od|) ∧ od[nw[x]] = x)
    # Why: every state is either deleted (no new number) or kept, with a new number that maps
    #      back to it. Trigger nw[x].
    # Math: ∀ i ∈ [0,|od|): od[i] ∈ [0,n) ∧ nw[od[i]] = i
    # Why: every new state is an old state whose new number is i (so it is kept, as i ≠ -1).
    #      Trigger od[i].
    return (len(dl) == n and len(nw) == n
            and Forall(int, lambda x: (Implies(0 <= x and x < n,
                                               Implies(dl[x], nw[x] == -1)
                                               and Implies(not dl[x],
                                                           0 <= nw[x] and nw[x] < len(od)
                                                           and od[nw[x]] == x)),
                                       [[nw[x]]]))
            and Forall(int, lambda i: (Implies(0 <= i and i < len(od),
                                               0 <= od[i] and od[i] < n and nw[od[i]] == i),
                                       [[od[i]]])))


# order_ok: the kept states keep their order.
@Pure
def order_ok(od: PSeq[int]) -> bool:
    """old_of is strictly increasing (checked on neighbours)."""
    # Math: ∀ i ∈ [0, |od|-1): od[i] < od[i+1]
    # Why: the Lean StrictMono (from neighbours by induction; a fact about order only, which no
    #      other check needs). Trigger: the pair od[i], od[i+1] (od[i+1] alone would also match
    #      the od[i] of the body, one index lower: a matching loop).
    return Forall(int, lambda i: (Implies(0 <= i and i + 1 < len(od), od[i] < od[i + 1]),
                                  [[od[i], od[i + 1]]]))


# flag fact (no pure function): each new state has the flag of its old state, for one flag list
# f (init or marked):
#     |f2| = |od| ∧ ∀ i ∈ [0,|od|): od[i] ∈ [0,|f|) ∧ (f2[i] ↔ f[od[i]])
# It is written out in full in the contracts of check_flag and check_delete, over the lists:
# - not over sequences: sequences of bools did not verify (Nagini boxes bools as objects);
# - not as a pure function: Nagini would not fold a pure function whose quantifier reads bool
#   lists (the reads are function applications; the same lesson as in active_index.py).


# trans_ok: each new transition copies an old one, with its event and its renamed target.
@Pure
def trans_ok(ev: PSeq[int], ds: PSeq[int], nw: PSeq[int], ev2: PSeq[int], ds2: PSeq[int],
             s2: PSeq[int], p2: PSeq[int]) -> bool:
    """For each new transition k': src2[k'] = k is an old transition, pos2[k] = k',
    evt2[k'] = evt[k], and dst2[k'] = new_of[dst[k]] ≥ 0 (the target is kept)."""
    # Math: |ev| = |ds| = |p2| ∧ |ev2| = |ds2| = |s2|
    #       ∧ ∀ k' ∈ [0,|s2|): s2[k'] ∈ [0,|ds|) ∧ p2[s2[k']] = k' ∧ ev2[k'] = ev[s2[k']]
    #                          ∧ ds[s2[k']] ∈ [0,|nw|) ∧ ds2[k'] = nw[ds[s2[k']]] ≥ 0
    # Why: soundness of each new transition, except its source (own2_ok). p2[s2[k']] = k' also
    #      makes src2 one-to-one (no old transition is copied twice). Trigger s2[k'].
    return (len(ev) == len(ds) and len(p2) == len(ds)
            and len(ev2) == len(s2) and len(ds2) == len(s2)
            and Forall(int, lambda j: (Implies(0 <= j and j < len(s2),
                                               0 <= s2[j] and s2[j] < len(ds)
                                               and p2[s2[j]] == j
                                               and ev2[j] == ev[s2[j]]
                                               and 0 <= ds[s2[j]] and ds[s2[j]] < len(nw)
                                               and ds2[j] == nw[ds[s2[j]]]
                                               and ds2[j] >= 0),
                                       [[s2[j]]])))


# own2 fact (no pure function): a new transition out of i copies a transition out of old_of[i]:
#     ∀ k' ∈ [0,|s2|). ∀ i. k' ∈ block2(i) ∧ i < |od| → i ∈ [0,|od|) ∧ s2[k'] ∈ block(od[i])
# ("i < |od|" in the antecedent costs nothing: blocks_ok(|od|, start2, T') gives it for any i
# with k' ∈ block2(i); stating it saves the solver an unfolding of in_blk under a quantifier,
# which made this postcondition verify only sometimes.)
# It is written in full in the contracts of check_own2 and check_delete: as a pure function,
# Nagini would not fold it (the formula itself verified, the function application did not; as for
# the flags; likely because the conclusion applies another function, in_blk).
# Triggers: s2[k'] for the outer ∀; in_blk(st2, i, k') for the inner (no single read contains
# both i and k').


# pos2_ok: pos2 points back: if old transition k is copied, it is copied at pos2[k].
@Pure
def pos2_ok(s2: PSeq[int], p2: PSeq[int]) -> bool:
    """For each old transition k: pos2[k] = -1, or src2[pos2[k]] = k."""
    # Math: ∀ k ∈ [0,|p2|): p2[k] = -1 ∨ (p2[k] ∈ [0,|s2|) ∧ s2[p2[k]] = k)
    # Why: with keep_ok, completeness without counting (pos2 is the inverse of src2 where
    #      defined). Trigger p2[k].
    return Forall(int, lambda k: (Implies(0 <= k and k < len(p2),
                                          p2[k] == -1
                                          or (0 <= p2[k] and p2[k] < len(s2)
                                              and s2[p2[k]] == k)),
                                  [[p2[k]]]))


# keep_ok: every old transition between two kept states is copied, into the right block.
@Pure
def keep_ok(st: PSeq[int], ds: PSeq[int], nw: PSeq[int], st2: PSeq[int],
            p2: PSeq[int]) -> bool:
    """For k ∈ block(x), with x and dst[k] kept: pos2[k] ∈ block2(new_of[x])."""
    # Math: ∀ k ∈ [0,|p2|). ∀ x. k ∈ block(x) ∧ x ∈ [0,|nw|) ∧ k < |ds| ∧ ds[k] ∈ [0,|nw|)
    #                             ∧ nw[x] ≥ 0 ∧ nw[ds[k]] ≥ 0  →  p2[k] ∈ block2(nw[x])
    # Why: completeness: no transition between kept states is lost. Triggers: p2[k] outer;
    #      in_blk(st, x, k) inner.
    return Forall(int, lambda k: (Implies(
        0 <= k and k < len(p2),
        Forall(int, lambda x: (Implies(in_blk(st, x, k) and 0 <= x and x < len(nw)
                                       and k < len(ds) and 0 <= ds[k] and ds[k] < len(nw)
                                       and nw[x] >= 0 and nw[ds[k]] >= 0,
                                       in_blk(st2, nw[x], p2[k])),
                               [[in_blk(st, x, k)]]))),
        [[p2[k]]]))


# --- checkers --------------------------------------------------------------------------------
# One method per fact. Each returns True only if its fact holds (Ensures Result() → fact).


# check_renum: one pass over the old states, one over the new ones.
def check_renum(n: int, dele: List[bool], new_of: List[int], old_of: List[int]) -> bool:
    """True only if renum_ok."""
    # Why: read access.
    Requires(Acc(list_pred(dele), 1 / 4) and Acc(list_pred(new_of), 1 / 4)
             and Acc(list_pred(old_of), 1 / 4))
    # Math: termination measure 2.
    # Why: two loops one after the other, no calls.
    Requires(MustTerminate(2))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(dele), 1 / 4) and Acc(list_pred(new_of), 1 / 4)
            and Acc(list_pred(old_of), 1 / 4))
    # Math: Result → renum_ok(n, dl, nw, od)
    # Why: the fact checked.
    Ensures(Implies(Result(), renum_ok(n, ToSeq(dele), ToSeq(new_of), ToSeq(old_of))))
    if len(dele) != n or len(new_of) != n:   # Math: |dl| = |nw| = n, else reject
        return False
    x = 0                                    # the old state
    while x < n:                             # each old state
        # Why: read access, kept through the loop.
        Invariant(Acc(list_pred(dele), 1 / 4) and Acc(list_pred(new_of), 1 / 4)
                  and Acc(list_pred(old_of), 1 / 4))
        # Math: measure n - x + 1.
        # Why: x goes up by 1.
        Invariant(MustTerminate(n - x + 1))
        # Math: |dl| = |nw| = n ∧ 0 ≤ x ≤ n
        # Why: the lengths, kept; x in range.
        Invariant(len(dele) == n and len(new_of) == n and 0 <= x and x <= n)
        # Math: ∀ z ∈ [0,x): (dl[z] → nw[z] = -1) ∧ (¬dl[z] → nw[z] ∈ [0,|od|) ∧ od[nw[z]] = z)
        # Why: the first part of renum_ok for the states checked so far. Trigger as there.
        Invariant(Forall(int, lambda z: (Implies(0 <= z and z < x,
                                                 Implies(ToSeq(dele)[z], ToSeq(new_of)[z] == -1)
                                                 and Implies(not ToSeq(dele)[z],
                                                             0 <= ToSeq(new_of)[z]
                                                             and ToSeq(new_of)[z] < len(ToSeq(old_of))
                                                             and ToSeq(old_of)[ToSeq(new_of)[z]] == z)),
                                         [[ToSeq(new_of)[z]]])))
        i = new_of[x]                        # the claimed new number of x
        # Math: nw[x] = i
        # Why (hint): the list read, as a sequence entry (the term the invariant uses).
        Assert(ToSeq(new_of)[x] == i)
        if dele[x]:                          # Math: x ∈ D
            if i != -1:                      # Math: nw[x] = -1, else reject
                return False
        else:                                # Math: x ∉ D
            if i < 0 or i >= len(old_of):    # Math: i ∈ [0,|od|), else reject
                return False
            if old_of[i] != x:               # Math: od[i] = x, else reject
                return False
            # Math: od[i] = x
            # Why (hint): as a sequence entry.
            Assert(ToSeq(old_of)[i] == x)
        nx = x + 1                           # the next state (a variable: the int note)
        x = nx
    i = 0                                    # the new state
    while i < len(old_of):                   # each new state
        # Why: read access, kept through the loop.
        Invariant(Acc(list_pred(dele), 1 / 4) and Acc(list_pred(new_of), 1 / 4)
                  and Acc(list_pred(old_of), 1 / 4))
        # Math: measure |od| - i + 1.
        # Why: i goes up by 1.
        Invariant(MustTerminate(len(old_of) - i + 1))
        # Math: |dl| = |nw| = n ∧ 0 ≤ i ≤ |od|
        # Why: the lengths, kept; i in range.
        Invariant(len(dele) == n and len(new_of) == n and 0 <= i and i <= len(old_of))
        # Math: ∀ z ∈ [0,n): (dl[z] → nw[z] = -1) ∧ (¬dl[z] → nw[z] ∈ [0,|od|) ∧ od[nw[z]] = z)
        # Why: the first part, finished by the first loop, kept (nothing is written).
        Invariant(Forall(int, lambda z: (Implies(0 <= z and z < n,
                                                 Implies(ToSeq(dele)[z], ToSeq(new_of)[z] == -1)
                                                 and Implies(not ToSeq(dele)[z],
                                                             0 <= ToSeq(new_of)[z]
                                                             and ToSeq(new_of)[z] < len(ToSeq(old_of))
                                                             and ToSeq(old_of)[ToSeq(new_of)[z]] == z)),
                                         [[ToSeq(new_of)[z]]])))
        # Math: ∀ j ∈ [0,i): od[j] ∈ [0,n) ∧ nw[od[j]] = j
        # Why: the second part of renum_ok for the new states checked so far. Trigger od[j].
        Invariant(Forall(int, lambda j: (Implies(0 <= j and j < i,
                                                 0 <= ToSeq(old_of)[j] and ToSeq(old_of)[j] < n
                                                 and ToSeq(new_of)[ToSeq(old_of)[j]] == j),
                                         [[ToSeq(old_of)[j]]])))
        x = old_of[i]                        # the claimed old state of i
        # Math: od[i] = x
        # Why (hint): the list read, as a sequence entry.
        Assert(ToSeq(old_of)[i] == x)
        if x < 0 or x >= n:                  # Math: x ∈ [0,n), else reject
            return False
        if new_of[x] != i:                   # Math: nw[x] = i, else reject
            return False
        # Math: nw[x] = i
        # Why (hint): as a sequence entry.
        Assert(ToSeq(new_of)[x] == i)
        ni = i + 1                           # the next new state (a variable: the int note)
        i = ni
    # Math: renum_ok(n, dl, nw, od)
    # Why (hint): the two invariants at the ends of the loops are its body.
    Assert(renum_ok(n, ToSeq(dele), ToSeq(new_of), ToSeq(old_of)))
    return True


# check_order: one pass over neighbouring new states.
def check_order(old_of: List[int]) -> bool:
    """True only if order_ok."""
    # Why: read access.
    Requires(Acc(list_pred(old_of), 1 / 4))
    # Math: termination measure 2.
    # Why: one loop, no calls.
    Requires(MustTerminate(2))
    # Why: gives the permission back.
    Ensures(Acc(list_pred(old_of), 1 / 4))
    # Math: Result → order_ok(od)
    # Why: the fact checked.
    Ensures(Implies(Result(), order_ok(ToSeq(old_of))))
    i = 0                                    # the left neighbour
    while i + 1 < len(old_of):               # each neighbouring pair (i, i+1)
        # Why: read access, kept through the loop.
        Invariant(Acc(list_pred(old_of), 1 / 4))
        # Math: measure |od| - i + 1.
        # Why: i goes up by 1.
        Invariant(MustTerminate(len(old_of) - i + 1))
        # Math: 0 ≤ i
        # Why: i in range (the loop test gives i+1 < |od|).
        Invariant(0 <= i)
        # Math: ∀ j ∈ [0,i): j+1 < |od| → od[j] < od[j+1]
        # Why: order_ok for the pairs checked so far. Trigger as in order_ok.
        Invariant(Forall(int, lambda j: (Implies(0 <= j and j < i and j + 1 < len(ToSeq(old_of)),
                                                 ToSeq(old_of)[j] < ToSeq(old_of)[j + 1]),
                                         [[ToSeq(old_of)[j], ToSeq(old_of)[j + 1]]])))
        if old_of[i] >= old_of[i + 1]:       # Math: od[i] < od[i+1], else reject
            return False
        # Math: od[i] < od[i+1]
        # Why (hint): the test above, as sequence entries.
        Assert(ToSeq(old_of)[i] < ToSeq(old_of)[i + 1])
        ni = i + 1                           # the next pair (a variable: the int note)
        i = ni
    # Math: order_ok(od)
    # Why (hint): at the end every pair (j, j+1) has j < i.
    Assert(order_ok(ToSeq(old_of)))
    return True


# check_flag: one pass over the new states, for one flag list f (init or marked).
def check_flag(old_of: List[int], f: List[bool], f2: List[bool]) -> bool:
    """True only if the flag fact holds for f (see the note above)."""
    # Why: read access.
    Requires(Acc(list_pred(old_of), 1 / 4) and Acc(list_pred(f), 1 / 4)
             and Acc(list_pred(f2), 1 / 4))
    # Math: termination measure 2.
    # Why: one loop, no calls.
    Requires(MustTerminate(2))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(old_of), 1 / 4) and Acc(list_pred(f), 1 / 4)
            and Acc(list_pred(f2), 1 / 4))
    # Math: Result → |f2| = |od| ∧ ∀ j ∈ [0,|od|): od[j] ∈ [0,|f|) ∧ (f2[j] ↔ f[od[j]])
    # Why: the flag fact checked (written out; see the note above check_flag). Trigger old_of[j] (an int read: a bool read as trigger did not verify).
    Ensures(Implies(Result(), len(f2) == len(old_of)
                    and Forall(int, lambda j: (Implies(0 <= j and j < len(old_of),
                                                       0 <= old_of[j] and old_of[j] < len(f)
                                                       and Implies(f2[j], f[old_of[j]])
                                                       and Implies(f[old_of[j]], f2[j])),
                                               [[old_of[j]]]))))
    if len(f2) != len(old_of):               # Math: |f2| = |od|, else reject
        return False
    i = 0                                    # the new state
    while i < len(old_of):                   # each new state
        # Why: read access, kept through the loop.
        Invariant(Acc(list_pred(old_of), 1 / 4) and Acc(list_pred(f), 1 / 4)
                  and Acc(list_pred(f2), 1 / 4))
        # Math: measure |od| - i + 1.
        # Why: i goes up by 1.
        Invariant(MustTerminate(len(old_of) - i + 1))
        # Math: |f2| = |od| ∧ 0 ≤ i ≤ |od|
        # Why: the length, kept; i in range.
        Invariant(len(f2) == len(old_of) and 0 <= i and i <= len(old_of))
        # Math: ∀ j ∈ [0,i): od[j] ∈ [0,|f|) ∧ (f2[j] ↔ f[od[j]])
        # Why: the flag fact for the new states checked so far. Trigger old_of[j] (an int read: a bool read as trigger did not verify).
        Invariant(Forall(int, lambda j: (Implies(0 <= j and j < i,
                                                 0 <= old_of[j] and old_of[j] < len(f)
                                                 and Implies(f2[j], f[old_of[j]])
                                                 and Implies(f[old_of[j]], f2[j])),
                                         [[old_of[j]]])))
        x = old_of[i]                        # the old state of i
        if x < 0 or x >= len(f):             # Math: x ∈ [0,|f|), else reject
            return False
        if (f2[i] and not f[x]) or (f[x] and not f2[i]):     # Math: ¬(f2[i] ↔ f[x]): reject
            return False
        # Math: od[i] ∈ [0,|f|) ∧ (f2[i] ↔ f[od[i]])
        # Why (hint): the tests above, in the exact terms of the invariant at j = i.
        Assert(0 <= old_of[i] and old_of[i] < len(f)
               and Implies(f2[i], f[old_of[i]]) and Implies(f[old_of[i]], f2[i]))
        ni = i + 1                           # the next new state (a variable: the int note)
        i = ni
    # Math: i = |od|
    # Why (hint): the loop's end, so the invariant covers every new state.
    Assert(i == len(old_of))
    return True


# check_trans: one pass over the new transitions.
def check_trans(evt: List[int], dst: List[int], new_of: List[int], evt2: List[int],
                dst2: List[int], src2: List[int], pos2: List[int]) -> bool:
    """True only if trans_ok."""
    # Why: read access.
    Requires(Acc(list_pred(evt), 1 / 4) and Acc(list_pred(dst), 1 / 4)
             and Acc(list_pred(new_of), 1 / 4) and Acc(list_pred(evt2), 1 / 4)
             and Acc(list_pred(dst2), 1 / 4) and Acc(list_pred(src2), 1 / 4)
             and Acc(list_pred(pos2), 1 / 4))
    # Math: termination measure 2.
    # Why: one loop, no calls.
    Requires(MustTerminate(2))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(evt), 1 / 4) and Acc(list_pred(dst), 1 / 4)
            and Acc(list_pred(new_of), 1 / 4) and Acc(list_pred(evt2), 1 / 4)
            and Acc(list_pred(dst2), 1 / 4) and Acc(list_pred(src2), 1 / 4)
            and Acc(list_pred(pos2), 1 / 4))
    # Math: Result → trans_ok(ev, ds, nw, ev2, ds2, s2, p2)
    # Why: the fact checked.
    Ensures(Implies(Result(), trans_ok(ToSeq(evt), ToSeq(dst), ToSeq(new_of), ToSeq(evt2),
                                       ToSeq(dst2), ToSeq(src2), ToSeq(pos2))))
    if len(evt) != len(dst) or len(pos2) != len(dst):        # Math: |ev| = |p2| = T, else reject
        return False
    if len(evt2) != len(src2) or len(dst2) != len(src2):     # Math: |ev2| = |ds2| = T', else reject
        return False
    j = 0                                    # the new transition
    while j < len(src2):                     # each new transition
        # Why: read access, kept through the loop.
        Invariant(Acc(list_pred(evt), 1 / 4) and Acc(list_pred(dst), 1 / 4)
                  and Acc(list_pred(new_of), 1 / 4) and Acc(list_pred(evt2), 1 / 4)
                  and Acc(list_pred(dst2), 1 / 4) and Acc(list_pred(src2), 1 / 4)
                  and Acc(list_pred(pos2), 1 / 4))
        # Math: measure T' - j + 1.
        # Why: j goes up by 1.
        Invariant(MustTerminate(len(src2) - j + 1))
        # Math: the lengths ∧ 0 ≤ j ≤ T'
        # Why: kept; j in range.
        Invariant(len(evt) == len(dst) and len(pos2) == len(dst) and len(evt2) == len(src2)
                  and len(dst2) == len(src2) and 0 <= j and j <= len(src2))
        # Math: ∀ i ∈ [0,j): s2[i] ∈ [0,T) ∧ p2[s2[i]] = i ∧ ev2[i] = ev[s2[i]]
        #                    ∧ ds[s2[i]] ∈ [0,|nw|) ∧ ds2[i] = nw[ds[s2[i]]] ≥ 0
        # Why: trans_ok for the new transitions checked so far. Trigger s2[i].
        Invariant(Forall(int, lambda i: (Implies(0 <= i and i < j,
                                                 0 <= ToSeq(src2)[i] and ToSeq(src2)[i] < len(ToSeq(dst))
                                                 and ToSeq(pos2)[ToSeq(src2)[i]] == i
                                                 and ToSeq(evt2)[i] == ToSeq(evt)[ToSeq(src2)[i]]
                                                 and 0 <= ToSeq(dst)[ToSeq(src2)[i]]
                                                 and ToSeq(dst)[ToSeq(src2)[i]] < len(ToSeq(new_of))
                                                 and ToSeq(dst2)[i] == ToSeq(new_of)[ToSeq(dst)[ToSeq(src2)[i]]]
                                                 and ToSeq(dst2)[i] >= 0),
                                         [[ToSeq(src2)[i]]])))
        k = src2[j]                          # the old transition copied
        # Math: s2[j] = k
        # Why (hint): the list read, as a sequence entry.
        Assert(ToSeq(src2)[j] == k)
        if k < 0 or k >= len(dst):           # Math: k ∈ [0,T), else reject
            return False
        if pos2[k] != j or evt2[j] != evt[k]:    # Math: p2[k] = j ∧ ev2[j] = ev[k], else reject
            return False
        y = dst[k]                           # the old target
        if y < 0 or y >= len(new_of):        # Math: y ∈ [0,|nw|), else reject
            return False
        if dst2[j] != new_of[y] or dst2[j] < 0:  # Math: ds2[j] = nw[y] ≥ 0, else reject
            return False
        # Math: p2[k] = j ∧ ev2[j] = ev[k] ∧ ds[k] = y ∧ ds2[j] = nw[y]
        # Why (hint): the tests above, as sequence entries.
        Assert(ToSeq(pos2)[k] == j and ToSeq(evt2)[j] == ToSeq(evt)[k]
               and ToSeq(dst)[k] == y and ToSeq(dst2)[j] == ToSeq(new_of)[y])
        nj = j + 1                           # the next new transition (a variable: the int note)
        j = nj
    # Math: trans_ok(ev, ds, nw, ev2, ds2, s2, p2)
    # Why (hint): the invariant at j = T' is its body.
    Assert(trans_ok(ToSeq(evt), ToSeq(dst), ToSeq(new_of), ToSeq(evt2), ToSeq(dst2),
                    ToSeq(src2), ToSeq(pos2)))
    return True


# check_own2: for each new state i, each new transition in block2(i).
# Shaped like check_own in core_aut/verified_core/reverse_index.py (two nested loops in one method,
# no return in the outer loop body): a version with the inner loop as its own method, and one with
# a return before the inner loop, verified only sometimes (measured 2026-10-27).
def check_own2(n: int, start: List[int], old_of: List[int], start2: List[int],
               src2: List[int]) -> bool:
    """True only if the own2 fact holds (see the note above)."""
    # Why: read access.
    Requires(Acc(list_pred(start), 1 / 4) and Acc(list_pred(old_of), 1 / 4)
             and Acc(list_pred(start2), 1 / 4) and Acc(list_pred(src2), 1 / 4))
    # Math: termination measure 3.
    # Why: two nested loops, no calls.
    Requires(MustTerminate(3))
    # Math: |start| = n+1 ∧ blocks_ok(|od|, start2, |s2|)
    # Why: start[x], start[x+1] are valid reads for a state x; block2(i) is a valid range.
    Requires(len(start) == n + 1)
    Requires(blocks_ok(len(old_of), start2, len(src2)))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 4) and Acc(list_pred(old_of), 1 / 4)
            and Acc(list_pred(start2), 1 / 4) and Acc(list_pred(src2), 1 / 4))
    # Math: Result → ∀ l ∈ [0,T'). ∀ z. l ∈ block2(z) ∧ z < |od| → z ∈ [0,|od|) ∧ s2[l] ∈ block(od[z])
    # Why: the own2 fact checked (written out; see the note above).
    Ensures(Implies(Result(), Forall(int, lambda l: (Implies(
        0 <= l and l < len(ToSeq(src2)),
        Forall(int, lambda z: (Implies(in_blk(ToSeq(start2), z, l) and z < len(ToSeq(old_of)),
                                       0 <= z and z < len(ToSeq(old_of))
                                           and in_blk(ToSeq(start), ToSeq(old_of)[z], ToSeq(src2)[l])),
                               [[in_blk(ToSeq(start2), z, l)]]))),
        [[ToSeq(src2)[l]]]))))
    n2 = len(old_of)                         # the number of new states (a variable: see below)
    i = 0                                    # the new state
    while i < n2:                            # each new state
        # Why: read access, kept through the loop.
        Invariant(Acc(list_pred(start), 1 / 4) and Acc(list_pred(old_of), 1 / 4)
                  and Acc(list_pred(start2), 1 / 4) and Acc(list_pred(src2), 1 / 4))
        # Math: measure n2 - i + 2 (> the inner loop's).
        # Why: i goes up by 1. Over the variable n2, not |od|: with the list length in the
        #      measure of an outer loop, the termination check failed (measured 2026-10-27).
        Invariant(MustTerminate(n2 - i + 2))
        # Math: |start| = n+1 ∧ blocks_ok(|od|, start2, |s2|) ∧ n2 = |od| ∧ 0 ≤ i ≤ |od|
        # Why: the preconditions, kept; i in range.
        Invariant(len(start) == n + 1 and blocks_ok(len(old_of), start2, len(src2))
                  and n2 == len(old_of) and 0 <= i and i <= len(old_of))
        # Math: ∀ l ∈ [0,T'). ∀ z < i. l ∈ block2(z) → z ∈ [0,|od|) ∧ s2[l] ∈ block(od[z])
        # Why: the own2 fact for the new states checked so far. Triggers as in the own2 fact.
        Invariant(Forall(int, lambda l: (Implies(
            0 <= l and l < len(ToSeq(src2)),
            Forall(int, lambda z: (Implies(in_blk(ToSeq(start2), z, l) and z < i,
                                           0 <= z and z < len(ToSeq(old_of))
                                           and in_blk(ToSeq(start), ToSeq(old_of)[z], ToSeq(src2)[l])),
                                   [[in_blk(ToSeq(start2), z, l)]]))),
            [[ToSeq(src2)[l]]])))
        # Math: |start2| = |od|+1 ∧ 0 ≤ start2[i] ≤ start2[i+1] ≤ T'
        # Why (hint): blocks_ok at i, so block2(i) is a valid range of src2. start2[i + 1]
        #      comes first: it is the trigger of blocks_ok's ∀.
        Assert(len(start2) == len(old_of) + 1 and start2[i + 1] <= len(src2)
               and 0 <= start2[i] and start2[i] <= start2[i + 1])
        x = old_of[i]                        # the old state of i (range checked below)
        j = start2[i]                        # first new transition of i
        hi2 = start2[i + 1]                  # one past the last
        while j < hi2:                       # each new transition of i
            # Why: read access, kept through the loop.
            Invariant(Acc(list_pred(start), 1 / 4) and Acc(list_pred(old_of), 1 / 4)
                      and Acc(list_pred(start2), 1 / 4) and Acc(list_pred(src2), 1 / 4))
            # Math: measure hi2 - j + 1.
            # Why: j goes up by 1, up to hi2.
            Invariant(MustTerminate(hi2 - j + 1))
            # Math: the outer facts ∧ i ∈ [0,|od|) ∧ od[i] = x
            #       ∧ start2[i] ≤ j ≤ hi2 = start2[i+1] ≤ T'
            # Why: kept; j inside block2(i).
            Invariant(len(start) == n + 1 and blocks_ok(len(old_of), start2, len(src2))
                      and n2 == len(old_of)
                      and 0 <= i and i < len(old_of) and len(start2) == len(old_of) + 1
                      and ToSeq(old_of)[i] == x
                      and start2[i] <= j and j <= hi2 and hi2 == start2[i + 1]
                      and hi2 <= len(src2) and 0 <= start2[i])
            # Math: ∀ l ∈ [0,T'). ∀ z. l ∈ block2(z) ∧ (z < i ∨ (z = i ∧ l < j))
            #                          → z ∈ [0,|od|) ∧ s2[l] ∈ block(od[z])
            # Why: the new states before i, and block2(i) up to j. Triggers as in the own2 fact.
            Invariant(Forall(int, lambda l: (Implies(
                0 <= l and l < len(ToSeq(src2)),
                Forall(int, lambda z: (Implies(in_blk(ToSeq(start2), z, l)
                                               and (z < i or (z == i and l < j)),
                                               0 <= z and z < len(ToSeq(old_of))
                                           and in_blk(ToSeq(start), ToSeq(old_of)[z], ToSeq(src2)[l])),
                                       [[in_blk(ToSeq(start2), z, l)]]))),
                [[ToSeq(src2)[l]]])))
            if x < 0 or x >= n:              # Math: x ∈ [0,n), else reject
                return False
            k = src2[j]                      # the old transition copied at j
            if k < start[x] or k >= start[x + 1]:    # Math: k ∈ block(x), else reject
                return False
            # Math: s2[j] = k ∧ in_blk(st, x, k)
            # Why (hint): the list read and the test, as the terms the invariant uses.
            Assert(ToSeq(src2)[j] == k and in_blk(ToSeq(start), x, k))
            nj = j + 1                       # the next new transition (the int note)
            j = nj
        ni = i + 1                           # the next new state (a variable: the int note)
        # Math: ∀ l ∈ [0,T'). ∀ z < ni. l ∈ block2(z) → z ∈ [0,|od|) ∧ s2[l] ∈ block(od[z])
        # Why (hint): z < i is the old part; z = i: l ∈ block2(i) means l < start2[i+1] = j.
        Assert(Forall(int, lambda l: (Implies(
            0 <= l and l < len(ToSeq(src2)),
            Forall(int, lambda z: (Implies(in_blk(ToSeq(start2), z, l) and z < ni,
                                           0 <= z and z < len(ToSeq(old_of))
                                           and in_blk(ToSeq(start), ToSeq(old_of)[z], ToSeq(src2)[l])),
                                   [[in_blk(ToSeq(start2), z, l)]]))),
            [[ToSeq(src2)[l]]])))
        i = ni
    # Math: i = |od|
    # Why (hint): the loop's end: "z < i" in the invariant is "z < |od|" in the postcondition.
    Assert(i == len(ToSeq(old_of)))
    return True


# check_pos2: one pass over the old transitions.
def check_pos2(src2: List[int], pos2: List[int]) -> bool:
    """True only if pos2_ok."""
    # Why: read access.
    Requires(Acc(list_pred(src2), 1 / 4) and Acc(list_pred(pos2), 1 / 4))
    # Math: termination measure 2.
    # Why: one loop, no calls.
    Requires(MustTerminate(2))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(src2), 1 / 4) and Acc(list_pred(pos2), 1 / 4))
    # Math: Result → pos2_ok(s2, p2)
    # Why: the fact checked.
    Ensures(Implies(Result(), pos2_ok(ToSeq(src2), ToSeq(pos2))))
    k = 0                                    # the old transition
    while k < len(pos2):                     # each old transition
        # Why: read access, kept through the loop.
        Invariant(Acc(list_pred(src2), 1 / 4) and Acc(list_pred(pos2), 1 / 4))
        # Math: measure T - k + 1.
        # Why: k goes up by 1.
        Invariant(MustTerminate(len(pos2) - k + 1))
        # Math: 0 ≤ k ≤ T
        # Why: k in range.
        Invariant(0 <= k and k <= len(pos2))
        # Math: ∀ i ∈ [0,k): p2[i] = -1 ∨ (p2[i] ∈ [0,T') ∧ s2[p2[i]] = i)
        # Why: pos2_ok for the old transitions checked so far. Trigger p2[i].
        Invariant(Forall(int, lambda i: (Implies(0 <= i and i < k,
                                                 ToSeq(pos2)[i] == -1
                                                 or (0 <= ToSeq(pos2)[i]
                                                     and ToSeq(pos2)[i] < len(ToSeq(src2))
                                                     and ToSeq(src2)[ToSeq(pos2)[i]] == i)),
                                         [[ToSeq(pos2)[i]]])))
        j = pos2[k]                          # the claimed new transition of k
        # Math: p2[k] = j
        # Why (hint): the list read, as a sequence entry.
        Assert(ToSeq(pos2)[k] == j)
        if j != -1:                          # Math: k is copied (claimed)
            if j < 0 or j >= len(src2):      # Math: j ∈ [0,T'), else reject
                return False
            if src2[j] != k:                 # Math: s2[j] = k, else reject
                return False
            # Math: s2[j] = k
            # Why (hint): as a sequence entry.
            Assert(ToSeq(src2)[j] == k)
        nk = k + 1                           # the next old transition (the int note)
        k = nk
    # Math: pos2_ok(s2, p2)
    # Why (hint): the invariant at k = T is its body.
    Assert(pos2_ok(ToSeq(src2), ToSeq(pos2)))
    return True


# check_keep_block: one old state x, each old transition in block(x).
# The inner loop of check_keep, as its own method (inner loops verify faster this way).
def check_keep_block(n: int, x: int, start: List[int], dst: List[int], new_of: List[int],
                     start2: List[int], pos2: List[int]) -> bool:
    """True only if keep_ok holds for the transitions out of x."""
    # Why: read access.
    Requires(Acc(list_pred(start), 1 / 8) and Acc(list_pred(dst), 1 / 8)
             and Acc(list_pred(new_of), 1 / 8) and Acc(list_pred(start2), 1 / 8)
             and Acc(list_pred(pos2), 1 / 8))
    # Math: termination measure 2.
    # Why: one loop, no calls.
    Requires(MustTerminate(2))
    # Math: blocks_ok(n, start, |p2|) ∧ |p2| = |ds| ∧ x ∈ [0,n)
    # Why: block(x) is a valid range of positions of pos2 and dst.
    Requires(blocks_ok(n, start, len(pos2)) and len(pos2) == len(dst) and 0 <= x and x < n)
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 8) and Acc(list_pred(dst), 1 / 8)
            and Acc(list_pred(new_of), 1 / 8) and Acc(list_pred(start2), 1 / 8)
            and Acc(list_pred(pos2), 1 / 8))
    # Math: Result → ∀ l ∈ [0,T). ∀ z. l ∈ block(z) ∧ z = x ∧ z ∈ [0,|nw|) ∧ ds[l] ∈ [0,|nw|)
    #                                  ∧ nw[z] ≥ 0 ∧ nw[ds[l]] ≥ 0 → p2[l] ∈ block2(nw[z])
    # Why: keep_ok at z = x, in keep_ok's own shape (a free z with z = x; see
    #      check_own2_block). Triggers as in keep_ok.
    Ensures(Implies(Result(), Forall(int, lambda l: (Implies(
        0 <= l and l < len(ToSeq(pos2)),
        Forall(int, lambda z: (Implies(in_blk(ToSeq(start), z, l) and z == x
                                       and 0 <= z and z < len(ToSeq(new_of))
                                       and l < len(ToSeq(dst)) and 0 <= ToSeq(dst)[l]
                                       and ToSeq(dst)[l] < len(ToSeq(new_of))
                                       and ToSeq(new_of)[z] >= 0
                                       and ToSeq(new_of)[ToSeq(dst)[l]] >= 0,
                                       in_blk(ToSeq(start2), ToSeq(new_of)[z],
                                              ToSeq(pos2)[l])),
                               [[in_blk(ToSeq(start), z, l)]]))),
        [[ToSeq(pos2)[l]]]))))
    if x >= len(new_of):                     # x has no entry in new_of: nothing to check
        return True
    i = new_of[x]                            # the new number of x (or -1)
    if i < 0:                                # x is deleted: nothing to check
        return True
    if i + 1 >= len(start2):                 # Math: i+1 < |st2| (block2(i) readable), else reject
        return False
    # Math: nw[x] = i
    # Why (hint): the list read, as a sequence entry (the term the postcondition uses).
    Assert(ToSeq(new_of)[x] == i)
    lo2 = start2[i]                          # block2(i) = [lo2, hi2)
    hi2 = start2[i + 1]
    # Math: |start| = n+1 ∧ 0 ≤ start[x] ≤ start[x+1] ≤ T
    # Why (hint): blocks_ok at x, so block(x) is a valid range. start[x + 1] comes first: it is
    #      the trigger of blocks_ok's ∀.
    Assert(len(start) == n + 1 and start[x + 1] <= len(pos2) and 0 <= start[x]
           and start[x] <= start[x + 1])
    k = start[x]                             # first transition of x
    hi = start[x + 1]                        # one past the last
    while k < hi:                            # each transition of x
        # Why: read access, kept through the loop.
        Invariant(Acc(list_pred(start), 1 / 8) and Acc(list_pred(dst), 1 / 8)
                  and Acc(list_pred(new_of), 1 / 8) and Acc(list_pred(start2), 1 / 8)
                  and Acc(list_pred(pos2), 1 / 8))
        # Math: measure hi - k + 1.
        # Why: k goes up by 1, up to hi.
        Invariant(MustTerminate(hi - k + 1))
        # Math: |p2| = |ds| ∧ x < |nw| ∧ nw[x] = i ≥ 0 ∧ block2(i) = [lo2, hi2)
        #       ∧ start[x] ≤ k ≤ hi = start[x+1] ≤ T
        # Why: kept; k inside block(x).
        Invariant(len(pos2) == len(dst) and 0 <= x and x < len(new_of)
                  and ToSeq(new_of)[x] == i and i >= 0 and i + 1 < len(start2)
                  and lo2 == ToSeq(start2)[i] and hi2 == ToSeq(start2)[i + 1]
                  and len(start) == n + 1 and x < n and ToSeq(start)[x] <= k and k <= hi
                  and hi == ToSeq(start)[x + 1] and hi <= len(pos2) and 0 <= ToSeq(start)[x])
        # Math: ∀ l ∈ [0,T). ∀ z. l ∈ block(z) ∧ z = x ∧ l < k ∧ ... → p2[l] ∈ block2(nw[z])
        # Why: the postcondition for the transitions of x checked so far.
        Invariant(Forall(int, lambda l: (Implies(
            0 <= l and l < len(ToSeq(pos2)),
            Forall(int, lambda z: (Implies(in_blk(ToSeq(start), z, l) and z == x and l < k
                                           and 0 <= z and z < len(ToSeq(new_of))
                                           and l < len(ToSeq(dst)) and 0 <= ToSeq(dst)[l]
                                           and ToSeq(dst)[l] < len(ToSeq(new_of))
                                           and ToSeq(new_of)[z] >= 0
                                           and ToSeq(new_of)[ToSeq(dst)[l]] >= 0,
                                           in_blk(ToSeq(start2), ToSeq(new_of)[z],
                                                  ToSeq(pos2)[l])),
                                   [[in_blk(ToSeq(start), z, l)]]))),
            [[ToSeq(pos2)[l]]])))
        y = dst[k]                           # the target of k
        # Math: ds[k] = y
        # Why (hint): the list read, as a sequence entry.
        Assert(ToSeq(dst)[k] == y)
        if 0 <= y and y < len(new_of):       # y has an entry in new_of
            if new_of[y] >= 0:               # the target is kept: k must be copied into i
                j = pos2[k]                  # where k is claimed to be copied
                if j < lo2 or j >= hi2:      # Math: j ∈ block2(i), else reject
                    return False
                # Math: p2[k] = j ∧ in_blk(st2, nw[x], j)
                # Why (hint): the read and the test, as the terms the invariant uses.
                Assert(ToSeq(pos2)[k] == j and in_blk(ToSeq(start2), ToSeq(new_of)[x], j))
        nk = k + 1                           # the next transition (a variable: the int note)
        k = nk
    return True


# check_keep: for each old state x, its block (check_keep_block).
def check_keep(n: int, start: List[int], dst: List[int], new_of: List[int],
               start2: List[int], pos2: List[int]) -> bool:
    """True only if keep_ok."""
    # Why: read access.
    Requires(Acc(list_pred(start), 1 / 4) and Acc(list_pred(dst), 1 / 4)
             and Acc(list_pred(new_of), 1 / 4) and Acc(list_pred(start2), 1 / 4)
             and Acc(list_pred(pos2), 1 / 4))
    # Math: termination measure 3.
    # Why: one loop, calling check_keep_block (measure 2).
    Requires(MustTerminate(3))
    # Math: blocks_ok(n, start, |p2|) ∧ |p2| = |ds|
    # Why: block(x) is a valid range of positions of pos2 and dst.
    Requires(blocks_ok(n, start, len(pos2)) and len(pos2) == len(dst))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 4) and Acc(list_pred(dst), 1 / 4)
            and Acc(list_pred(new_of), 1 / 4) and Acc(list_pred(start2), 1 / 4)
            and Acc(list_pred(pos2), 1 / 4))
    # Math: Result → keep_ok(st, ds, nw, st2, p2)
    # Why: the fact checked.
    Ensures(Implies(Result(), keep_ok(ToSeq(start), ToSeq(dst), ToSeq(new_of), ToSeq(start2),
                                      ToSeq(pos2))))
    x = 0                                    # the old source state
    while x < n:                             # each old state
        # Why: read access, kept through the loop.
        Invariant(Acc(list_pred(start), 1 / 4) and Acc(list_pred(dst), 1 / 4)
                  and Acc(list_pred(new_of), 1 / 4) and Acc(list_pred(start2), 1 / 4)
                  and Acc(list_pred(pos2), 1 / 4))
        # Math: measure n - x + 1.
        # Why: x goes up by 1.
        Invariant(MustTerminate(n - x + 1))
        # Math: blocks_ok(n, start, |p2|) ∧ |p2| = |ds| ∧ 0 ≤ x ≤ n
        # Why: the precondition, kept; x in range.
        Invariant(blocks_ok(n, start, len(pos2)) and len(pos2) == len(dst)
                  and 0 <= x and x <= n)
        # Math: ∀ k ∈ [0,T). ∀ z < x. k ∈ block(z) ∧ z ∈ [0,|nw|) ∧ ds[k] ∈ [0,|nw|)
        #                    ∧ nw[z] ≥ 0 ∧ nw[ds[k]] ≥ 0 → p2[k] ∈ block2(nw[z])
        # Why: keep_ok for the old states checked so far. Triggers as in keep_ok.
        Invariant(Forall(int, lambda k: (Implies(
            0 <= k and k < len(ToSeq(pos2)),
            Forall(int, lambda z: (Implies(in_blk(ToSeq(start), z, k) and z < x
                                           and 0 <= z and z < len(ToSeq(new_of))
                                           and k < len(ToSeq(dst)) and 0 <= ToSeq(dst)[k]
                                           and ToSeq(dst)[k] < len(ToSeq(new_of))
                                           and ToSeq(new_of)[z] >= 0
                                           and ToSeq(new_of)[ToSeq(dst)[k]] >= 0,
                                           in_blk(ToSeq(start2), ToSeq(new_of)[z],
                                                  ToSeq(pos2)[k])),
                                   [[in_blk(ToSeq(start), z, k)]]))),
            [[ToSeq(pos2)[k]]])))
        if not check_keep_block(n, x, start, dst, new_of, start2, pos2):  # block(x), else reject
            return False
        nx = x + 1                           # the next state (a variable: the int note)
        # Math: ∀ k ∈ [0,T). ∀ z < nx. k ∈ block(z) ∧ ... → p2[k] ∈ block2(nw[z])
        # Why (hint): z < x is the old part; z = x is check_keep_block's postcondition.
        Assert(Forall(int, lambda k: (Implies(
            0 <= k and k < len(ToSeq(pos2)),
            Forall(int, lambda z: (Implies(in_blk(ToSeq(start), z, k) and z < nx
                                           and 0 <= z and z < len(ToSeq(new_of))
                                           and k < len(ToSeq(dst)) and 0 <= ToSeq(dst)[k]
                                           and ToSeq(dst)[k] < len(ToSeq(new_of))
                                           and ToSeq(new_of)[z] >= 0
                                           and ToSeq(new_of)[ToSeq(dst)[k]] >= 0,
                                           in_blk(ToSeq(start2), ToSeq(new_of)[z],
                                                  ToSeq(pos2)[k])),
                                   [[in_blk(ToSeq(start), z, k)]]))),
            [[ToSeq(pos2)[k]]])))
        x = nx
    # Math: keep_ok(st, ds, nw, st2, p2)
    # Why (hint): at x = n every block counts (in_blk(st, z, k) gives z + 1 < n + 1).
    Assert(keep_ok(ToSeq(start), ToSeq(dst), ToSeq(new_of), ToSeq(start2), ToSeq(pos2)))
    return True


# --- the whole check -------------------------------------------------------------------------


# check_delete: accepts the result only if all seven facts hold and start2 is a valid block
# structure. Called by the public delete_states (ops_aut/basic_ops.py) before the result is
# validated and returned.
def check_delete(n: int, start: List[int], evt: List[int], dst: List[int], init: List[bool],
                 marked: List[bool], dele: List[bool], new_of: List[int], old_of: List[int],
                 start2: List[int], evt2: List[int], dst2: List[int], init2: List[bool],
                 marked2: List[bool], src2: List[int], pos2: List[int]) -> bool:
    """True only if the result lists are exactly the automaton with the states `dele` deleted."""
    # Why: read access.
    Requires(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2)
             and Acc(list_pred(dst), 1 / 2) and Acc(list_pred(init), 1 / 2)
             and Acc(list_pred(marked), 1 / 2) and Acc(list_pred(dele), 1 / 2)
             and Acc(list_pred(new_of), 1 / 2) and Acc(list_pred(old_of), 1 / 2)
             and Acc(list_pred(start2), 1 / 2) and Acc(list_pred(evt2), 1 / 2)
             and Acc(list_pred(dst2), 1 / 2) and Acc(list_pred(init2), 1 / 2)
             and Acc(list_pred(marked2), 1 / 2) and Acc(list_pred(src2), 1 / 2)
             and Acc(list_pred(pos2), 1 / 2))
    # Math: termination measure 4.
    # Why: calls the checkers (measures 2 and 3).
    Requires(MustTerminate(4))
    # Math: blocks_ok(n, start, T)
    # Why: a validated automaton (check_automaton proves it).
    Requires(blocks_ok(n, start, len(dst)))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2)
            and Acc(list_pred(dst), 1 / 2) and Acc(list_pred(init), 1 / 2)
            and Acc(list_pred(marked), 1 / 2) and Acc(list_pred(dele), 1 / 2)
            and Acc(list_pred(new_of), 1 / 2) and Acc(list_pred(old_of), 1 / 2)
            and Acc(list_pred(start2), 1 / 2) and Acc(list_pred(evt2), 1 / 2)
            and Acc(list_pred(dst2), 1 / 2) and Acc(list_pred(init2), 1 / 2)
            and Acc(list_pred(marked2), 1 / 2) and Acc(list_pred(src2), 1 / 2)
            and Acc(list_pred(pos2), 1 / 2))
    # Math: Result → blocks_ok(n', start2, T') ∧ renum_ok ∧ order_ok
    # Why: the new states and their blocks.
    Ensures(Implies(Result(), blocks_ok(len(old_of), start2, len(src2))
                    and renum_ok(n, ToSeq(dele), ToSeq(new_of), ToSeq(old_of))
                    and order_ok(ToSeq(old_of))))
    # Math: Result → |in2| = |od| ∧ ∀ j ∈ [0,|od|): od[j] ∈ [0,|in|) ∧ (in2[j] ↔ in[od[j]])
    # Why: the flag fact for init (the Lean IsDeletion.X0). Trigger od[j].
    Ensures(Implies(Result(), len(init2) == len(old_of)
                    and Forall(int, lambda j: (Implies(0 <= j and j < len(old_of),
                                                       0 <= old_of[j] and old_of[j] < len(init)
                                                       and Implies(init2[j], init[old_of[j]])
                                                       and Implies(init[old_of[j]], init2[j])),
                                               [[old_of[j]]]))))
    # Math: Result → |mk2| = |od| ∧ ∀ j ∈ [0,|od|): od[j] ∈ [0,|mk|) ∧ (mk2[j] ↔ mk[od[j]])
    # Why: the flag fact for marked (the Lean IsDeletion.marked). Trigger od[j].
    Ensures(Implies(Result(), len(marked2) == len(old_of)
                    and Forall(int, lambda j: (Implies(0 <= j and j < len(old_of),
                                                       0 <= old_of[j] and old_of[j] < len(marked)
                                                       and Implies(marked2[j], marked[old_of[j]])
                                                       and Implies(marked[old_of[j]], marked2[j])),
                                               [[old_of[j]]]))))
    # Math: Result → ∀ l ∈ [0,T'). ∀ z. l ∈ block2(z) ∧ z < |od| → z ∈ [0,|od|) ∧ s2[l] ∈ block(od[z])
    # Why: the own2 fact: each new transition copies one out of the right old state.
    Ensures(Implies(Result(), Forall(int, lambda l: (Implies(
        0 <= l and l < len(ToSeq(src2)),
        Forall(int, lambda z: (Implies(in_blk(ToSeq(start2), z, l) and z < len(ToSeq(old_of)),
                                       0 <= z and z < len(ToSeq(old_of))
                                       and in_blk(ToSeq(start), ToSeq(old_of)[z], ToSeq(src2)[l])),
                               [[in_blk(ToSeq(start2), z, l)]]))),
        [[ToSeq(src2)[l]]]))))
    # Math: Result → trans_ok ∧ pos2_ok ∧ keep_ok
    # Why: the new transitions are exactly the old ones between kept states (see the file
    #      docstring for how these give the Lean IsDeletion).
    Ensures(Implies(Result(), trans_ok(ToSeq(evt), ToSeq(dst), ToSeq(new_of), ToSeq(evt2),
                                       ToSeq(dst2), ToSeq(src2), ToSeq(pos2))
                    and pos2_ok(ToSeq(src2), ToSeq(pos2))
                    and keep_ok(ToSeq(start), ToSeq(dst), ToSeq(new_of), ToSeq(start2),
                                ToSeq(pos2))))
    if len(pos2) != len(dst):                # Math: |p2| = T, else reject
        return False
    if not check_blocks(len(old_of), start2, len(src2)):     # Math: blocks_ok(n', start2, T')
        return False
    if not check_renum(n, dele, new_of, old_of):     # Math: renum_ok, else reject
        return False
    if not check_order(old_of):              # Math: order_ok, else reject
        return False
    if not check_flag(old_of, init, init2):  # Math: the flag fact for init, else reject
        return False
    if not check_flag(old_of, marked, marked2):  # Math: the flag fact for marked, else reject
        return False
    if not check_trans(evt, dst, new_of, evt2, dst2, src2, pos2):    # Math: trans_ok
        return False
    # Math: |start| = n+1
    # Why (hint): from blocks_ok(n, start, T), for check_own2's precondition.
    Assert(len(start) == n + 1)
    if not check_own2(n, start, old_of, start2, src2):       # Math: the own2 fact, else reject
        return False
    if not check_pos2(src2, pos2):           # Math: pos2_ok, else reject
        return False
    # Math: blocks_ok(n, start, |p2|)
    # Why (hint): the same as blocks_ok(n, start, T) with |p2| = T (a different term for the
    #      same number), for check_keep's precondition.
    Assert(blocks_ok(n, start, len(pos2)))
    if not check_keep(n, start, dst, new_of, start2, pos2):  # Math: keep_ok, else reject
        return False
    return True
