"""
Verified composition of two encoded automata: parallel and product (certisc-proof/spec/parallel.md).

A verified forward search over pairs of states (spec §3): the search itself is the proved code,
and what it writes is already a valid automaton (no validation pass afterwards).

Lean target: `IsComposition` (DESopsProof/Parallel.lean): step_sound, step_complete,
init_sound, init_complete, marked, E, Euc, Euo.

Encoding as in core_aut/verified_core/check.py. Input r (r = 1, 2): states 0 .. n_r-1; state x owns
the positions block_r(x) = [start_r[x], start_r[x+1]) of evt_r / dst_r, sorted by event.
Output event numbers (spec §3, "event numbering"): G1's own numbers 0 .. m1-1, then the events
only G2 has, m1 .. m-1, in G2's order. So an event of G1 needs no map; G2's event e2 has the
output number map2[e2] (built by trusted code from the event names, spec question 3).

Verify, from certisc-lib/ (Python >= 3.12, `verify` extra, Java):

    nagini src/ops_aut/verified_ops/compose.py

Math notation used in the comments:
    [a, b)        the integers a, a+1, ..., b-1
    |l|           the length of list (or sequence) l
    l · [y]       l with y appended
    block_r(x)    [start_r[x], start_r[x+1]), the transitions of state x of G_r
    mode[e]       0 both, 1 left (G1 alone), 2 right (G2 alone), 3 none (Lean: Mode)
    φ(i)          (p1[i], p2[i]), the pair of output state i (Lean: φ)
    l_old         the value of l when the method was called (Old(...))
    F ⊑ L         L extends F: |F| ≤ |L| and L[t] = F[t] for t < |F| (`ext`)

Output lists of the search (all only appended to):
    p1, p2        labels: output state i is the pair (p1[i], p2[i])
    start         start[i]: first transition of state i (one entry per processed state, + 1)
    evt, dst      output transition k: evt[k] (output number), target dst[k]
    own           own[k]: the state that transition k leaves (a witness for the proof)
    src1, src2    src_r[k]: the input transition that k uses (-1: that side stays)
    slot, dl, dr  completeness witnesses (see compl_ok)

How to read the contracts (all removed before the code runs; core_aut/trusted/_strip.py):
- Requires(P) / Ensures(P)   precondition (the caller makes P true) / postcondition.
- Invariant(P)               loop invariant: true before the loop and after every iteration.
- Assert(P)                  a proof step, checked by Nagini. "Why (hint)": a fact Nagini can
                             prove but would not find by itself.
- Acc(list_pred(l), q)       permission to use list l: q = 1 read and write; q < 1 read only.
  Acc(dict_pred(d), q)       the same for a dict. (A permission, not a formula: no Math.)
- MustTerminate(t)           the method (or loop) terminates; t decreases, and a method only
                             calls methods with a smaller t.
- ToSeq(l)                   the contents of list l as a value (a sequence).
- PSeq[int]                  the type of such a value.
- Old(e)                     e when the method was called.
- Implies(a, b)              a → b.
- Forall(int, lambda i: (P, [[t]]))   ∀ i ∈ ℤ: P; used by Nagini for an i where the term t
                             appears (the trigger). Forall2: two variables.
- @Pure                      a side-effect-free function, usable in contracts (a definition).
- Lemma                      a method that only proves a fact (its calls are removed before
                             running).

Map of the file:
- specification: ext, step_in1, step_in2, move, sound_ok, labels_ok, own_ok, sorted_flat, cur_ok;
- lemmas: keep_* (an invariant survives one kind of append), ext_trans, ext_app;
- find_or_add, emit: the only methods that write the labels and the transitions.
"""

from typing import Dict, List

from nagini_contracts.contracts import *
from nagini_contracts.obligations import MustTerminate

# appended: "list o is o0 with y appended", one fact per append (shared with reach.py).
from ops_aut.verified_ops.reach import appended


# --- specification ---------------------------------------------------------------------------
# The inputs are passed as sequences (ToSeq of the lists): values, so they stay known unchanged
# while the output lists grow (the lesson of reach.py). Formulas over list reads are written out
# in full inside quantifiers (not through step_in1 / move): Nagini passes ints to functions as
# objects, and move(.., p1[own[k]], ..) inside a quantifier did not match move(.., p1[i], ..)
# (a run hung on this, 2026-10-29); list reads compare by value.


# ext: "L extends F" (F ⊑ L): the snapshot F of a list is still its prefix.
# Used in: the search keeps facts about finished parts on snapshots (values taken earlier) and
# carries them over with ext, instead of re-proving them after every append.
@Pure
def ext(F: PSeq[int], L: PSeq[int]) -> bool:
    """L starts with F."""
    # Math: |F| ≤ |L| ∧ ∀ t ∈ [0,|F|): L[t] = F[t]
    # Why: the old entries are unchanged. Trigger L[t]: a read of the current list gives the
    #      snapshot's entry, which then triggers the facts stated on the snapshot.
    return (len(F) <= len(L)
            and Forall(int, lambda t: (Implies(0 <= t and t < len(F), L[t] == F[t]), [[L[t]]])))


# step_in1 / step_in2: one transition of an input automaton, in output event numbers.
# Used in: move.
@Pure
def step_in1(st: PSeq[int], ev: PSeq[int], ds: PSeq[int], x: int, e: int, k: int,
             y: int) -> bool:
    """Transition k of G1 goes from x to y with the event e (G1's numbers are the output's)."""
    # Math: x ∈ [0,|start1|-1) ∧ k ∈ block1(x) ∧ k ∈ [0,|dst1|) ∧ k < |evt1|
    #       ∧ evt1[k] = e ∧ dst1[k] = y                                       (x --e-->_k y)
    # Why: the Lean `y ∈ f1(x, e)`, with the transition k as the witness. Bounds first, so
    #      every read is valid.
    return (0 <= x and x + 1 < len(st) and st[x] <= k and k < st[x + 1]
            and 0 <= k and k < len(ds) and k < len(ev) and ev[k] == e and ds[k] == y)


@Pure
def step_in2(st: PSeq[int], ev: PSeq[int], ds: PSeq[int], mp: PSeq[int], x: int, e: int,
             k: int, y: int) -> bool:
    """Transition k of G2 goes from x to y with the output event e (= map2[evt2[k]])."""
    # Math: x ∈ [0,|start2|-1) ∧ k ∈ block2(x) ∧ k ∈ [0,|dst2|) ∧ k < |evt2|
    #       ∧ evt2[k] ∈ [0,|map2|) ∧ map2[evt2[k]] = e ∧ dst2[k] = y
    # Why: the Lean `y ∈ f2(x, e)`, in output numbers, with the witness k.
    return (0 <= x and x + 1 < len(st) and st[x] <= k and k < st[x + 1]
            and 0 <= k and k < len(ds) and k < len(ev)
            and 0 <= ev[k] and ev[k] < len(mp) and mp[ev[k]] == e and ds[k] == y)


# move: one move of the composition, by mode (Lean: q ∈ syncF mode f1 f2 p e).
# Used in: the preconditions of emit and keep_sound_trans (arguments: plain variables only).
@Pure
def move(st1: PSeq[int], ev1: PSeq[int], ds1: PSeq[int],
         st2: PSeq[int], ev2: PSeq[int], ds2: PSeq[int], mp2: PSeq[int],
         m: int, x1: int, x2: int, e: int, y1: int, y2: int, k1: int, k2: int) -> bool:
    """(x1, x2) --e--> (y1, y2) is a move with mode m, using transitions k1 of G1 and k2 of G2
    (-1 for a side that stays)."""
    # Math: (m = 0 ∧ x1 --e-->_k1 y1 ∧ x2 --e-->_k2 y2)
    #     ∨ (m = 1 ∧ x1 --e-->_k1 y1 ∧ k2 = -1 ∧ y2 = x2)
    #     ∨ (m = 2 ∧ k1 = -1 ∧ y1 = x1 ∧ x2 --e-->_k2 y2)
    # Why: the three non-empty cases of syncF (Lean: mem_syncF_both, mem_syncF_left,
    #      mem_syncF_right); mode 3 (none) has no move (syncF_none).
    return ((m == 0 and step_in1(st1, ev1, ds1, x1, e, k1, y1)
             and step_in2(st2, ev2, ds2, mp2, x2, e, k2, y2))
            or (m == 1 and step_in1(st1, ev1, ds1, x1, e, k1, y1)
                and k2 == -1 and y2 == x2)
            or (m == 2 and k1 == -1 and y1 == x1
                and step_in2(st2, ev2, ds2, mp2, x2, e, k2, y2)))


# sound_ok: every output transition written so far is a move (Lean: step_sound).
# Used in: the invariants of the search; find_or_add and emit keep it (keep_sound_state,
# keep_sound_trans).
# @Opaque: Nagini does not unfold the definition unless asked (Reveal). Most methods only pass the
# fact on unchanged, which is then a single term; only the keep_* lemmas look inside. (Without
# it, re-proving the unfolded formula at every call made a walk run past 5 minutes; and folding
# the definition back from its body failed erratically, 2026-10-30.)
@Opaque
@Pure
def sound_ok(st1: PSeq[int], ev1: PSeq[int], ds1: PSeq[int],
             st2: PSeq[int], ev2: PSeq[int], ds2: PSeq[int], mp2: PSeq[int], md: PSeq[int],
             P1: PSeq[int], P2: PSeq[int], Ev: PSeq[int], Ds: PSeq[int], Ow: PSeq[int],
             S1: PSeq[int], S2: PSeq[int]) -> bool:
    """Each output transition k (from own[k] to dst[k], event evt[k]) is a move between the pairs
    of its two states, with the input transitions src1[k], src2[k]."""
    # Math: |p2| = |p1| ∧ |dst| = |own| = |src1| = |src2| = |evt|
    # Why: so every read below is of an existing entry.
    # Math: ∀ k ∈ [0,|evt|), with i = own[k], y = dst[k], e = evt[k], m = mode[e]:
    #         i, y ∈ [0,|p1|) ∧ e ∈ [0,|mode|) ∧ m ∈ [0,2]
    #         ∧ (m ≤ 1 → p1[i] --e-->_{src1[k]} p1[y])  ∧ (m = 2 → src1[k] = -1 ∧ p1[y] = p1[i])
    #         ∧ (m ≠ 1 → p2[i] --e-->_{src2[k]} p2[y])  ∧ (m = 1 → src2[k] = -1 ∧ p2[y] = p2[i])
    #      (the same as move(m, φ(i), e, φ(y), src1[k], src2[k]), side by side)
    # Why: Lean `step_sound`: y ∈ f_H(i, e) → φ(y) ∈ syncF mode f1 f2 (φ(i)) e; the witnesses
    #      src1, src2 replace the "∃ transition". Written out in full (see the note above `ext`).
    #      Trigger own[k]: read wherever a source is used.
    return (len(P2) == len(P1) and len(Ds) == len(Ev) and len(Ow) == len(Ev) and len(S1) == len(Ev)
            and len(S2) == len(Ev)
            and Forall(int, lambda k: (Implies(
                0 <= k and k < len(Ev),
                0 <= Ow[k] and Ow[k] < len(P1) and 0 <= Ds[k] and Ds[k] < len(P1)
                and 0 <= Ev[k] and Ev[k] < len(md) and 0 <= md[Ev[k]] and md[Ev[k]] <= 2
                # G1 side: moves by src1[k] (modes 0, 1), or stays (mode 2)
                and Implies(md[Ev[k]] <= 1,
                            0 <= P1[Ow[k]] and P1[Ow[k]] + 1 < len(st1)
                            and st1[P1[Ow[k]]] <= S1[k] and S1[k] < st1[P1[Ow[k]] + 1]
                            and 0 <= S1[k] and S1[k] < len(ds1) and S1[k] < len(ev1)
                            and ev1[S1[k]] == Ev[k] and ds1[S1[k]] == P1[Ds[k]])
                and Implies(md[Ev[k]] == 2, S1[k] == -1 and P1[Ds[k]] == P1[Ow[k]])
                # G2 side: moves by src2[k] (modes 0, 2), or stays (mode 1)
                and Implies(md[Ev[k]] != 1,
                            0 <= P2[Ow[k]] and P2[Ow[k]] + 1 < len(st2)
                            and st2[P2[Ow[k]]] <= S2[k] and S2[k] < st2[P2[Ow[k]] + 1]
                            and 0 <= S2[k] and S2[k] < len(ds2) and S2[k] < len(ev2)
                            and 0 <= ev2[S2[k]] and ev2[S2[k]] < len(mp2)
                            and mp2[ev2[S2[k]]] == Ev[k] and ds2[S2[k]] == P2[Ds[k]])
                and Implies(md[Ev[k]] == 1, S2[k] == -1 and P2[Ds[k]] == P2[Ow[k]])),
                [[Ow[k]]])))


# sizes_ok: one entry per transition in each transition list, one per state in p1, p2.
# Used in: next to sound_ok in every contract (sound_ok is opaque, so its own size facts are
# hidden; the contracts need them to read the lists).
@Pure
def sizes_ok(P1: PSeq[int], P2: PSeq[int], Ev: PSeq[int], Ds: PSeq[int], Ow: PSeq[int],
             S1: PSeq[int], S2: PSeq[int]) -> bool:
    """The label lists and the transition lists have consistent lengths."""
    # Math: |p2| = |p1| ∧ |dst| = |own| = |src1| = |src2| = |evt|
    # Why: so the lists can be read at the same positions.
    return (len(P2) == len(P1) and len(Ds) == len(Ev) and len(Ow) == len(Ev)
            and len(S1) == len(Ev) and len(S2) == len(Ev))


# labels_ok: every label is a pair of input states.
# Used in: the search (reading start1[p1[h]] needs p1[h] to be a state); find_or_add keeps it.
@Pure
def labels_ok(n1: int, n2: int, P1: PSeq[int], P2: PSeq[int]) -> bool:
    """p1[i] is a state of G1 and p2[i] a state of G2."""
    # Math: |p2| = |p1| ∧ ∀ i ∈ [0,|p1|): p1[i] ∈ [0,n1) ∧ p2[i] ∈ [0,n2)
    # Why: φ(i) ∈ X1 × X2 (Lean: φ : Fin H.n → Fin G1.n × Fin G2.n). Trigger p1[i].
    return (len(P2) == len(P1)
            and Forall(int, lambda i: (Implies(0 <= i and i < len(P1),
                                               0 <= P1[i] and P1[i] < n1
                                               and 0 <= P2[i] and P2[i] < n2), [[P1[i]]])))


# own_ok: own agrees with the blocks of the processed states 0 .. h-1 and the current one h.
# Used in: the search; emit keeps it, close_state extends it; at the end it gives
# "k ∈ block(x) ⟺ own[k] = x" (with mono_ok).
@Pure
def own_ok(St: PSeq[int], Ow: PSeq[int], h: int) -> bool:
    """start has the h+1 block starts so far; each transition k is inside the block of own[k]
    (the block of the current state h is still open)."""
    # Math: |start| = h+1 ∧ 0 ≤ start[h] ≤ |own|
    # Why: the starts of states 0 .. h; the current block begins at start[h].
    # Math: ∀ k ∈ [0,|own|): own[k] ∈ [0,h] ∧ start[own[k]] ≤ k ∧ (own[k] < h → k < start[own[k]+1])
    # Why: k lies in the block of its state (closed blocks have their end start[own[k]+1]).
    #      Trigger own[k].
    return (h >= 0 and len(St) == h + 1 and 0 <= St[h] and St[h] <= len(Ow)
            and Forall(int, lambda k: (Implies(
                0 <= k and k < len(Ow),
                0 <= Ow[k] and Ow[k] <= h and St[Ow[k]] <= k
                and Implies(Ow[k] < h, k < St[Ow[k] + 1])), [[Ow[k]]])))


# sorted_flat: the transitions of one state are in event order (strictly, if dt).
# Used in: the search; emit keeps it; at the end it gives sorted_ok and det_ok of check.py.
@Pure
def sorted_flat(Ow: PSeq[int], Ev: PSeq[int], dt: bool) -> bool:
    """Two transitions j < i of the same state: evt[j] ≤ evt[i], and < if dt."""
    # Math: |own| = |evt| ∧
    #       ∀ j, i: 0 ≤ j < i < |evt| ∧ own[j] = own[i] → evt[j] < evt[i] ∨ (¬dt ∧ evt[j] = evt[i])
    # Why: every block sorted (the encoding's sorted_ok), and with dt no event twice (det_ok).
    #      Pairwise, not only neighbours: Nagini cannot chain neighbour facts (induction).
    #      Trigger: the two reads evt[j], evt[i].
    return (len(Ow) == len(Ev)
            and Forall2(int, int, lambda j, i: (Implies(
                0 <= j and j < i and i < len(Ev) and Ow[j] == Ow[i],
                Ev[j] < Ev[i] or (not dt and Ev[j] == Ev[i])), [[Ev[j], Ev[i]]])))


# cur_ok: the transitions of the current state h so far have events ≤ last.
# Used in: the search; emit keeps it (with last = the event just emitted).
@Pure
def cur_ok(Ow: PSeq[int], Ev: PSeq[int], h: int, last: int) -> bool:
    """Every transition of state h written so far has an event ≤ last."""
    # Math: |own| = |evt| ∧ ∀ j ∈ [0,|evt|): own[j] = h → evt[j] ≤ last
    # Why: so a next event e ≥ last keeps the block sorted (and e > last keeps it strict).
    #      Trigger evt[j].
    return (len(Ow) == len(Ev)
            and Forall(int, lambda j: (Implies(0 <= j and j < len(Ev) and Ow[j] == h,
                                               Ev[j] <= last), [[Ev[j]]])))


# walk_ok: the invariant of the search while state h is being processed, as one opaque fact.
# Used in: find_or_add, emit and the walks (they pass it on; find_or_add and emit open it).
# Why one opaque fact: a loop that carried these six facts separately (and more) could no longer
# prove simple facts such as a list read in range (2026-10-30); bundled, a caller sees one term.
@Opaque
@Pure
def walk_ok(n1: int, n2: int, st1: PSeq[int], ev1: PSeq[int], ds1: PSeq[int],
            st2: PSeq[int], ev2: PSeq[int], ds2: PSeq[int], mp2: PSeq[int], md: PSeq[int],
            St: PSeq[int], P1: PSeq[int], P2: PSeq[int], Ev: PSeq[int], Ds: PSeq[int],
            Ow: PSeq[int], S1: PSeq[int], S2: PSeq[int], h: int, last: int, dt: bool) -> bool:
    """The labels, sizes, soundness, blocks, order and current-block facts."""
    # Math: labels_ok ∧ sizes_ok ∧ sound_ok ∧ own_ok(start, own, h) ∧ sorted_flat(own, evt, dt)
    #       ∧ cur_ok(own, evt, h, last)
    # Why: everything the search keeps true about its output lists (see each definition).
    return (labels_ok(n1, n2, P1, P2) and sizes_ok(P1, P2, Ev, Ds, Ow, S1, S2)
            and sound_ok(st1, ev1, ds1, st2, ev2, ds2, mp2, md, P1, P2, Ev, Ds, Ow, S1, S2)
            and own_ok(St, Ow, h) and sorted_flat(Ow, Ev, dt) and cur_ok(Ow, Ev, h, last))


# --- lemmas ----------------------------------------------------------------------------------


# ext_trans: ⊑ is transitive.
# Used in: the search, to carry a snapshot over a call that extends a list.
def ext_trans(F: PSeq[int], M: PSeq[int], L: PSeq[int]) -> None:
    """Lemma: F ⊑ M and M ⊑ L give F ⊑ L."""
    # Math: termination measure 1.
    # Why: no loops and no calls.
    Requires(MustTerminate(1))
    # Math: F ⊑ M ∧ M ⊑ L
    # Why: the two steps.
    Requires(ext(F, M) and ext(M, L))
    # Math: F ⊑ L
    # Why: the fact.
    Ensures(ext(F, L))
    # Math: ∀ t ∈ [0,|F|): L[t] = M[t] = F[t]
    # Why (hint): the chain at each t (t < |F| ≤ |M|). Trigger L[t], as in ext.
    Assert(Forall(int, lambda t: (Implies(0 <= t and t < len(F), L[t] == F[t]), [[L[t]]])))


# keep_ext: an append keeps a snapshot a prefix.
# Used in: the search, after each append.
def keep_ext(F: PSeq[int], L0: PSeq[int], L: PSeq[int], y: int) -> None:
    """Lemma: F ⊑ L0 and L = L0 · [y] give F ⊑ L."""
    # Math: termination measure 1.
    # Why: no loops and no calls.
    Requires(MustTerminate(1))
    # Math: F ⊑ L0 ∧ L = L0 · [y]
    # Why: the snapshot before, and the append.
    Requires(ext(F, L0) and appended(L0, L, y))
    # Math: F ⊑ L
    # Why: the fact.
    Ensures(ext(F, L))
    # Math: ∀ t ∈ [0,|F|): L[t] = L0[t] = F[t]
    # Why (hint): the append keeps entries below |L0| ≥ |F|. Trigger L[t].
    Assert(Forall(int, lambda t: (Implies(0 <= t and t < len(F), L[t] == F[t]), [[L[t]]])))


# ext_app: L0 ⊑ L0 · [y].
# Used in: find_or_add (its postcondition says "the labels only grew").
def ext_app(L0: PSeq[int], L: PSeq[int], y: int) -> None:
    """Lemma: an append extends the list."""
    # Math: termination measure 1.
    # Why: no loops and no calls.
    Requires(MustTerminate(1))
    # Math: L = L0 · [y]
    # Why: the append.
    Requires(appended(L0, L, y))
    # Math: L0 ⊑ L
    # Why: the fact.
    Ensures(ext(L0, L))
    # Math: ∀ t ∈ [0,|L0|): L[t] = L0[t]
    # Why (hint): appended's quantifier, restated with ext's trigger.
    Assert(Forall(int, lambda t: (Implies(0 <= t and t < len(L0), L[t] == L0[t]), [[L[t]]])))


# keep_sound_state: sound_all survives appending a new pair (y1, y2) to p1, p2.
# Used in: find_or_add.
# Idea: every old transition reads p1, p2 only at states < |p1_old|, which keep their pairs.
def keep_sound_state(st1: PSeq[int], ev1: PSeq[int], ds1: PSeq[int],
                     st2: PSeq[int], ev2: PSeq[int], ds2: PSeq[int], mp2: PSeq[int],
                     md: PSeq[int], P10: PSeq[int], P20: PSeq[int], P1: PSeq[int],
                     P2: PSeq[int], Ev: PSeq[int], Ds: PSeq[int], Ow: PSeq[int],
                     S1: PSeq[int], S2: PSeq[int], y1: int, y2: int) -> None:
    """Lemma: a new state does not change the moves of the existing transitions."""
    # Math: termination measure 1.
    # Why: no loops and no calls.
    Requires(MustTerminate(1))
    # Math: sound_all(p1_old, p2_old, ...)
    # Why: the invariant before.
    Requires(sizes_ok(P10, P20, Ev, Ds, Ow, S1, S2)
             and sound_ok(st1, ev1, ds1, st2, ev2, ds2, mp2, md, P10, P20, Ev, Ds, Ow, S1, S2))
    # Math: p1 = p1_old · [y1] ∧ p2 = p2_old · [y2]
    # Why: the update.
    Requires(appended(P10, P1, y1) and appended(P20, P2, y2))
    # Math: sound_all(p1, p2, ...)
    # Why: the invariant after: for each k, own[k], dst[k] < |p1_old|, so p1[own[k]] =
    #      p1_old[own[k]] (and the same for dst[k], and for p2): the move is the old one.
    Ensures(sizes_ok(P1, P2, Ev, Ds, Ow, S1, S2)
            and sound_ok(st1, ev1, ds1, st2, ev2, ds2, mp2, md, P1, P2, Ev, Ds, Ow, S1, S2))
    # Math: sound_ok(before) ⟹ its body
    # Why (hint): opens the opaque definition (the facts about each old transition).
    Assert(Reveal(sound_ok(st1, ev1, ds1, st2, ev2, ds2, mp2, md, P10, P20, Ev, Ds,
                           Ow, S1, S2)))
    # Math: sound_ok(after), from its body
    # Why (hint): closes the opaque definition (its body was just proved).
    Assert(Reveal(sound_ok(st1, ev1, ds1, st2, ev2, ds2, mp2, md, P1, P2, Ev, Ds, Ow, S1, S2)))


# keep_sound_trans: sound_all survives appending one transition that is a move.
# Used in: emit. In two parts: sound_old (the old positions, unchanged) and sound_new (the new
# position, a ground fact); as one proof it ran past 5 minutes (2026-10-30).
def sound_old(st1: PSeq[int], ev1: PSeq[int], ds1: PSeq[int],
              st2: PSeq[int], ev2: PSeq[int], ds2: PSeq[int], mp2: PSeq[int],
              md: PSeq[int], P1: PSeq[int], P2: PSeq[int],
              Ev0: PSeq[int], Ds0: PSeq[int], Ow0: PSeq[int], S10: PSeq[int],
              S20: PSeq[int], Ev: PSeq[int], Ds: PSeq[int], Ow: PSeq[int],
              S1: PSeq[int], S2: PSeq[int], i: int, e: int, j: int, k1: int,
              k2: int) -> None:
    """Lemma: after the appends, the old transitions are still moves."""
    # Math: termination measure 1.
    # Why: no loops and no calls.
    Requires(MustTerminate(1))
    # Math: sound_all(evt_old, dst_old, own_old, src1_old, src2_old)
    # Why: the invariant before.
    Requires(sizes_ok(P1, P2, Ev0, Ds0, Ow0, S10, S20)
             and sound_ok(st1, ev1, ds1, st2, ev2, ds2, mp2, md, P1, P2, Ev0, Ds0, Ow0, S10, S20))
    # Math: evt = evt_old · [e] ∧ dst = dst_old · [j] ∧ own = own_old · [i]
    #       ∧ src1 = src1_old · [k1] ∧ src2 = src2_old · [k2]
    # Why: the update: one entry added to each of the five lists.
    Requires(appended(Ev0, Ev, e) and appended(Ds0, Ds, j) and appended(Ow0, Ow, i)
             and appended(S10, S1, k1) and appended(S20, S2, k2))
    # Math: ∀ k ∈ [0,|evt_old|): transition k of the new lists is a move
    # Why: the old part of the invariant after.
    Ensures(Forall(int, lambda k: (Implies(
                0 <= k and k < len(Ev0),
                0 <= Ow[k] and Ow[k] < len(P1) and 0 <= Ds[k] and Ds[k] < len(P1)
                and 0 <= Ev[k] and Ev[k] < len(md) and 0 <= md[Ev[k]] and md[Ev[k]] <= 2
                # G1 side: moves by src1[k] (modes 0, 1), or stays (mode 2)
                and Implies(md[Ev[k]] <= 1,
                            0 <= P1[Ow[k]] and P1[Ow[k]] + 1 < len(st1)
                            and st1[P1[Ow[k]]] <= S1[k] and S1[k] < st1[P1[Ow[k]] + 1]
                            and 0 <= S1[k] and S1[k] < len(ds1) and S1[k] < len(ev1)
                            and ev1[S1[k]] == Ev[k] and ds1[S1[k]] == P1[Ds[k]])
                and Implies(md[Ev[k]] == 2, S1[k] == -1 and P1[Ds[k]] == P1[Ow[k]])
                # G2 side: moves by src2[k] (modes 0, 2), or stays (mode 1)
                and Implies(md[Ev[k]] != 1,
                            0 <= P2[Ow[k]] and P2[Ow[k]] + 1 < len(st2)
                            and st2[P2[Ow[k]]] <= S2[k] and S2[k] < st2[P2[Ow[k]] + 1]
                            and 0 <= S2[k] and S2[k] < len(ds2) and S2[k] < len(ev2)
                            and 0 <= ev2[S2[k]] and ev2[S2[k]] < len(mp2)
                            and mp2[ev2[S2[k]]] == Ev[k] and ds2[S2[k]] == P2[Ds[k]])
                and Implies(md[Ev[k]] == 1, S2[k] == -1 and P2[Ds[k]] == P2[Ow[k]])),
                [[Ow[k]]])))
    # Math: sound_ok(before) ⟹ its body
    # Why (hint): opens the opaque definition (the facts about each old transition).
    Assert(Reveal(sound_ok(st1, ev1, ds1, st2, ev2, ds2, mp2, md, P1, P2, Ev0, Ds0,
                           Ow0, S10, S20)))
    # Math: ∀ k ∈ [0,|evt_old|): the entries at k are the old ones
    # Why (hint): from appended; stated once for all five lists. Trigger own[k].
    Assert(Forall(int, lambda k: (Implies(0 <= k and k < len(Ev0),
                                          Ow[k] == Ow0[k] and Ev[k] == Ev0[k]
                                          and Ds[k] == Ds0[k] and S1[k] == S10[k]
                                          and S2[k] == S20[k]),
                                  [[Ow[k]]])))


def sound_new(st1: PSeq[int], ev1: PSeq[int], ds1: PSeq[int],
              st2: PSeq[int], ev2: PSeq[int], ds2: PSeq[int], mp2: PSeq[int],
              md: PSeq[int], P1: PSeq[int], P2: PSeq[int],
              Ev0: PSeq[int], Ds0: PSeq[int], Ow0: PSeq[int], S10: PSeq[int],
              S20: PSeq[int], Ev: PSeq[int], Ds: PSeq[int], Ow: PSeq[int],
              S1: PSeq[int], S2: PSeq[int], i: int, e: int, j: int, k1: int,
              k2: int) -> None:
    """Lemma: the new transition (position |evt_old|) is a move."""
    # Math: termination measure 1.
    # Why: no loops and no calls.
    Requires(MustTerminate(1))
    # Math: |dst_old| = |own_old| = |src1_old| = |src2_old| = |evt_old| ∧ |p2| = |p1|
    # Why: the new entries are at the same position in all five lists; p2[i], p2[j] readable.
    Requires(len(Ds0) == len(Ev0) and len(Ow0) == len(Ev0) and len(S10) == len(Ev0)
             and len(S20) == len(Ev0) and len(P2) == len(P1))
    # Math: evt = evt_old · [e] ∧ dst = dst_old · [j] ∧ own = own_old · [i]
    #       ∧ src1 = src1_old · [k1] ∧ src2 = src2_old · [k2]
    # Why: the update: one entry added to each of the five lists.
    Requires(appended(Ev0, Ev, e) and appended(Ds0, Ds, j) and appended(Ow0, Ow, i)
             and appended(S10, S1, k1) and appended(S20, S2, k2))
    # Math: i, j ∈ [0,|p1|) ∧ e ∈ [0,|mode|)
    # Why: the new transition's states and event are in range.
    Requires(0 <= i and i < len(P1) and 0 <= j and j < len(P1) and 0 <= e and e < len(md))
    # Math: move(mode[e], φ(i), e, φ(j), k1, k2)
    # Why: the new transition is a move.
    Requires(move(st1, ev1, ds1, st2, ev2, ds2, mp2, md[e], P1[i], P2[i], e, P1[j], P2[j],
                  k1, k2))
    # Math: transition |evt_old| of the new lists is a move
    # Why: the new part of the invariant after.
    Ensures(Forall(int, lambda k: (Implies(
                len(Ev0) <= k and k < len(Ev0) + 1,
                0 <= Ow[k] and Ow[k] < len(P1) and 0 <= Ds[k] and Ds[k] < len(P1)
                and 0 <= Ev[k] and Ev[k] < len(md) and 0 <= md[Ev[k]] and md[Ev[k]] <= 2
                # G1 side: moves by src1[k] (modes 0, 1), or stays (mode 2)
                and Implies(md[Ev[k]] <= 1,
                            0 <= P1[Ow[k]] and P1[Ow[k]] + 1 < len(st1)
                            and st1[P1[Ow[k]]] <= S1[k] and S1[k] < st1[P1[Ow[k]] + 1]
                            and 0 <= S1[k] and S1[k] < len(ds1) and S1[k] < len(ev1)
                            and ev1[S1[k]] == Ev[k] and ds1[S1[k]] == P1[Ds[k]])
                and Implies(md[Ev[k]] == 2, S1[k] == -1 and P1[Ds[k]] == P1[Ow[k]])
                # G2 side: moves by src2[k] (modes 0, 2), or stays (mode 1)
                and Implies(md[Ev[k]] != 1,
                            0 <= P2[Ow[k]] and P2[Ow[k]] + 1 < len(st2)
                            and st2[P2[Ow[k]]] <= S2[k] and S2[k] < st2[P2[Ow[k]] + 1]
                            and 0 <= S2[k] and S2[k] < len(ds2) and S2[k] < len(ev2)
                            and 0 <= ev2[S2[k]] and ev2[S2[k]] < len(mp2)
                            and mp2[ev2[S2[k]]] == Ev[k] and ds2[S2[k]] == P2[Ds[k]])
                and Implies(md[Ev[k]] == 1, S2[k] == -1 and P2[Ds[k]] == P2[Ow[k]])),
                [[Ow[k]]])))
    # Math: own[|evt_old|] = i ∧ evt[|evt_old|] = e ∧ dst[|evt_old|] = j
    #       ∧ src1[|evt_old|] = k1 ∧ src2[|evt_old|] = k2
    # Why (hint): the new entry, read at its position.
    Assert(Ow[len(Ev0)] == i and Ev[len(Ev0)] == e and Ds[len(Ev0)] == j
           and S1[len(Ev0)] == k1 and S2[len(Ev0)] == k2)


def keep_sound_trans(st1: PSeq[int], ev1: PSeq[int], ds1: PSeq[int],
                     st2: PSeq[int], ev2: PSeq[int], ds2: PSeq[int], mp2: PSeq[int],
                     md: PSeq[int], P1: PSeq[int], P2: PSeq[int],
                     Ev0: PSeq[int], Ds0: PSeq[int], Ow0: PSeq[int], S10: PSeq[int],
                     S20: PSeq[int], Ev: PSeq[int], Ds: PSeq[int], Ow: PSeq[int],
                     S1: PSeq[int], S2: PSeq[int], i: int, e: int, j: int, k1: int,
                     k2: int) -> None:
    """Lemma: the old transitions are unchanged, and the new one (i --e--> j) is a move."""
    # Math: termination measure 2.
    # Why: calls sound_old and sound_new (measure 1).
    Requires(MustTerminate(2))
    # Math: sound_all(evt_old, dst_old, own_old, src1_old, src2_old)
    # Why: the invariant before.
    Requires(sizes_ok(P1, P2, Ev0, Ds0, Ow0, S10, S20)
             and sound_ok(st1, ev1, ds1, st2, ev2, ds2, mp2, md, P1, P2, Ev0, Ds0, Ow0, S10, S20))
    # Math: evt = evt_old · [e] ∧ dst = dst_old · [j] ∧ own = own_old · [i]
    #       ∧ src1 = src1_old · [k1] ∧ src2 = src2_old · [k2]
    # Why: the update: one entry added to each of the five lists.
    Requires(appended(Ev0, Ev, e) and appended(Ds0, Ds, j) and appended(Ow0, Ow, i)
             and appended(S10, S1, k1) and appended(S20, S2, k2))
    # Math: i, j ∈ [0,|p1|) ∧ e ∈ [0,|mode|)
    # Why: the new transition's states and event are in range.
    Requires(0 <= i and i < len(P1) and 0 <= j and j < len(P1) and 0 <= e and e < len(md))
    # Math: move(mode[e], φ(i), e, φ(j), k1, k2)
    # Why: the new transition is a move.
    Requires(move(st1, ev1, ds1, st2, ev2, ds2, mp2, md[e], P1[i], P2[i], e, P1[j], P2[j],
                  k1, k2))
    # Math: sound_all(evt, dst, own, src1, src2)
    # Why: the invariant after.
    Ensures(sizes_ok(P1, P2, Ev, Ds, Ow, S1, S2)
            and sound_ok(st1, ev1, ds1, st2, ev2, ds2, mp2, md, P1, P2, Ev, Ds, Ow, S1, S2))
    # Math: the old positions are moves
    # Why: the old part.
    sound_old(st1, ev1, ds1, st2, ev2, ds2, mp2, md, P1, P2, Ev0, Ds0, Ow0, S10, S20,
              Ev, Ds, Ow, S1, S2, i, e, j, k1, k2)
    # Math: the new position is a move
    # Why: the new part.
    sound_new(st1, ev1, ds1, st2, ev2, ds2, mp2, md, P1, P2, Ev0, Ds0, Ow0, S10, S20,
              Ev, Ds, Ow, S1, S2, i, e, j, k1, k2)
    # Math: sound_ok(after), from its body
    # Why (hint): closes the opaque definition (its body was just proved).
    Assert(Reveal(sound_ok(st1, ev1, ds1, st2, ev2, ds2, mp2, md, P1, P2, Ev, Ds, Ow, S1, S2)))


# keep_labels: labels_ok survives a new pair of states.
# Used in: find_or_add.
def keep_labels(n1: int, n2: int, P10: PSeq[int], P20: PSeq[int], P1: PSeq[int],
                P2: PSeq[int], y1: int, y2: int) -> None:
    """Lemma: appending a pair of input states keeps every label a pair of states."""
    # Math: termination measure 1.
    # Why: no loops and no calls.
    Requires(MustTerminate(1))
    # Math: labels_ok(p1_old, p2_old) ∧ p1 = p1_old · [y1] ∧ p2 = p2_old · [y2]
    # Why: the invariant before, and the update.
    Requires(labels_ok(n1, n2, P10, P20) and appended(P10, P1, y1) and appended(P20, P2, y2))
    # Math: y1 ∈ [0,n1) ∧ y2 ∈ [0,n2)
    # Why: the new pair is a pair of states.
    Requires(0 <= y1 and y1 < n1 and 0 <= y2 and y2 < n2)
    # Math: labels_ok(p1, p2)
    # Why: the invariant after.
    Ensures(labels_ok(n1, n2, P1, P2))
    # Math: ∀ i ∈ [0,|p1|): p1[i] ∈ [0,n1) ∧ p2[i] ∈ [0,n2)
    # Why (hint): old entries from before; the new one is (y1, y2). Trigger p1[i].
    Assert(Forall(int, lambda i: (Implies(0 <= i and i < len(P1),
                                          0 <= P1[i] and P1[i] < n1
                                          and 0 <= P2[i] and P2[i] < n2), [[P1[i]]])))


# keep_own: own_ok survives a new transition of the current state h.
# Used in: emit.
def keep_own(St: PSeq[int], Ow0: PSeq[int], Ow: PSeq[int], h: int) -> None:
    """Lemma: a new transition of state h lies in h's (open) block."""
    # Math: termination measure 1.
    # Why: no loops and no calls.
    Requires(MustTerminate(1))
    # Math: own_ok(start, own_old, h) ∧ own = own_old · [h]
    # Why: the invariant before, and the update.
    Requires(own_ok(St, Ow0, h) and appended(Ow0, Ow, h))
    # Math: own_ok(start, own, h)
    # Why: the invariant after.
    Ensures(own_ok(St, Ow, h))
    # Math: ∀ k ∈ [0,|own|): the body of own_ok at k
    # Why (hint): old k: unchanged; new k = |own_old|: own[k] = h and start[h] ≤ |own_old| = k.
    #      Trigger own[k].
    Assert(Forall(int, lambda k: (Implies(
        0 <= k and k < len(Ow),
        0 <= Ow[k] and Ow[k] <= h and St[Ow[k]] <= k
        and Implies(Ow[k] < h, k < St[Ow[k] + 1])), [[Ow[k]]])))


# keep_sorted: sorted_flat and cur_ok survive a new transition of state h with event e ≥ last.
# Used in: emit.
def keep_sorted(Ow0: PSeq[int], Ev0: PSeq[int], Ow: PSeq[int], Ev: PSeq[int], h: int, e: int,
                last: int, dt: bool, dt2: bool) -> None:
    """Lemma: appending event e ≥ last to state h keeps the blocks sorted (strictly, if dt2)."""
    # Math: termination measure 1.
    # Why: no loops and no calls.
    Requires(MustTerminate(1))
    # Math: sorted_flat(own_old, evt_old, dt) ∧ cur_ok(own_old, evt_old, h, last)
    # Why: the invariants before.
    Requires(sorted_flat(Ow0, Ev0, dt) and cur_ok(Ow0, Ev0, h, last))
    # Math: own = own_old · [h] ∧ evt = evt_old · [e]
    # Why: the update.
    Requires(appended(Ow0, Ow, h) and appended(Ev0, Ev, e))
    # Math: last ≤ e ∧ (dt2 → dt ∧ last < e)
    # Why: e comes in order; the flag stays true only if e is strictly larger.
    Requires(last <= e and Implies(dt2, dt and last < e))
    # Math: sorted_flat(own, evt, dt2) ∧ cur_ok(own, evt, h, e)
    # Why: the invariants after.
    Ensures(sorted_flat(Ow, Ev, dt2) and cur_ok(Ow, Ev, h, e))
    # Math: ∀ j ∈ [0,|evt_old|): own[j] = own_old[j] ∧ evt[j] = evt_old[j]
    # Why (hint): the old entries, for both lists at once. Trigger evt[j].
    Assert(Forall(int, lambda j: (Implies(0 <= j and j < len(Ev0),
                                          Ow[j] == Ow0[j] and Ev[j] == Ev0[j]), [[Ev[j]]])))
    # Math: ∀ j ∈ [0,|evt|): own[j] = h → evt[j] ≤ e
    # Why (hint): old j of h: ≤ last ≤ e; the new one is e. Trigger evt[j].
    Assert(Forall(int, lambda j: (Implies(0 <= j and j < len(Ev) and Ow[j] == h,
                                          Ev[j] <= e), [[Ev[j]]])))
    # Math: ∀ j < i < |evt|, own[j] = own[i]: evt[j] < evt[i] ∨ (¬dt2 ∧ evt[j] = evt[i])
    # Why (hint): old pairs from before (dt2 → dt); pairs with the new i: evt[j] ≤ last ≤ e,
    #      and last < e if dt2. Trigger evt[j], evt[i].
    Assert(Forall2(int, int, lambda j, i: (Implies(
        0 <= j and j < i and i < len(Ev) and Ow[j] == Ow[i],
        Ev[j] < Ev[i] or (not dt2 and Ev[j] == Ev[i])), [[Ev[j], Ev[i]]])))


# --- the writing methods ---------------------------------------------------------------------
# Both take and give back walk_ok (for the current state h, with the last event `last` and the
# flag dt) and open it inside (Reveal); callers never look inside.


# find_or_add: the output state with the pair (y1, y2): found through the dict, or new.
# Called from: the walks, for the target of each move.
# The dict pos maps the key y1·n2 + y2 to a state; its contents are not specified (no
# invariant): a found state is checked (p1[j] = y1, p2[j] = y2), and a missing or wrong entry
# only adds a new state. A duplicate state is still a correct state (spec §3); with a working
# dict it never happens (tests check it). cap bounds the number of states (termination).
def find_or_add(n1: int, n2: int, cap: int,
                st1: PSeq[int], ev1: PSeq[int], ds1: PSeq[int],
                st2: PSeq[int], ev2: PSeq[int], ds2: PSeq[int], mp2: PSeq[int], md: PSeq[int],
                St: PSeq[int], pos: Dict[int, int], p1: List[int], p2: List[int],
                evt: List[int], dst: List[int], own: List[int], src1: List[int],
                src2: List[int], h: int, last: int, dt: bool, y1: int, y2: int) -> int:
    """The output state with pair (y1, y2), adding it if the dict does not give it; -1 if a
    new state is needed but there are cap states already (never, with a working dict)."""
    # Why: write access to the dict and the labels; read access to the transition lists (1/4:
    #      the caller keeps a share, so they are known unchanged after the call).
    Requires(Acc(dict_pred(pos)) and Acc(list_pred(p1)) and Acc(list_pred(p2)))
    Requires(Acc(list_pred(evt), 1 / 4) and Acc(list_pred(dst), 1 / 4)
             and Acc(list_pred(own), 1 / 4) and Acc(list_pred(src1), 1 / 4)
             and Acc(list_pred(src2), 1 / 4))
    # Math: termination measure 3.
    # Why: calls the lemmas (measure 1) and append.
    Requires(MustTerminate(3))
    # Math: y1 ∈ [0,n1) ∧ y2 ∈ [0,n2) ∧ |p1| ≤ cap
    # Why: the pair is a pair of states; the bound on the states so far.
    Requires(0 <= y1 and y1 < n1 and 0 <= y2 and y2 < n2 and len(p1) <= cap)
    # Math: walk_ok(h, last, dt)
    # Why: the invariant before.
    Requires(walk_ok(n1, n2, st1, ev1, ds1, st2, ev2, ds2, mp2, md, St, ToSeq(p1), ToSeq(p2),
                     ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1), ToSeq(src2), h, last, dt))
    # Why: gives the permissions back.
    Ensures(Acc(dict_pred(pos)) and Acc(list_pred(p1)) and Acc(list_pred(p2)))
    Ensures(Acc(list_pred(evt), 1 / 4) and Acc(list_pred(dst), 1 / 4)
            and Acc(list_pred(own), 1 / 4) and Acc(list_pred(src1), 1 / 4)
            and Acc(list_pred(src2), 1 / 4))
    # Math: p1_old ⊑ p1 ∧ p2_old ⊑ p2 ∧ |p1| ≤ cap ∧ |p2| = |p1|
    # Why: the old states keep their pairs (at most one state was added).
    Ensures(ext(Old(ToSeq(p1)), ToSeq(p1)) and ext(Old(ToSeq(p2)), ToSeq(p2))
            and len(p1) <= cap and len(ToSeq(p2)) == len(ToSeq(p1)))
    # Math: walk_ok(h, last, dt)
    # Why: the invariant after.
    Ensures(walk_ok(n1, n2, st1, ev1, ds1, st2, ev2, ds2, mp2, md, St, ToSeq(p1), ToSeq(p2),
                    ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1), ToSeq(src2), h, last, dt))
    # Math: r ≥ -1 ∧ (r ≥ 0 → r ∈ [0,|p1|) ∧ p1[r] = y1 ∧ p2[r] = y2)
    # Why: the answer, a state with the pair (y1, y2); -1 is the only failure code.
    Ensures(Result() >= -1)
    Ensures(Implies(Result() >= 0, Result() < len(ToSeq(p1)) and ToSeq(p1)[Result()] == y1
                    and ToSeq(p2)[Result()] == y2))
    # Math: walk_ok(before) ⟹ its parts
    # Why (hint): opens the invariant (labels_ok, sizes_ok, sound_ok, ...).
    Assert(Reveal(walk_ok(n1, n2, st1, ev1, ds1, st2, ev2, ds2, mp2, md, St, ToSeq(p1),
                          ToSeq(p2), ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1),
                          ToSeq(src2), h, last, dt)))
    key = y1 * n2 + y2               # the dict key of the pair
    if key in pos:
        j = pos[key]                 # the state the dict gives ...
        if 0 <= j and j < len(p1) and p1[j] == y1 and p2[j] == y2:
            # ... checked: it has the pair (y1, y2)
            # Math: p1 ⊑ p1 ∧ p2 ⊑ p2
            # Why (hint): nothing changed (ext of a list with itself, stated with its trigger).
            Assert(ext(ToSeq(p1), ToSeq(p1)) and ext(ToSeq(p2), ToSeq(p2)))
            return j
    if len(p1) >= cap:
        # Math: p1 ⊑ p1 ∧ p2 ⊑ p2
        # Why (hint): nothing changed.
        Assert(ext(ToSeq(p1), ToSeq(p1)) and ext(ToSeq(p2), ToSeq(p2)))
        return -1                    # no room: cannot happen with a working dict
    i = len(p1)                      # the new state's number
    p1.append(y1)                    # its G1 state ...
    p2.append(y2)                    # ... and G2 state
    pos[key] = i                     # remember it
    # Math: p1 = p1_old · [y1] ∧ p2 = p2_old · [y2]
    # Why (hint): the two appends, as one fact each (the lemmas use them).
    Assert(appended(Old(ToSeq(p1)), ToSeq(p1), y1) and appended(Old(ToSeq(p2)), ToSeq(p2), y2))
    # Math: p1_old ⊑ p1 ∧ p2_old ⊑ p2
    # Why: the postcondition "the lists only grew".
    ext_app(Old(ToSeq(p1)), ToSeq(p1), y1)
    ext_app(Old(ToSeq(p2)), ToSeq(p2), y2)
    # Math: labels_ok(p1, p2)
    # Why: the new label is a pair of states.
    keep_labels(n1, n2, Old(ToSeq(p1)), Old(ToSeq(p2)), ToSeq(p1), ToSeq(p2), y1, y2)
    # Math: sound_ok with the new p1, p2
    # Why: the old transitions are still moves.
    keep_sound_state(st1, ev1, ds1, st2, ev2, ds2, mp2, md, Old(ToSeq(p1)), Old(ToSeq(p2)),
                     ToSeq(p1), ToSeq(p2), ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1),
                     ToSeq(src2), y1, y2)
    # Math: walk_ok(after), from its parts
    # Why (hint): closes the invariant (own_ok, sorted_flat, cur_ok do not read p1, p2).
    Assert(Reveal(walk_ok(n1, n2, st1, ev1, ds1, st2, ev2, ds2, mp2, md, St, ToSeq(p1),
                          ToSeq(p2), ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1),
                          ToSeq(src2), h, last, dt)))
    return i


# emit: a new output transition h --e--> j of the current state h that is a move.
# Called from: the walks, for each move of the state being processed.
def emit(n1: int, n2: int, st1: PSeq[int], ev1: PSeq[int], ds1: PSeq[int],
         st2: PSeq[int], ev2: PSeq[int], ds2: PSeq[int], mp2: PSeq[int], md: PSeq[int],
         St: PSeq[int], p1: List[int], p2: List[int], evt: List[int], dst: List[int],
         own: List[int], src1: List[int], src2: List[int], h: int, e: int, j: int, k1: int,
         k2: int, last: int, dt: bool, dt2: bool) -> None:
    """Append the transition h --e--> j (input transitions k1, k2) to the output."""
    # Why: read access to the labels (1/4: the caller keeps a share); write access to the
    #      transition lists.
    Requires(Acc(list_pred(p1), 1 / 4) and Acc(list_pred(p2), 1 / 4))
    Requires(Acc(list_pred(evt)) and Acc(list_pred(dst)) and Acc(list_pred(own))
             and Acc(list_pred(src1)) and Acc(list_pred(src2)))
    # Math: termination measure 3.
    # Why: calls keep_sound_trans (measure 2), the other lemmas (1) and append.
    Requires(MustTerminate(3))
    # Math: walk_ok(h, last, dt)
    # Why: the invariant before.
    Requires(walk_ok(n1, n2, st1, ev1, ds1, st2, ev2, ds2, mp2, md, St, ToSeq(p1), ToSeq(p2),
                     ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1), ToSeq(src2), h, last, dt))
    # Math: |p2| = |p1| ∧ h, j ∈ [0,|p1|) ∧ e ∈ [0,|mode|)
    # Why: the new transition's states and event are in range.
    Requires(len(ToSeq(p2)) == len(ToSeq(p1)) and 0 <= h and h < len(ToSeq(p1)) and 0 <= j
             and j < len(ToSeq(p1)) and 0 <= e and e < len(md))
    # Math: move(mode[e], φ(h), e, φ(j), k1, k2)
    # Why: the new transition is a move (the walk establishes it from the input transitions).
    Requires(move(st1, ev1, ds1, st2, ev2, ds2, mp2, md[e], ToSeq(p1)[h], ToSeq(p2)[h], e,
                  ToSeq(p1)[j], ToSeq(p2)[j], k1, k2))
    # Math: last ≤ e ∧ (dt2 → dt ∧ last < e)
    # Why: the moves of a state come in event order; dt2 is the flag after this one.
    Requires(last <= e and Implies(dt2, dt and last < e))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(p1), 1 / 4) and Acc(list_pred(p2), 1 / 4))
    Ensures(Acc(list_pred(evt)) and Acc(list_pred(dst)) and Acc(list_pred(own))
            and Acc(list_pred(src1)) and Acc(list_pred(src2)))
    # Math: own = own_old · [h] ∧ src1 = src1_old · [k1] ∧ src2 = src2_old · [k2]
    #       ∧ evt = evt_old · [e] ∧ dst = dst_old · [j]
    # Why: the caller learns the new entry and that the old ones are kept (for its snapshots).
    Ensures(appended(Old(ToSeq(own)), ToSeq(own), h)
            and appended(Old(ToSeq(src1)), ToSeq(src1), k1)
            and appended(Old(ToSeq(src2)), ToSeq(src2), k2)
            and appended(Old(ToSeq(evt)), ToSeq(evt), e)
            and appended(Old(ToSeq(dst)), ToSeq(dst), j))
    # Math: walk_ok(h, e, dt2)
    # Why: the invariant after; e is now the last event of h.
    Ensures(walk_ok(n1, n2, st1, ev1, ds1, st2, ev2, ds2, mp2, md, St, ToSeq(p1), ToSeq(p2),
                    ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1), ToSeq(src2), h, e, dt2))
    # Math: walk_ok(before) ⟹ its parts
    # Why (hint): opens the invariant.
    Assert(Reveal(walk_ok(n1, n2, st1, ev1, ds1, st2, ev2, ds2, mp2, md, St, ToSeq(p1),
                          ToSeq(p2), ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1),
                          ToSeq(src2), h, last, dt)))
    evt.append(e)                    # the event ...
    dst.append(j)                    # ... the target state ...
    own.append(h)                    # ... the source state ...
    src1.append(k1)                  # ... and the input transitions used (-1: that side stays)
    src2.append(k2)
    # Math: each list is its old value with one entry appended
    # Why (hint): the five appends, as one fact each (the lemmas use them).
    Assert(appended(Old(ToSeq(evt)), ToSeq(evt), e) and appended(Old(ToSeq(dst)), ToSeq(dst), j)
           and appended(Old(ToSeq(own)), ToSeq(own), h)
           and appended(Old(ToSeq(src1)), ToSeq(src1), k1)
           and appended(Old(ToSeq(src2)), ToSeq(src2), k2))
    # Math: sound_ok with the new transition lists
    # Why: the old transitions are unchanged, and the new one is a move.
    keep_sound_trans(st1, ev1, ds1, st2, ev2, ds2, mp2, md, ToSeq(p1), ToSeq(p2),
                     Old(ToSeq(evt)), Old(ToSeq(dst)), Old(ToSeq(own)), Old(ToSeq(src1)),
                     Old(ToSeq(src2)), ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1),
                     ToSeq(src2), h, e, j, k1, k2)
    # Math: own_ok(start, own, h)
    # Why: the new transition is in h's block.
    keep_own(St, Old(ToSeq(own)), ToSeq(own), h)
    # Math: sorted_flat(dt2) ∧ cur_ok(h, e)
    # Why: e comes after the earlier events of h.
    keep_sorted(Old(ToSeq(own)), Old(ToSeq(evt)), ToSeq(own), ToSeq(evt), h, e, last, dt, dt2)
    # Math: walk_ok(h, e, dt2), from its parts
    # Why (hint): closes the invariant.
    Assert(Reveal(walk_ok(n1, n2, st1, ev1, ds1, st2, ev2, ds2, mp2, md, St, ToSeq(p1),
                          ToSeq(p2), ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1),
                          ToSeq(src2), h, e, dt2)))


# --- one run of `both` moves ------------------------------------------------------------------
# Inside these methods the input target lists are read at runtime (dst1, dst2), so the contracts
# use ToSeq(dst1), ToSeq(dst2) for G1's and G2's targets (a separate PSeq parameter "equal" to
# ToSeq(dst1) carries no facts: PSeq equality needs the element types known equal).


# both_step: one move (k1, k2) of a run: the target state (found or added) and the transition.
# Called from: both_run, once per k2. A separate method so that each proof is small.
def both_step(n1: int, n2: int, cap: int,
              st1: PSeq[int], ev1: PSeq[int],
              st2: PSeq[int], ev2: PSeq[int], mp2: PSeq[int], md: PSeq[int],
              St: PSeq[int], dst1: List[int], dst2: List[int], pos: Dict[int, int],
              p1: List[int], p2: List[int], evt: List[int], dst: List[int], own: List[int],
              src1: List[int], src2: List[int], h: int, a: int, b: int, k1: int, e: int,
              k2: int, y1: int, last: int, dt: bool, dt2: bool) -> int:
    """Emit h --e--> (y1, dst2[k2]) with y1 = dst1[k1]; 0, or -1 if find_or_add failed."""
    # Why: read access to the input target lists.
    Requires(Acc(list_pred(dst1), 1 / 8) and Acc(list_pred(dst2), 1 / 8))
    # Math: md[e] = 0 ∧ a --e-->_k1 y1 ∧ y1 ∈ [0,n1)
    # Why: k1 is a transition of a on the shared event e, with target y1.
    Requires(0 <= e and e < len(md) and md[e] == 0
             and 0 <= a and a + 1 < len(st1) and st1[a] <= k1 and k1 < st1[a + 1]
             and 0 <= k1 and k1 < len(ToSeq(dst1)) and k1 < len(ev1) and ev1[k1] == e
             and ToSeq(dst1)[k1] == y1 and 0 <= y1 and y1 < n1)
    # Math: b --e-->_k2 dst2[k2] (output numbers) ∧ dst2[k2] ∈ [0,n2)
    # Why: k2 is a transition of b on e.
    Requires(0 <= b and b + 1 < len(st2) and st2[b] <= k2 and k2 < st2[b + 1]
             and 0 <= k2 and k2 < len(ToSeq(dst2)) and k2 < len(dst2) and k2 < len(ev2)
             and 0 <= ev2[k2] and ev2[k2] < len(mp2) and mp2[ev2[k2]] == e
             and 0 <= ToSeq(dst2)[k2] and ToSeq(dst2)[k2] < n2)
    # Why: write access to the dict, the labels and the transition lists.
    Requires(Acc(dict_pred(pos)) and Acc(list_pred(p1)) and Acc(list_pred(p2)))
    Requires(Acc(list_pred(evt)) and Acc(list_pred(dst)) and Acc(list_pred(own))
             and Acc(list_pred(src1)) and Acc(list_pred(src2)))
    # Math: termination measure 4.
    # Why: calls find_or_add (3) and emit (3).
    Requires(MustTerminate(4))
    # Math: h ∈ [0,|p1|) ∧ φ(h) = (a, b) ∧ |p2| = |p1| ≤ cap
    # Why: h is the current state, with the pair (a, b).
    Requires(len(ToSeq(p2)) == len(ToSeq(p1)) and 0 <= h and h < len(ToSeq(p1))
             and ToSeq(p1)[h] == a and ToSeq(p2)[h] == b and len(p1) <= cap)
    # Math: walk_ok(h, last, dt) ∧ last ≤ e ∧ (dt2 → dt ∧ last < e)
    # Why: the invariant before, and the order of events.
    Requires(walk_ok(n1, n2, st1, ev1, ToSeq(dst1), st2, ev2, ToSeq(dst2), mp2, md, St,
                     ToSeq(p1), ToSeq(p2), ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1),
                     ToSeq(src2), h, last, dt))
    Requires(last <= e and Implies(dt2, dt and last < e))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(dst1), 1 / 8) and Acc(list_pred(dst2), 1 / 8))
    Ensures(Acc(dict_pred(pos)) and Acc(list_pred(p1)) and Acc(list_pred(p2)))
    Ensures(Acc(list_pred(evt)) and Acc(list_pred(dst)) and Acc(list_pred(own))
            and Acc(list_pred(src1)) and Acc(list_pred(src2)))
    # Math: r ∈ {-1, 0}
    # Why: 0 done, -1 no room.
    Ensures(Result() == 0 or Result() == -1)
    # Math: p1_old ⊑ p1 ∧ p2_old ⊑ p2 ∧ |p2| = |p1| ≤ cap ∧ φ(h) = (a, b)
    # Why: only appends to the labels; the current state keeps its pair.
    Ensures(ext(Old(ToSeq(p1)), ToSeq(p1)) and ext(Old(ToSeq(p2)), ToSeq(p2)) and len(p1) <= cap
            and len(ToSeq(p2)) == len(ToSeq(p1)) and h < len(ToSeq(p1))
            and ToSeq(p1)[h] == a and ToSeq(p2)[h] == b)
    # Math: r = 0 → own = own_old · [h] ∧ src1 = src1_old · [k1] ∧ src2 = src2_old · [k2]
    #       ∧ evt = evt_old · [e] ∧ walk_ok(h, e, dt2)
    # Why: the new transition (the caller's run fact), and the invariant after.
    Ensures(Implies(Result() == 0, appended(Old(ToSeq(own)), ToSeq(own), h)
                    and appended(Old(ToSeq(src1)), ToSeq(src1), k1)
                    and appended(Old(ToSeq(src2)), ToSeq(src2), k2)
                    and appended(Old(ToSeq(evt)), ToSeq(evt), e)
                    and walk_ok(n1, n2, st1, ev1, ToSeq(dst1), st2, ev2, ToSeq(dst2), mp2, md,
                                St, ToSeq(p1), ToSeq(p2), ToSeq(evt), ToSeq(dst), ToSeq(own),
                                ToSeq(src1), ToSeq(src2), h, e, dt2)))
    # Math: r ≠ 0 → own_old ⊑ own ∧ src1_old ⊑ src1 ∧ src2_old ⊑ src2
    # Why: on failure nothing was emitted (the caller's snapshots stay prefixes).
    Ensures(Implies(Result() != 0, ext(Old(ToSeq(own)), ToSeq(own))
                    and ext(Old(ToSeq(src1)), ToSeq(src1))
                    and ext(Old(ToSeq(src2)), ToSeq(src2))))
    y2 = dst2[k2]                    # the G2 target
    j = find_or_add(n1, n2, cap, st1, ev1, ToSeq(dst1), st2, ev2, ToSeq(dst2), mp2, md, St,
                    pos, p1, p2, evt, dst, own, src1, src2, h, last, dt, y1, y2)  # the target
    if j < 0:
        # Math: own ⊑ own ∧ src1 ⊑ src1 ∧ src2 ⊑ src2
        # Why (hint): nothing emitted (ext of a list with itself).
        Assert(ext(ToSeq(own), ToSeq(own)) and ext(ToSeq(src1), ToSeq(src1))
               and ext(ToSeq(src2), ToSeq(src2)))
        return -1                    # no room (never with a working dict)
    # Math: φ(h) = (a, b)
    # Why (hint): h < |p1_old|, so its pair is unchanged (ext at h).
    Assert(ToSeq(p1)[h] == Old(ToSeq(p1))[h] and ToSeq(p2)[h] == Old(ToSeq(p2))[h])
    emit(n1, n2, st1, ev1, ToSeq(dst1), st2, ev2, ToSeq(dst2), mp2, md, St, p1, p2, evt, dst,
         own, src1, src2, h, e, j, k1, k2, last, dt, dt2)   # the transition
    return 0


# both_run: the moves of the current state h on a shared event e that use the G1 transition k1,
# from the G2 transition k2 on: one per G2 transition in [k2, hi) (the G2 transitions of p2[h]
# on e lie in [lo, hi), found by binary search; the caller starts at k2 = lo).
# Called from: walk_left (k2 = lo), and itself (k2 + 1).
# Recursive rather than a loop: inside a loop with these invariants, simple facts (a list read
# in range) did not verify, while a method with the same facts as its contract does
# (2026-10-30). The depth is hi - lo, the number of G2 transitions of one state on one event.
# The run is written at the positions d + k (one after another): the completeness witness for
# (h, k1) is d.
def both_run(n1: int, n2: int, cap: int,
             st1: PSeq[int], ev1: PSeq[int],
             st2: PSeq[int], ev2: PSeq[int], mp2: PSeq[int], md: PSeq[int],
             St: PSeq[int], dst1: List[int], dst2: List[int], pos: Dict[int, int],
             p1: List[int], p2: List[int], evt: List[int], dst: List[int], own: List[int],
             src1: List[int], src2: List[int], h: int, a: int, b: int, k1: int, e: int,
             y1: int, lo: int, k2: int, hi: int, d: int, last: int, dt: bool) -> int:
    """Emit h --e--> (y1, dst2[k]) for every k in [k2, hi). Returns the flag after the run
    (1 true, 0 false), or -1 if find_or_add failed."""
    # Why: read access to the input target lists (1/4: both_step gets 1/8, so this call keeps
    #      a share and still knows the lists afterwards).
    Requires(Acc(list_pred(dst1), 1 / 4) and Acc(list_pred(dst2), 1 / 4))
    # Math: md[e] = 0 ∧ a --e-->_k1 y1 ∧ y1 ∈ [0,n1)
    # Why: k1 is a transition of a on the shared event e, with target y1.
    Requires(0 <= e and e < len(md) and md[e] == 0
             and 0 <= a and a + 1 < len(st1) and st1[a] <= k1 and k1 < st1[a + 1]
             and 0 <= k1 and k1 < len(ToSeq(dst1)) and k1 < len(ev1) and ev1[k1] == e
             and ToSeq(dst1)[k1] == y1 and 0 <= y1 and y1 < n1)
    # Math: lo ≤ k2 ≤ hi ∧ [lo,hi) ⊆ [0,|evt2|) ∩ [0,|dst2|)
    # Why: so evt2[k], dst2[k] can be read (then the quantifier below gives the rest).
    Requires(0 <= b and b + 1 < len(st2) and 0 <= lo and lo <= k2 and k2 <= hi
             and hi <= len(ev2) and hi <= len(ToSeq(dst2)) and hi <= len(dst2))
    # Math: ∀ k ∈ [lo,hi): b --e-->_k dst2[k] (in output numbers) ∧ dst2[k] ∈ [0,n2)
    # Why: [lo, hi) are transitions of b on e. Trigger evt2[k], the first read (a trigger must
    #      be read unconditionally: a read after another conjunct is not matched, 2026-10-30).
    Requires(Forall(int, lambda k: (Implies(lo <= k and k < hi,
                                            0 <= ev2[k] and ev2[k] < len(mp2) and mp2[ev2[k]] == e
                                            and st2[b] <= k and k < st2[b + 1]
                                            and 0 <= ToSeq(dst2)[k] and ToSeq(dst2)[k] < n2),
                                    [[ev2[k]]])))
    # Why: write access to the dict, the labels and the transition lists.
    Requires(Acc(dict_pred(pos)) and Acc(list_pred(p1)) and Acc(list_pred(p2)))
    Requires(Acc(list_pred(evt)) and Acc(list_pred(dst)) and Acc(list_pred(own))
             and Acc(list_pred(src1)) and Acc(list_pred(src2)))
    # Math: termination measure hi - k2 + 5.
    # Why: decreases with each recursive call (k2 + 1); both_step has measure 4.
    Requires(MustTerminate(hi - k2 + 5))
    # Math: h ∈ [0,|p1|) ∧ φ(h) = (a, b) ∧ |p2| = |p1| ≤ cap
    # Why: h is the current state, with the pair (a, b).
    Requires(len(ToSeq(p2)) == len(ToSeq(p1)) and 0 <= h and h < len(ToSeq(p1))
             and ToSeq(p1)[h] == a and ToSeq(p2)[h] == b and len(p1) <= cap)
    # Math: |evt| = |own| = |src1| = |src2| = d + k2 ∧ d + lo ≥ 0
    # Why: the next move (k1, k2) goes to position d + k2.
    Requires(len(ToSeq(evt)) == d + k2 and len(ToSeq(own)) == d + k2
             and len(ToSeq(src1)) == d + k2 and len(ToSeq(src2)) == d + k2 and 0 <= d + lo)
    # Math: ∀ k ∈ [lo,k2): own[d+k] = h ∧ src1[d+k] = k1 ∧ src2[d+k] = k
    # Why: the run so far. Trigger own[d + k], the first read.
    Requires(Forall(int, lambda k: (Implies(
        lo <= k and k < k2,
        ToSeq(own)[d + k] == h and ToSeq(src1)[d + k] == k1 and ToSeq(src2)[d + k] == k),
        [[ToSeq(own)[d + k]]])))
    # Math: walk_ok(h, last, dt)
    # Why: the invariant before (last, dt: after the moves so far).
    Requires(walk_ok(n1, n2, st1, ev1, ToSeq(dst1), st2, ev2, ToSeq(dst2), mp2, md, St,
                     ToSeq(p1), ToSeq(p2), ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1),
                     ToSeq(src2), h, last, dt))
    # Math: last ≤ e
    # Why: e comes after the earlier events of h.
    Requires(last <= e)
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(dst1), 1 / 4) and Acc(list_pred(dst2), 1 / 4))
    Ensures(Acc(dict_pred(pos)) and Acc(list_pred(p1)) and Acc(list_pred(p2)))
    Ensures(Acc(list_pred(evt)) and Acc(list_pred(dst)) and Acc(list_pred(own))
            and Acc(list_pred(src1)) and Acc(list_pred(src2)))
    # Math: r ∈ {-1, 0, 1} ∧ (r = 1 → dt)
    # Why: the flag after the run (it only goes from true to false), or -1 no room (never
    #      with a working dict).
    Ensures(Result() >= -1 and Result() <= 1 and Implies(Result() == 1, dt))
    # Math: L_old ⊑ L for p1, p2, own, src1, src2 ∧ |p2| = |p1| ≤ cap ∧ φ(h) = (a, b)
    # Why: only appends (the caller's snapshots stay prefixes); the current state's pair.
    Ensures(ext(Old(ToSeq(p1)), ToSeq(p1)) and ext(Old(ToSeq(p2)), ToSeq(p2))
            and ext(Old(ToSeq(own)), ToSeq(own)) and ext(Old(ToSeq(src1)), ToSeq(src1))
            and ext(Old(ToSeq(src2)), ToSeq(src2)) and len(p1) <= cap
            and len(ToSeq(p2)) == len(ToSeq(p1)) and h < len(ToSeq(p1))
            and ToSeq(p1)[h] == a and ToSeq(p2)[h] == b)
    # Math: r ≥ 0 → walk_ok(h, e, r = 1) ∧ |evt| = |own| = |src1| = |src2| = d + hi
    # Why: the invariant after (e is the last event, also when nothing is left: last ≤ e),
    #      and the length of the run.
    Ensures(Implies(Result() >= 0, walk_ok(n1, n2, st1, ev1, ToSeq(dst1), st2, ev2,
                                           ToSeq(dst2), mp2, md, St, ToSeq(p1), ToSeq(p2),
                                           ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1),
                                           ToSeq(src2), h, e, Result() == 1)
                    and len(ToSeq(evt)) == d + hi and len(ToSeq(own)) == d + hi
                    and len(ToSeq(src1)) == d + hi and len(ToSeq(src2)) == d + hi))
    # Math: r ≥ 0 → ∀ k ∈ [lo,hi): own[d+k] = h ∧ src1[d+k] = k1 ∧ src2[d+k] = k
    # Why: the whole run: the move (k1, k) is the output transition d + k (completeness
    #      witness). Trigger own[d + k], the first read.
    Ensures(Implies(Result() >= 0, Forall(int, lambda k: (Implies(
        lo <= k and k < hi,
        ToSeq(own)[d + k] == h and ToSeq(src1)[d + k] == k1 and ToSeq(src2)[d + k] == k),
        [[ToSeq(own)[d + k]]]))))
    if k2 == hi:
        # nothing left: weaken cur_ok from last to e
        # Math: walk_ok(h, last, dt) ⟹ its parts
        # Why (hint): opens the invariant (to change the bound of cur_ok).
        Assert(Reveal(walk_ok(n1, n2, st1, ev1, ToSeq(dst1), st2, ev2, ToSeq(dst2), mp2, md, St,
                              ToSeq(p1), ToSeq(p2), ToSeq(evt), ToSeq(dst), ToSeq(own),
                              ToSeq(src1), ToSeq(src2), h, last, dt)))
        # Math: ∀ j: own[j] = h → evt[j] ≤ last ≤ e
        # Why (hint): cur_ok with the larger bound e. Trigger evt[j], as in cur_ok.
        Assert(Forall(int, lambda jj: (Implies(0 <= jj and jj < len(ToSeq(evt))
                                               and ToSeq(own)[jj] == h,
                                               ToSeq(evt)[jj] <= e), [[ToSeq(evt)[jj]]])))
        # Math: walk_ok(h, e, dt)
        # Why (hint): closes it with the new bound.
        Assert(Reveal(walk_ok(n1, n2, st1, ev1, ToSeq(dst1), st2, ev2, ToSeq(dst2), mp2, md, St,
                              ToSeq(p1), ToSeq(p2), ToSeq(evt), ToSeq(dst), ToSeq(own),
                              ToSeq(src1), ToSeq(src2), h, e, dt)))
        # Math: L ⊑ L for the five lists
        # Why (hint): nothing changed (ext of a list with itself).
        Assert(ext(ToSeq(p1), ToSeq(p1)) and ext(ToSeq(p2), ToSeq(p2))
               and ext(ToSeq(own), ToSeq(own)) and ext(ToSeq(src1), ToSeq(src1))
               and ext(ToSeq(src2), ToSeq(src2)))
        if dt:
            return 1                 # the flag is still true
        return 0
    # Math: b --e-->_k2 dst2[k2] ∧ dst2[k2] ∈ [0,n2)
    # Why (hint): the precondition's quantifier at k2 (mentioning evt2[k2] triggers it).
    Assert(0 <= ev2[k2] and ev2[k2] < len(mp2) and mp2[ev2[k2]] == e)
    f = dt and last < e              # the flag after this move
    r = both_step(n1, n2, cap, st1, ev1, st2, ev2, mp2, md, St, dst1, dst2, pos, p1, p2, evt,
                  dst, own, src1, src2, h, a, b, k1, e, k2, y1, last, dt, f)   # move (k1, k2)
    if r < 0:
        return -1                    # no room (never with a working dict)
    # Math: own_old ⊑ own ∧ src1_old ⊑ src1 ∧ src2_old ⊑ src2
    # Why (hint): the step appended one entry to each (appended ⟹ ext).
    ext_app(Old(ToSeq(own)), ToSeq(own), h)
    ext_app(Old(ToSeq(src1)), ToSeq(src1), k1)
    ext_app(Old(ToSeq(src2)), ToSeq(src2), k2)
    P10 = ToSeq(p1)                  # snapshots after the step (proof only)
    P20 = ToSeq(p2)
    O0 = ToSeq(own)
    A0 = ToSeq(src1)
    B0 = ToSeq(src2)
    # Math: ∀ k ∈ [lo,k2]: own[d+k] = h ∧ src1[d+k] = k1 ∧ src2[d+k] = k
    # Why (hint): old run entries unchanged by the append; the new one at d + k2.
    Assert(Forall(int, lambda k: (Implies(
        lo <= k and k <= k2,
        ToSeq(own)[d + k] == h and ToSeq(src1)[d + k] == k1 and ToSeq(src2)[d + k] == k),
        [[ToSeq(own)[d + k]]])))
    r = both_run(n1, n2, cap, st1, ev1, st2, ev2, mp2, md, St, dst1, dst2, pos, p1, p2, evt,
                 dst, own, src1, src2, h, a, b, k1, e, y1, lo, k2 + 1, hi, d, e,
                 f)                  # the rest of the run
    # Math: L_old ⊑ L for p1, p2, own, src1, src2
    # Why: chain the two calls' "only appends".
    ext_trans(Old(ToSeq(p1)), P10, ToSeq(p1))
    ext_trans(Old(ToSeq(p2)), P20, ToSeq(p2))
    ext_trans(Old(ToSeq(own)), O0, ToSeq(own))
    ext_trans(Old(ToSeq(src1)), A0, ToSeq(src1))
    ext_trans(Old(ToSeq(src2)), B0, ToSeq(src2))
    return r


# --- binary search in a sorted block ------------------------------------------------------
# As lower_bound / upper_bound in basic_ops.py, with the facts stated on ToSeq(evt) (the
# callers' contracts use ToSeq of the input lists).


# lbound: the first position a in [lo, hi] with evt[a] ≥ x.
# Called from: walk_left (the G2 transitions of a state on a shared event).
def lbound(evt: List[int], lo: int, hi: int, x: int) -> int:
    """Binary search in a sorted range: the first position a in lo .. hi with evt[a] >= x."""
    # Math: termination measure 2.
    # Why: one loop, no calls.
    Requires(MustTerminate(2))
    # Why: read access to evt.
    Requires(Acc(list_pred(evt), 1 / 16))
    # Math: 0 ≤ lo ≤ hi ≤ |evt|
    # Why: a valid range (the list length and its ToSeq length, both).
    Requires(0 <= lo and lo <= hi and hi <= len(evt) and hi <= len(ToSeq(evt)))
    # Math: ∀ j < i in [lo,hi): evt[j] ≤ evt[i]
    # Why: the range is sorted. Trigger: the two reads.
    Requires(Forall2(int, int, lambda j, i: (Implies(lo <= j and j < i and i < hi,
                                                     ToSeq(evt)[j] <= ToSeq(evt)[i]),
                                             [[ToSeq(evt)[j], ToSeq(evt)[i]]])))
    # Why: gives the permission back.
    Ensures(Acc(list_pred(evt), 1 / 16))
    # Math: lo ≤ a ≤ hi ≤ |evt|
    # Why: the answer is in the range (|evt| restated, so evt[k] below can be read).
    Ensures(lo <= Result() and Result() <= hi and hi <= len(ToSeq(evt)))
    # Math: ∀ k ∈ [lo,a): evt[k] < x
    # Why: everything before a is on a smaller event. Trigger evt[k].
    Ensures(Forall(int, lambda k: (Implies(lo <= k and k < Result(), ToSeq(evt)[k] < x),
                                   [[ToSeq(evt)[k]]])))
    # Math: ∀ k ∈ [a,hi): evt[k] ≥ x
    # Why: everything from a on is on x or a larger event. Trigger evt[k].
    Ensures(Forall(int, lambda k: (Implies(Result() <= k and k < hi, ToSeq(evt)[k] >= x),
                                   [[ToSeq(evt)[k]]])))
    l = lo                           # the answer is in [l, r]
    r = hi
    while l < r:
        # Math: termination measure r - l + 1, decreasing (the range halves).
        # Why: no calls in the loop.
        Invariant(MustTerminate(r - l + 1))
        # Why: read access; evt unchanged.
        Invariant(Acc(list_pred(evt), 1 / 16))
        Invariant(ToSeq(evt) == Old(ToSeq(evt)))
        # Math: lo ≤ l ≤ r ≤ hi ≤ |evt|
        # Why: the search range, inside the list.
        Invariant(lo <= l and l <= r and r <= hi and hi <= len(evt) and hi <= len(ToSeq(evt)))
        # Math: the range is sorted (the precondition, restated: the loop starts from here)
        Invariant(Forall2(int, int, lambda j, i: (Implies(lo <= j and j < i and i < hi,
                                                          ToSeq(evt)[j] <= ToSeq(evt)[i]),
                                                  [[ToSeq(evt)[j], ToSeq(evt)[i]]])))
        # Math: ∀ k ∈ [lo,l): evt[k] < x   and   ∀ k ∈ [r,hi): evt[k] ≥ x
        # Why: outside [l, r] the comparison with x is known.
        Invariant(Forall(int, lambda k: (Implies(lo <= k and k < l, ToSeq(evt)[k] < x),
                                         [[ToSeq(evt)[k]]])))
        Invariant(Forall(int, lambda k: (Implies(r <= k and k < hi, ToSeq(evt)[k] >= x),
                                         [[ToSeq(evt)[k]]])))
        mid = (l + r) // 2           # l ≤ mid < r
        if evt[mid] < x:
            # Math: ∀ k ∈ [lo,mid]: evt[k] ≤ evt[mid] < x
            # Why (hint): sorted, so everything up to mid is < x too.
            Assert(Forall(int, lambda k: (Implies(lo <= k and k <= mid,
                                                  ToSeq(evt)[k] <= ToSeq(evt)[mid]),
                                          [[ToSeq(evt)[k]]])))
            l = mid + 1
        else:
            # Math: ∀ k ∈ [mid,hi): evt[k] ≥ evt[mid] ≥ x
            # Why (hint): sorted, so everything from mid on is ≥ x too.
            Assert(Forall(int, lambda k: (Implies(mid <= k and k < hi,
                                                  ToSeq(evt)[mid] <= ToSeq(evt)[k]),
                                          [[ToSeq(evt)[k]]])))
            r = mid
    return l


# ubound: the first position b in [a, hi] with evt[b] > x.
# Called from: walk_left (after lbound).
def ubound(evt: List[int], lo: int, a: int, hi: int, x: int) -> int:
    """Binary search in a sorted range, from a: the first position b in a .. hi with
    evt[b] > x."""
    # Math: termination measure 2.
    # Why: one loop, no calls.
    Requires(MustTerminate(2))
    # Why: read access to evt.
    Requires(Acc(list_pred(evt), 1 / 16))
    # Math: 0 ≤ lo ≤ a ≤ hi ≤ |evt|
    # Why: a valid range.
    Requires(0 <= lo and lo <= a and a <= hi and hi <= len(evt) and hi <= len(ToSeq(evt)))
    # Math: ∀ j < i in [lo,hi): evt[j] ≤ evt[i]
    # Why: the range is sorted.
    Requires(Forall2(int, int, lambda j, i: (Implies(lo <= j and j < i and i < hi,
                                                     ToSeq(evt)[j] <= ToSeq(evt)[i]),
                                             [[ToSeq(evt)[j], ToSeq(evt)[i]]])))
    # Why: gives the permission back.
    Ensures(Acc(list_pred(evt), 1 / 16))
    # Math: a ≤ b ≤ hi ≤ |evt|
    # Why: the answer is in the range (|evt| restated, so evt[k] below can be read).
    Ensures(a <= Result() and Result() <= hi and hi <= len(ToSeq(evt)))
    # Math: ∀ k ∈ [a,b): evt[k] ≤ x
    # Why: up to b, events are ≤ x. Trigger evt[k].
    Ensures(Forall(int, lambda k: (Implies(a <= k and k < Result(), ToSeq(evt)[k] <= x),
                                   [[ToSeq(evt)[k]]])))
    # Math: ∀ k ∈ [b,hi): evt[k] > x
    # Why: from b on, events are larger. Trigger evt[k].
    Ensures(Forall(int, lambda k: (Implies(Result() <= k and k < hi, ToSeq(evt)[k] > x),
                                   [[ToSeq(evt)[k]]])))
    l = a                            # the answer is in [l, r]
    r = hi
    while l < r:
        # Math: termination measure r - l + 1, decreasing.
        # Why: no calls in the loop.
        Invariant(MustTerminate(r - l + 1))
        # Why: read access; evt unchanged.
        Invariant(Acc(list_pred(evt), 1 / 16))
        Invariant(ToSeq(evt) == Old(ToSeq(evt)))
        # Math: lo ≤ a ≤ l ≤ r ≤ hi ≤ |evt|
        # Why: the search range, inside the list.
        Invariant(lo <= a and a <= l and l <= r and r <= hi and hi <= len(evt)
                  and hi <= len(ToSeq(evt)))
        # Math: the range is sorted (restated)
        Invariant(Forall2(int, int, lambda j, i: (Implies(lo <= j and j < i and i < hi,
                                                          ToSeq(evt)[j] <= ToSeq(evt)[i]),
                                                  [[ToSeq(evt)[j], ToSeq(evt)[i]]])))
        # Math: ∀ k ∈ [a,l): evt[k] ≤ x   and   ∀ k ∈ [r,hi): evt[k] > x
        # Why: outside [l, r] the comparison with x is known.
        Invariant(Forall(int, lambda k: (Implies(a <= k and k < l, ToSeq(evt)[k] <= x),
                                         [[ToSeq(evt)[k]]])))
        Invariant(Forall(int, lambda k: (Implies(r <= k and k < hi, ToSeq(evt)[k] > x),
                                         [[ToSeq(evt)[k]]])))
        mid = (l + r) // 2           # l ≤ mid < r
        if evt[mid] <= x:
            # Math: ∀ k ∈ [a,mid]: evt[k] ≤ evt[mid] ≤ x
            # Why (hint): sorted, so everything up to mid is ≤ x too.
            Assert(Forall(int, lambda k: (Implies(lo <= k and k <= mid,
                                                  ToSeq(evt)[k] <= ToSeq(evt)[mid]),
                                          [[ToSeq(evt)[k]]])))
            l = mid + 1
        else:
            # Math: ∀ k ∈ [mid,hi): evt[k] ≥ evt[mid] > x
            # Why (hint): sorted, so everything from mid on is > x too.
            Assert(Forall(int, lambda k: (Implies(mid <= k and k < hi,
                                                  ToSeq(evt)[mid] <= ToSeq(evt)[k]),
                                          [[ToSeq(evt)[k]]])))
            r = mid
    return l


# --- the walk over G1's block of the current state -------------------------------------------


# left_step: one `left` move (G1 alone): the target state (found or added) and the transition.
# Called from: left_one. The analogue of both_step, with G2 staying in b.
def left_step(n1: int, n2: int, cap: int,
              st1: PSeq[int], ev1: PSeq[int],
              st2: PSeq[int], ev2: PSeq[int], ds2: PSeq[int], mp2: PSeq[int], md: PSeq[int],
              St: PSeq[int], dst1: List[int], pos: Dict[int, int],
              p1: List[int], p2: List[int], evt: List[int], dst: List[int], own: List[int],
              src1: List[int], src2: List[int], h: int, a: int, b: int, k1: int, e: int,
              y1: int, last: int, dt: bool, dt2: bool) -> int:
    """Emit h --e--> (y1, b) with y1 = dst1[k1]; 0, or -1 if find_or_add failed."""
    # Why: read access to G1's target list.
    Requires(Acc(list_pred(dst1), 1 / 8))
    # Math: md[e] = 1 ∧ a --e-->_k1 y1 ∧ y1 ∈ [0,n1) ∧ b ∈ [0,n2)
    # Why: k1 is a transition of a on the G1-only event e, with target y1; G2 stays in b.
    Requires(0 <= e and e < len(md) and md[e] == 1
             and 0 <= a and a + 1 < len(st1) and st1[a] <= k1 and k1 < st1[a + 1]
             and 0 <= k1 and k1 < len(ToSeq(dst1)) and k1 < len(ev1) and ev1[k1] == e
             and ToSeq(dst1)[k1] == y1 and 0 <= y1 and y1 < n1 and 0 <= b and b < n2)
    # Why: write access to the dict, the labels and the transition lists.
    Requires(Acc(dict_pred(pos)) and Acc(list_pred(p1)) and Acc(list_pred(p2)))
    Requires(Acc(list_pred(evt)) and Acc(list_pred(dst)) and Acc(list_pred(own))
             and Acc(list_pred(src1)) and Acc(list_pred(src2)))
    # Math: termination measure 4.
    # Why: calls find_or_add (3) and emit (3).
    Requires(MustTerminate(4))
    # Math: h ∈ [0,|p1|) ∧ φ(h) = (a, b) ∧ |p2| = |p1| ≤ cap
    # Why: h is the current state, with the pair (a, b).
    Requires(len(ToSeq(p2)) == len(ToSeq(p1)) and 0 <= h and h < len(ToSeq(p1))
             and ToSeq(p1)[h] == a and ToSeq(p2)[h] == b and len(p1) <= cap)
    # Math: walk_ok(h, last, dt) ∧ last ≤ e ∧ (dt2 → dt ∧ last < e)
    # Why: the invariant before, and the order of events.
    Requires(walk_ok(n1, n2, st1, ev1, ToSeq(dst1), st2, ev2, ds2, mp2, md, St,
                     ToSeq(p1), ToSeq(p2), ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1),
                     ToSeq(src2), h, last, dt))
    Requires(last <= e and Implies(dt2, dt and last < e))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(dst1), 1 / 8))
    Ensures(Acc(dict_pred(pos)) and Acc(list_pred(p1)) and Acc(list_pred(p2)))
    Ensures(Acc(list_pred(evt)) and Acc(list_pred(dst)) and Acc(list_pred(own))
            and Acc(list_pred(src1)) and Acc(list_pred(src2)))
    # Math: r ∈ {-1, 0}
    # Why: 0 done, -1 no room.
    Ensures(Result() == 0 or Result() == -1)
    # Math: p1_old ⊑ p1 ∧ p2_old ⊑ p2 ∧ |p2| = |p1| ≤ cap ∧ φ(h) = (a, b)
    # Why: only appends to the labels; the current state keeps its pair.
    Ensures(ext(Old(ToSeq(p1)), ToSeq(p1)) and ext(Old(ToSeq(p2)), ToSeq(p2)) and len(p1) <= cap
            and len(ToSeq(p2)) == len(ToSeq(p1)) and h < len(ToSeq(p1))
            and ToSeq(p1)[h] == a and ToSeq(p2)[h] == b)
    # Math: r = 0 → own = own_old · [h] ∧ src1 = src1_old · [k1] ∧ src2 = src2_old · [-1]
    #       ∧ evt = evt_old · [e] ∧ walk_ok(h, e, dt2)
    # Why: the new transition (the caller's witness fact), and the invariant after.
    Ensures(Implies(Result() == 0, appended(Old(ToSeq(own)), ToSeq(own), h)
                    and appended(Old(ToSeq(src1)), ToSeq(src1), k1)
                    and appended(Old(ToSeq(src2)), ToSeq(src2), -1)
                    and appended(Old(ToSeq(evt)), ToSeq(evt), e)
                    and walk_ok(n1, n2, st1, ev1, ToSeq(dst1), st2, ev2, ds2, mp2, md,
                                St, ToSeq(p1), ToSeq(p2), ToSeq(evt), ToSeq(dst), ToSeq(own),
                                ToSeq(src1), ToSeq(src2), h, e, dt2)))
    # Math: r ≠ 0 → own_old ⊑ own ∧ src1_old ⊑ src1 ∧ src2_old ⊑ src2
    # Why: on failure nothing was emitted (the caller's snapshots stay prefixes).
    Ensures(Implies(Result() != 0, ext(Old(ToSeq(own)), ToSeq(own))
                    and ext(Old(ToSeq(src1)), ToSeq(src1))
                    and ext(Old(ToSeq(src2)), ToSeq(src2))))
    j = find_or_add(n1, n2, cap, st1, ev1, ToSeq(dst1), st2, ev2, ds2, mp2, md, St,
                    pos, p1, p2, evt, dst, own, src1, src2, h, last, dt, y1, b)  # the target
    if j < 0:
        # Math: own ⊑ own ∧ src1 ⊑ src1 ∧ src2 ⊑ src2
        # Why (hint): nothing emitted (ext of a list with itself).
        Assert(ext(ToSeq(own), ToSeq(own)) and ext(ToSeq(src1), ToSeq(src1))
               and ext(ToSeq(src2), ToSeq(src2)))
        return -1                    # no room (never with a working dict)
    # Math: φ(h) = (a, b)
    # Why (hint): h < |p1_old|, so its pair is unchanged (ext at h).
    Assert(ToSeq(p1)[h] == Old(ToSeq(p1))[h] and ToSeq(p2)[h] == Old(ToSeq(p2))[h])
    emit(n1, n2, st1, ev1, ToSeq(dst1), st2, ev2, ds2, mp2, md, St, p1, p2, evt, dst,
         own, src1, src2, h, e, j, k1, -1, last, dt, dt2)   # the transition (G2 stays: -1)
    return 0


# left_one: the moves of the current state h that use the G1 transition k1, and their witness.
# Called from: walk_left, once per G1 transition of a = p1[h].
# By the mode of e = evt1[k1]: `left`: one move (left_step); `both`: one move per G2 transition
# of b = p2[h] on e, found by binary search in b's block (sorted by G2's numbers; e's G2 number
# is inv2[e]) and emitted by both_run; otherwise (`none`): no move. The witness w appended to
# wit is the position of the move (`left`), or the base d with the move (k1, k) at d + k (`both`).
# The input lists are read here, so they are lists, and the contracts use their ToSeq.
def left_one(n1: int, n2: int, cap: int,
             start1: List[int], evt1: List[int], dst1: List[int],
             start2: List[int], evt2: List[int], dst2: List[int], mp2: PSeq[int],
             mode: List[int], inv2: List[int], St: PSeq[int], pos: Dict[int, int],
             p1: List[int], p2: List[int], evt: List[int], dst: List[int], own: List[int],
             src1: List[int], src2: List[int], wit: List[int], h: int, a: int, b: int,
             k1: int, last: int, dt: bool) -> int:
    """Emit the moves of h by the G1 transition k1 and append their witness to wit. Returns the
    flag after them (1 true, 0 false), or -1 if find_or_add failed."""
    # Why: read access to the inputs (1/2: the callees get less, so this method keeps a share
    #      and knows the inputs unchanged after each call).
    Requires(Acc(list_pred(start1), 1 / 2) and Acc(list_pred(evt1), 1 / 2)
             and Acc(list_pred(dst1), 1 / 2) and Acc(list_pred(start2), 1 / 2)
             and Acc(list_pred(evt2), 1 / 2) and Acc(list_pred(dst2), 1 / 2)
             and Acc(list_pred(mode), 1 / 2) and Acc(list_pred(inv2), 1 / 2))
    # Why: write access to the dict, the labels, the transition lists and the witnesses.
    Requires(Acc(dict_pred(pos)) and Acc(list_pred(p1)) and Acc(list_pred(p2)))
    Requires(Acc(list_pred(evt)) and Acc(list_pred(dst)) and Acc(list_pred(own))
             and Acc(list_pred(src1)) and Acc(list_pred(src2)) and Acc(list_pred(wit)))
    # Math: termination measure |evt2| + 6.
    # Why: calls both_run (hi - lo + 5 ≤ |evt2| + 5), left_step (4), lbound / ubound (2).
    Requires(MustTerminate(len(ToSeq(evt2)) + 6))
    # Math: a ∈ [0,|start1|-1) ∧ k1 ∈ block1(a) ∧ k1 ∈ [0,|evt1|) ∩ [0,|dst1|)
    # Why: k1 is a transition of a (so evt1[k1], dst1[k1] can be read).
    Requires(0 <= a and a + 1 < len(ToSeq(start1)) and ToSeq(start1)[a] <= k1
             and k1 < ToSeq(start1)[a + 1] and 0 <= k1 and k1 < len(ToSeq(evt1))
             and k1 < len(ToSeq(dst1)))
    # Math: evt1[k1] ∈ [0,|mode|) ∧ dst1[k1] ∈ [0,n1)
    # Why: G1 is valid: its event is an output event, its target a state.
    Requires(0 <= ToSeq(evt1)[k1] and ToSeq(evt1)[k1] < len(ToSeq(mode))
             and 0 <= ToSeq(dst1)[k1] and ToSeq(dst1)[k1] < n1)
    # Math: mode[e] = 0 → e ∈ [0,|inv2|) ∧ inv2[e] ∈ [0,|map2|) ∧ map2[inv2[e]] = e  (e = evt1[k1])
    # Why: a shared event has a G2 number, inv2[e], that map2 sends back to e (the event map
    #      checks give this for every shared e).
    Requires(Implies(ToSeq(mode)[ToSeq(evt1)[k1]] == 0,
                     ToSeq(evt1)[k1] < len(ToSeq(inv2)) and 0 <= ToSeq(inv2)[ToSeq(evt1)[k1]]
                     and ToSeq(inv2)[ToSeq(evt1)[k1]] < len(mp2)
                     and mp2[ToSeq(inv2)[ToSeq(evt1)[k1]]] == ToSeq(evt1)[k1]))
    # Math: b ∈ [0,n2) ∩ [0,|start2|-1) ∧ 0 ≤ start2[b] ≤ start2[b+1] ≤ |evt2| ≤ |dst2|
    # Why: b is a state of G2 and its block can be read.
    Requires(0 <= b and b < n2 and b + 1 < len(ToSeq(start2)) and 0 <= ToSeq(start2)[b]
             and ToSeq(start2)[b] <= ToSeq(start2)[b + 1]
             and ToSeq(start2)[b + 1] <= len(ToSeq(evt2))
             and len(ToSeq(evt2)) <= len(ToSeq(dst2)))
    # Math: ∀ k ∈ block2(b): dst2[k] ∈ [0,n2)
    # Why: G2 is valid: targets are states. Trigger dst2[k].
    Requires(Forall(int, lambda k: (Implies(ToSeq(start2)[b] <= k and k < ToSeq(start2)[b + 1],
                                            0 <= ToSeq(dst2)[k] and ToSeq(dst2)[k] < n2),
                                    [[ToSeq(dst2)[k]]])))
    # Math: ∀ j < i in block2(b): evt2[j] ≤ evt2[i]
    # Why: G2 is valid: its blocks are sorted (needed by the binary search).
    Requires(Forall2(int, int, lambda j, i: (Implies(
        ToSeq(start2)[b] <= j and j < i and i < ToSeq(start2)[b + 1],
        ToSeq(evt2)[j] <= ToSeq(evt2)[i]), [[ToSeq(evt2)[j], ToSeq(evt2)[i]]])))
    # Math: h ∈ [0,|p1|) ∧ φ(h) = (a, b) ∧ |p2| = |p1| ≤ cap
    # Why: h is the current state, with the pair (a, b).
    Requires(len(ToSeq(p2)) == len(ToSeq(p1)) and 0 <= h and h < len(ToSeq(p1))
             and ToSeq(p1)[h] == a and ToSeq(p2)[h] == b and len(p1) <= cap)
    # Math: |own| = |src1| = |src2| = |evt|
    # Why: both_run needs the lengths (inside walk_ok they are hidden: it is opaque).
    Requires(len(ToSeq(own)) == len(ToSeq(evt)) and len(ToSeq(src1)) == len(ToSeq(evt))
             and len(ToSeq(src2)) == len(ToSeq(evt)))
    # Math: walk_ok(h, last, dt) ∧ last ≤ evt1[k1]
    # Why: the invariant before; k1's event comes after the earlier events of h.
    Requires(walk_ok(n1, n2, ToSeq(start1), ToSeq(evt1), ToSeq(dst1), ToSeq(start2),
                     ToSeq(evt2), ToSeq(dst2), mp2, ToSeq(mode), St, ToSeq(p1), ToSeq(p2),
                     ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1), ToSeq(src2), h, last, dt))
    Requires(last <= ToSeq(evt1)[k1])
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start1), 1 / 2) and Acc(list_pred(evt1), 1 / 2)
            and Acc(list_pred(dst1), 1 / 2) and Acc(list_pred(start2), 1 / 2)
            and Acc(list_pred(evt2), 1 / 2) and Acc(list_pred(dst2), 1 / 2)
            and Acc(list_pred(mode), 1 / 2) and Acc(list_pred(inv2), 1 / 2))
    Ensures(Acc(dict_pred(pos)) and Acc(list_pred(p1)) and Acc(list_pred(p2)))
    Ensures(Acc(list_pred(evt)) and Acc(list_pred(dst)) and Acc(list_pred(own))
            and Acc(list_pred(src1)) and Acc(list_pred(src2)) and Acc(list_pred(wit)))
    # Math: the inputs are unchanged
    # Why: the caller passes on facts about them (it gives this method all its share).
    Ensures(ToSeq(start1) == Old(ToSeq(start1)) and ToSeq(evt1) == Old(ToSeq(evt1))
            and ToSeq(dst1) == Old(ToSeq(dst1)) and ToSeq(start2) == Old(ToSeq(start2))
            and ToSeq(evt2) == Old(ToSeq(evt2)) and ToSeq(dst2) == Old(ToSeq(dst2))
            and ToSeq(mode) == Old(ToSeq(mode)) and ToSeq(inv2) == Old(ToSeq(inv2)))
    # Math: r ∈ {-1, 0, 1} ∧ (r = 1 → dt)
    # Why: the flag after the moves (it only goes from true to false), or -1 no room.
    Ensures(Result() >= -1 and Result() <= 1 and Implies(Result() == 1, dt))
    # Math: L_old ⊑ L for p1, p2, own, src1, src2, wit ∧ |p2| = |p1| ≤ cap ∧ φ(h) = (a, b)
    # Why: only appends (the caller's snapshots stay prefixes); the current state's pair.
    Ensures(ext(Old(ToSeq(p1)), ToSeq(p1)) and ext(Old(ToSeq(p2)), ToSeq(p2))
            and ext(Old(ToSeq(own)), ToSeq(own)) and ext(Old(ToSeq(src1)), ToSeq(src1))
            and ext(Old(ToSeq(src2)), ToSeq(src2)) and ext(Old(ToSeq(wit)), ToSeq(wit))
            and len(p1) <= cap and len(ToSeq(p2)) == len(ToSeq(p1)) and h < len(ToSeq(p1))
            and ToSeq(p1)[h] == a and ToSeq(p2)[h] == b)
    # Math: r ≥ 0 → walk_ok(h, evt1[k1], r = 1) ∧ |own| = |src1| = |src2| = |evt|
    #       ∧ |wit| = |wit_old| + 1
    # Why: the invariant after (k1's event is now the last one), and one witness more.
    Ensures(Implies(Result() >= 0,
                    walk_ok(n1, n2, ToSeq(start1), ToSeq(evt1), ToSeq(dst1), ToSeq(start2),
                            ToSeq(evt2), ToSeq(dst2), mp2, ToSeq(mode), St, ToSeq(p1),
                            ToSeq(p2), ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1),
                            ToSeq(src2), h, ToSeq(evt1)[k1], Result() == 1)
                    and len(ToSeq(own)) == len(ToSeq(evt))
                    and len(ToSeq(src1)) == len(ToSeq(evt))
                    and len(ToSeq(src2)) == len(ToSeq(evt))
                    and len(ToSeq(wit)) == len(Old(ToSeq(wit))) + 1))
    # Math: r ≥ 0 ∧ mode[e] = 1 → w ∈ [0,|own|) ∧ own[w] = h ∧ src1[w] = k1 ∧ src2[w] = -1
    #       (e = evt1[k1], w = wit[|wit_old|], the new witness)
    # Why: completeness of the `left` move: it is the output transition w.
    Ensures(Implies(Result() >= 0 and ToSeq(mode)[ToSeq(evt1)[k1]] == 1,
                    0 <= ToSeq(wit)[len(Old(ToSeq(wit)))]
                    and ToSeq(wit)[len(Old(ToSeq(wit)))] < len(ToSeq(own))
                    and ToSeq(own)[ToSeq(wit)[len(Old(ToSeq(wit)))]] == h
                    and ToSeq(src1)[ToSeq(wit)[len(Old(ToSeq(wit)))]] == k1
                    and ToSeq(src2)[ToSeq(wit)[len(Old(ToSeq(wit)))]] == -1))
    # Math: r ≥ 0 ∧ mode[e] = 0 → ∀ k ∈ block2(b): evt2[k] = inv2[e] →
    #         w+k ∈ [0,|own|) ∧ own[w+k] = h ∧ src1[w+k] = k1 ∧ src2[w+k] = k
    # Why: completeness of the `both` moves: the move (k1, k) is the output transition w + k,
    #      for every G2 transition k of b on e. Trigger evt2[k].
    Ensures(Implies(Result() >= 0 and ToSeq(mode)[ToSeq(evt1)[k1]] == 0,
                    Forall(int, lambda k: (Implies(
                        ToSeq(start2)[b] <= k and k < ToSeq(start2)[b + 1],
                        Implies(ToSeq(evt2)[k] == ToSeq(inv2)[ToSeq(evt1)[k1]],
                                0 <= ToSeq(wit)[len(Old(ToSeq(wit)))] + k
                                and ToSeq(wit)[len(Old(ToSeq(wit)))] + k < len(ToSeq(own))
                                and ToSeq(own)[ToSeq(wit)[len(Old(ToSeq(wit)))] + k] == h
                                and ToSeq(src1)[ToSeq(wit)[len(Old(ToSeq(wit)))] + k] == k1
                                and ToSeq(src2)[ToSeq(wit)[len(Old(ToSeq(wit)))] + k] == k)),
                        [[ToSeq(evt2)[k]]]))))
    e = evt1[k1]                     # the event (G1's number = output number)
    y1 = dst1[k1]                    # the G1 target
    m = mode[e]                      # its mode
    if m == 1:
        # `left`: one move, at the next position w
        w = len(evt)
        f = dt and last < e          # the flag after this move
        r = left_step(n1, n2, cap, ToSeq(start1), ToSeq(evt1), ToSeq(start2), ToSeq(evt2),
                      ToSeq(dst2), mp2, ToSeq(mode), St, dst1, pos, p1, p2, evt, dst, own,
                      src1, src2, h, a, b, k1, e, y1, last, dt, f)
        if r < 0:
            # Math: wit ⊑ wit
            # Why (hint): nothing appended to wit.
            Assert(ext(ToSeq(wit), ToSeq(wit)))
            return -1                # no room (never with a working dict)
        wit.append(w)                # the witness: the move is transition w
        # Math: wit = wit_old · [w]
        # Why (hint): the append, as one fact.
        Assert(appended(Old(ToSeq(wit)), ToSeq(wit), w))
        # Math: own_old ⊑ own ∧ src1_old ⊑ src1 ∧ src2_old ⊑ src2 ∧ wit_old ⊑ wit
        # Why: the postcondition "only appends" (appended ⟹ ext).
        ext_app(Old(ToSeq(own)), ToSeq(own), h)
        ext_app(Old(ToSeq(src1)), ToSeq(src1), k1)
        ext_app(Old(ToSeq(src2)), ToSeq(src2), -1)
        ext_app(Old(ToSeq(wit)), ToSeq(wit), w)
        if f:
            return 1
        return 0
    if m == 0:
        # `both`: the G2 transitions of b on e are those on e2 = inv2[e], a run [lo, hi)
        e2 = inv2[e]
        lo = lbound(evt2, start2[b], start2[b + 1], e2)       # first with evt2 ≥ e2
        hi = ubound(evt2, start2[b], lo, start2[b + 1], e2)   # first with evt2 > e2
        # Math: ∀ k ∈ [lo,hi): b --e-->_k dst2[k] (output numbers) ∧ dst2[k] ∈ [0,n2)
        # Why (hint): both_run's precondition: evt2[k] = e2 (≥ and ≤ it), map2[e2] = e, k is
        #      in b's block, and the target is a state. Trigger evt2[k].
        Assert(Forall(int, lambda k: (Implies(lo <= k and k < hi,
                                              0 <= ToSeq(evt2)[k] and ToSeq(evt2)[k] < len(mp2)
                                              and mp2[ToSeq(evt2)[k]] == e
                                              and ToSeq(start2)[b] <= k
                                              and k < ToSeq(start2)[b + 1]
                                              and 0 <= ToSeq(dst2)[k] and ToSeq(dst2)[k] < n2),
                                      [[ToSeq(evt2)[k]]])))
        d = len(evt) - lo            # the move (k1, k) goes to position d + k
        r = both_run(n1, n2, cap, ToSeq(start1), ToSeq(evt1), ToSeq(start2), ToSeq(evt2), mp2,
                     ToSeq(mode), St, dst1, dst2, pos, p1, p2, evt, dst, own, src1, src2,
                     h, a, b, k1, e, y1, lo, lo, hi, d, last, dt)
        if r < 0:
            # Math: wit ⊑ wit
            # Why (hint): nothing appended to wit.
            Assert(ext(ToSeq(wit), ToSeq(wit)))
            return -1                # no room (never with a working dict)
        wit.append(d)                # the witness: the base of the run
        # Math: wit = wit_old · [d]
        # Why (hint): the append, as one fact.
        Assert(appended(Old(ToSeq(wit)), ToSeq(wit), d))
        # Why: wit only grew.
        ext_app(Old(ToSeq(wit)), ToSeq(wit), d)
        # Math: ∀ k ∈ block2(b): evt2[k] = e2 → k ∈ [lo,hi) → own[d+k] = h ∧ ...
        # Why (hint): outside [lo, hi) the event is < e2 or > e2 (the searches); inside, the
        #      run fact of both_run. Trigger evt2[k].
        Assert(Forall(int, lambda k: (Implies(
            ToSeq(start2)[b] <= k and k < ToSeq(start2)[b + 1],
            Implies(ToSeq(evt2)[k] == e2,
                    lo <= k and k < hi and 0 <= d + k and d + k < len(ToSeq(own))
                    and ToSeq(own)[d + k] == h and ToSeq(src1)[d + k] == k1
                    and ToSeq(src2)[d + k] == k)),
            [[ToSeq(evt2)[k]]])))
        return r
    # `none` (or `right`, never for a G1 event): no move; weaken cur_ok from last to e
    # Math: walk_ok(h, last, dt) ⟹ its parts
    # Why (hint): opens the invariant (to change the bound of cur_ok).
    Assert(Reveal(walk_ok(n1, n2, ToSeq(start1), ToSeq(evt1), ToSeq(dst1), ToSeq(start2),
                          ToSeq(evt2), ToSeq(dst2), mp2, ToSeq(mode), St, ToSeq(p1), ToSeq(p2),
                          ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1), ToSeq(src2), h,
                          last, dt)))
    # Math: ∀ j: own[j] = h → evt[j] ≤ last ≤ e
    # Why (hint): cur_ok with the larger bound e. Trigger evt[j], as in cur_ok.
    Assert(Forall(int, lambda jj: (Implies(0 <= jj and jj < len(ToSeq(evt))
                                           and ToSeq(own)[jj] == h,
                                           ToSeq(evt)[jj] <= e), [[ToSeq(evt)[jj]]])))
    # Math: walk_ok(h, e, dt)
    # Why (hint): closes it with the new bound.
    Assert(Reveal(walk_ok(n1, n2, ToSeq(start1), ToSeq(evt1), ToSeq(dst1), ToSeq(start2),
                          ToSeq(evt2), ToSeq(dst2), mp2, ToSeq(mode), St, ToSeq(p1), ToSeq(p2),
                          ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1), ToSeq(src2), h,
                          e, dt)))
    wit.append(0)                    # no move: the witness is unused
    # Why: wit only grew (the other lists are unchanged).
    ext_app(Old(ToSeq(wit)), ToSeq(wit), 0)
    # Math: L ⊑ L for p1, p2, own, src1, src2
    # Why (hint): nothing changed (ext of a list with itself).
    Assert(ext(ToSeq(p1), ToSeq(p1)) and ext(ToSeq(p2), ToSeq(p2))
           and ext(ToSeq(own), ToSeq(own)) and ext(ToSeq(src1), ToSeq(src1))
           and ext(ToSeq(src2), ToSeq(src2)))
    if dt:
        return 1
    return 0


# raise_last: walk_ok with a larger bound for cur_ok.
# Used in: walk_left at the end of G1's block (bound raised to top, before the G2-only events).
# A lemma, so that the callers never open walk_ok (in walk_left it made the method too slow).
def raise_last(n1: int, n2: int, st1: PSeq[int], ev1: PSeq[int], ds1: PSeq[int],
               st2: PSeq[int], ev2: PSeq[int], ds2: PSeq[int], mp2: PSeq[int], md: PSeq[int],
               St: PSeq[int], P1: PSeq[int], P2: PSeq[int], Ev: PSeq[int], Ds: PSeq[int],
               Ow: PSeq[int], S1: PSeq[int], S2: PSeq[int], h: int, last: int, top: int,
               dt: bool) -> None:
    """Lemma: walk_ok(h, last, dt) and last ≤ top give walk_ok(h, top, dt)."""
    # Math: termination measure 1.
    # Why: no loops and no calls.
    Requires(MustTerminate(1))
    # Math: walk_ok(h, last, dt) ∧ last ≤ top
    # Why: the invariant, and the larger bound.
    Requires(walk_ok(n1, n2, st1, ev1, ds1, st2, ev2, ds2, mp2, md, St, P1, P2, Ev, Ds, Ow, S1,
                     S2, h, last, dt) and last <= top)
    # Math: walk_ok(h, top, dt)
    # Why: the fact (only cur_ok's bound changes).
    Ensures(walk_ok(n1, n2, st1, ev1, ds1, st2, ev2, ds2, mp2, md, St, P1, P2, Ev, Ds, Ow, S1,
                    S2, h, top, dt))
    # Math: walk_ok(h, last, dt) ⟹ its parts
    # Why (hint): opens the invariant.
    Assert(Reveal(walk_ok(n1, n2, st1, ev1, ds1, st2, ev2, ds2, mp2, md, St, P1, P2, Ev, Ds, Ow,
                          S1, S2, h, last, dt)))
    # Math: ∀ j: own[j] = h → evt[j] ≤ last ≤ top
    # Why (hint): cur_ok with the bound top. Trigger evt[j], as in cur_ok.
    Assert(Forall(int, lambda jj: (Implies(0 <= jj and jj < len(Ev) and Ow[jj] == h,
                                           Ev[jj] <= top), [[Ev[jj]]])))
    # Math: walk_ok(h, top, dt)
    # Why (hint): closes it with the new bound.
    Assert(Reveal(walk_ok(n1, n2, st1, ev1, ds1, st2, ev2, ds2, mp2, md, St, P1, P2, Ev, Ds, Ow,
                          S1, S2, h, top, dt)))


# left_done: the completeness facts of the walk over G1's block, for q ∈ [start1[a], k1).
# Used in: walk_left (passed on as one term), carry_left (opens it).
# @Opaque, as walk_ok: written out in walk_left's contract, the facts made the method too long for
# Silicon, which crashed with a stack overflow (2026-11-03).
@Opaque
@Pure
def left_done(S1: PSeq[int], E1: PSeq[int], M: PSeq[int], S2: PSeq[int], E2: PSeq[int],
              I2: PSeq[int], mp2: PSeq[int], W: PSeq[int], O: PSeq[int], A: PSeq[int],
              B: PSeq[int], h: int, a: int, b: int, c: int, k1: int) -> bool:
    """Every move of h by a G1 transition q ∈ [start1[a], k1) is an output transition, found
    through the witness wit[c + q]."""
    # Math: a ∈ [0,|start1|-1) ∧ 0 ≤ start1[a] ≤ k1 ≤ start1[a+1] ≤ |evt1|
    # Why: so the reads below are in range (a pure function's body must be well defined).
    Requires(0 <= a and a + 1 < len(S1) and 0 <= S1[a] and S1[a] <= k1 and k1 <= S1[a + 1]
             and S1[a + 1] <= len(E1))
    # Math: ∀ k ∈ block1(a): evt1[k] ∈ [0,|mode|)
    # Why: so mode[evt1[q]] can be read. Trigger evt1[k].
    Requires(Forall(int, lambda k: (Implies(S1[a] <= k and k < S1[a + 1],
                                            0 <= E1[k] and E1[k] < len(M)), [[E1[k]]])))
    # Math: ∀ e ∈ [0,|mode|): mode[e] = 0 → e ∈ [0,|inv2|) ∧ inv2[e] ∈ [0,|map2|) ∧ map2[inv2[e]] = e
    # Why: so inv2[evt1[q]] can be read (for a shared event). Trigger mode[e].
    Requires(Forall(int, lambda ee: (Implies(0 <= ee and ee < len(M) and M[ee] == 0,
                                             ee < len(I2) and 0 <= I2[ee] and I2[ee] < len(mp2)
                                             and mp2[I2[ee]] == ee), [[M[ee]]])))
    # Math: b ∈ [0,|start2|-1) ∧ 0 ≤ start2[b] ≤ start2[b+1] ≤ |evt2|
    # Why: so evt2[k] can be read for k in b's block.
    Requires(0 <= b and b + 1 < len(S2) and 0 <= S2[b] and S2[b] <= S2[b + 1]
             and S2[b + 1] <= len(E2))
    # Math: |wit| ≥ c + k1 ∧ c + start1[a] ≥ 0 ∧ |src1| = |src2| = |own|
    # Why: so wit[c + q] can be read, and src1, src2 wherever own can.
    Requires(len(W) >= c + k1 and 0 <= c + S1[a] and len(A) == len(O) and len(B) == len(O))
    # Math: (∀ q ∈ [start1[a],k1): mode[evt1[q]] = 1 → w ∈ [0,|own|) ∧ own[w] = h
    #          ∧ src1[w] = q ∧ src2[w] = -1)
    #       ∧ (∀ q ∈ [start1[a],k1), k ∈ block2(b): mode[evt1[q]] = 0 ∧ evt2[k] = inv2[evt1[q]] →
    #          w+k ∈ [0,|own|) ∧ own[w+k] = h ∧ src1[w+k] = q ∧ src2[w+k] = k)     (w = wit[c+q])
    # Why: the `left` move of q is the output transition w; the `both` move (q, k) is w + k
    #      (Lean: step_complete, for the moves through G1's transitions). Triggers: wit[c + q];
    #      wit[c + q] with evt2[k].
    return (Forall(int, lambda q: (Implies(
                S1[a] <= q and q < k1,
                Implies(M[E1[q]] == 1,
                        0 <= W[c + q] and W[c + q] < len(O) and O[W[c + q]] == h
                        and A[W[c + q]] == q and B[W[c + q]] == -1)),
                [[W[c + q]]]))
            and Forall2(int, int, lambda q, k: (Implies(
                S1[a] <= q and q < k1,
                Implies(M[E1[q]] == 0 and S2[b] <= k and k < S2[b + 1],
                        Implies(E2[k] == I2[E1[q]],
                                0 <= W[c + q] + k and W[c + q] + k < len(O)
                                and O[W[c + q] + k] == h and A[W[c + q] + k] == q
                                and B[W[c + q] + k] == k))),
                [[W[c + q], E2[k]]])))

# carry_left: the completeness facts of walk_left, from [start1[a], k1) to [start1[a], k1].
# Used in: walk_left, after left_one. The old facts were stated on the lists before left_one
# (W0, O0, A0, B0); the lists only grew, so the old entries still hold; the fact at k1 is
# left_one's (its witness is W[|W0|] = W[c + k1]).
def carry_left(S1: PSeq[int], E1: PSeq[int], M: PSeq[int], S2: PSeq[int], E2: PSeq[int],
               I2: PSeq[int], mp2: PSeq[int], W0: PSeq[int], O0: PSeq[int], A0: PSeq[int],
               B0: PSeq[int], W: PSeq[int], O: PSeq[int], A: PSeq[int], B: PSeq[int],
               h: int, a: int, b: int, c: int, k1: int) -> None:
    """Lemma: the walk's completeness facts, one G1 transition further."""
    # Math: termination measure 1.
    # Why: no loops and no calls.
    Requires(MustTerminate(1))
    # Math: a ∈ [0,|start1|-1) ∧ 0 ≤ start1[a] ≤ k1 < start1[a+1] ≤ |evt1|
    # Why: k1 is in a's block, which can be read.
    Requires(0 <= a and a + 1 < len(S1) and 0 <= S1[a] and S1[a] <= k1 and k1 < S1[a + 1]
             and S1[a + 1] <= len(E1))
    # Math: ∀ k ∈ block1(a): evt1[k] ∈ [0,|mode|)
    # Why: so mode[evt1[q]] can be read. Trigger evt1[k].
    Requires(Forall(int, lambda k: (Implies(S1[a] <= k and k < S1[a + 1],
                                            0 <= E1[k] and E1[k] < len(M)), [[E1[k]]])))
    # Math: ∀ e ∈ [0,|mode|): mode[e] = 0 → e ∈ [0,|inv2|) ∧ inv2[e] ∈ [0,|map2|) ∧ map2[inv2[e]] = e
    # Why: so inv2[evt1[q]] can be read (for a shared event). Trigger mode[e].
    Requires(Forall(int, lambda ee: (Implies(0 <= ee and ee < len(M) and M[ee] == 0,
                                             ee < len(I2) and 0 <= I2[ee] and I2[ee] < len(mp2)
                                             and mp2[I2[ee]] == ee), [[M[ee]]])))
    # Math: b ∈ [0,|start2|-1) ∧ start2[b] ≤ start2[b+1] ≤ |evt2|
    # Why: b's block can be read.
    Requires(0 <= b and b + 1 < len(S2) and 0 <= S2[b] and S2[b] <= S2[b + 1]
             and S2[b + 1] <= len(E2))
    # Math: |W0| = c + k1 ∧ c + start1[a] ≥ 0 ∧ |W| = |W0| + 1
    #       ∧ W0 ⊑ W ∧ O0 ⊑ O ∧ A0 ⊑ A ∧ B0 ⊑ B
    # Why: left_one appended one witness and only appended to own, src1, src2.
    Requires(len(W0) == c + k1 and 0 <= c + S1[a] and len(W) == len(W0) + 1
             and ext(W0, W) and ext(O0, O) and ext(A0, A) and ext(B0, B))
    # Math: |src1| = |src2| = |own|, before and after
    # Why: so src1, src2 can be read wherever own can.
    Requires(len(A0) == len(O0) and len(B0) == len(O0) and len(A) == len(O) and len(B) == len(O))
    # Math: left_done(before, k1)
    # Why: walk_left's precondition (the facts for q < k1, on the lists before left_one).
    Requires(left_done(S1, E1, M, S2, E2, I2, mp2, W0, O0, A0, B0, h, a, b, c, k1))
    # Math: the `left` and `both` facts at k1, with the witness w = W[|W0|]
    # Why: left_one's postconditions.
    Requires(Implies(M[E1[k1]] == 1,
                     0 <= W[len(W0)] and W[len(W0)] < len(O) and O[W[len(W0)]] == h
                     and A[W[len(W0)]] == k1 and B[W[len(W0)]] == -1))
    Requires(Implies(M[E1[k1]] == 0,
                     Forall(int, lambda k: (Implies(
                         S2[b] <= k and k < S2[b + 1],
                         Implies(E2[k] == I2[E1[k1]],
                                 0 <= W[len(W0)] + k and W[len(W0)] + k < len(O)
                                 and O[W[len(W0)] + k] == h and A[W[len(W0)] + k] == k1
                                 and B[W[len(W0)] + k] == k)),
                         [[E2[k]]]))))
    # Math: left_done(after, k1 + 1)
    # Why: the fact, one G1 transition further.
    Ensures(left_done(S1, E1, M, S2, E2, I2, mp2, W, O, A, B, h, a, b, c, k1 + 1))
    # Math: left_done(before, k1) ⟹ its body
    # Why (hint): opens the opaque definition (the facts for q < k1).
    Assert(Reveal(left_done(S1, E1, M, S2, E2, I2, mp2, W0, O0, A0, B0, h, a, b, c, k1)))
    # Math: left_done(after, k1 + 1), from its body
    # Why (hint): closes it: old q from the old entries (the lists only grew), q = k1 from
    #      left_one's facts.
    Assert(Reveal(left_done(S1, E1, M, S2, E2, I2, mp2, W, O, A, B, h, a, b, c, k1 + 1)))


# left_next: one step of walk_left: left_one for the G1 transition k1, and the completeness
# facts carried from [start1[a], k1) to [start1[a], k1].
# Called from: walk_left. A separate method because Silicon's stack depth grows with the length
# of a method's path; with this inside, walk_left crashed with a stack overflow (2026-11-03).
def left_next(n1: int, n2: int, cap: int,
              start1: List[int], evt1: List[int], dst1: List[int],
              start2: List[int], evt2: List[int], dst2: List[int], mp2: PSeq[int],
              mode: List[int], inv2: List[int], St: PSeq[int], pos: Dict[int, int],
              p1: List[int], p2: List[int], evt: List[int], dst: List[int], own: List[int],
              src1: List[int], src2: List[int], wit: List[int], h: int, a: int, b: int,
              c: int, k1: int, top: int, last: int, dt: bool) -> int:
    """Emit the moves of h by the G1 transition k1, with its witness. Returns the flag
    after them (1 true, 0 false), or -1 if find_or_add failed."""
    # Why: read access to the inputs (all passed on to left_one, which gives them back
    #      unchanged).
    Requires(Acc(list_pred(start1), 1 / 2) and Acc(list_pred(evt1), 1 / 2)
             and Acc(list_pred(dst1), 1 / 2) and Acc(list_pred(start2), 1 / 2)
             and Acc(list_pred(evt2), 1 / 2) and Acc(list_pred(dst2), 1 / 2)
             and Acc(list_pred(mode), 1 / 2) and Acc(list_pred(inv2), 1 / 2))
    # Why: write access to the dict, the labels, the transition lists and the witnesses.
    Requires(Acc(dict_pred(pos)) and Acc(list_pred(p1)) and Acc(list_pred(p2)))
    Requires(Acc(list_pred(evt)) and Acc(list_pred(dst)) and Acc(list_pred(own))
             and Acc(list_pred(src1)) and Acc(list_pred(src2)) and Acc(list_pred(wit)))
    # Math: a ∈ [0,|start1|-1) ∧ 0 ≤ start1[a] ≤ k1 < start1[a+1] ≤ |evt1| ≤ |dst1|
    # Why: k1 is a transition of a's block, which can be read.
    Requires(0 <= a and a + 1 < len(ToSeq(start1)) and 0 <= ToSeq(start1)[a]
             and ToSeq(start1)[a] <= k1 and k1 < ToSeq(start1)[a + 1]
             and ToSeq(start1)[a + 1] <= len(ToSeq(evt1))
             and len(ToSeq(evt1)) <= len(ToSeq(dst1)))
    # Math: termination measure |evt2| + 7.
    # Why: calls left_one (|evt2| + 6) and lemmas.
    Requires(MustTerminate(len(ToSeq(evt2)) + 7))
    # Math: top < |mode| ∧ ∀ k ∈ block1(a): evt1[k] ∈ [0,top]
    # Why: G1 is valid: its events are output events, all ≤ top. Trigger evt1[k].
    Requires(top < len(ToSeq(mode)))
    Requires(Forall(int, lambda k: (Implies(ToSeq(start1)[a] <= k and k < ToSeq(start1)[a + 1],
                                            0 <= ToSeq(evt1)[k] and ToSeq(evt1)[k] <= top),
                                    [[ToSeq(evt1)[k]]])))
    # Math: ∀ k ∈ block1(a): dst1[k] ∈ [0,n1)
    # Why: G1 is valid: targets are states. Trigger dst1[k].
    Requires(Forall(int, lambda k: (Implies(ToSeq(start1)[a] <= k and k < ToSeq(start1)[a + 1],
                                            0 <= ToSeq(dst1)[k] and ToSeq(dst1)[k] < n1),
                                    [[ToSeq(dst1)[k]]])))
    # Math: ∀ j < i in block1(a): evt1[j] ≤ evt1[i]
    # Why: G1 is valid: its blocks are sorted (the moves come in event order).
    Requires(Forall2(int, int, lambda j, i: (Implies(
        ToSeq(start1)[a] <= j and j < i and i < ToSeq(start1)[a + 1],
        ToSeq(evt1)[j] <= ToSeq(evt1)[i]), [[ToSeq(evt1)[j], ToSeq(evt1)[i]]])))
    # Math: ∀ e ∈ [0,|mode|): mode[e] = 0 → e ∈ [0,|inv2|) ∧ inv2[e] ∈ [0,|map2|)
    #                                        ∧ map2[inv2[e]] = e
    # Why: every shared event has a G2 number (the event map checks). Trigger mode[e].
    Requires(Forall(int, lambda ee: (Implies(0 <= ee and ee < len(ToSeq(mode))
                                             and ToSeq(mode)[ee] == 0,
                                             ee < len(ToSeq(inv2)) and 0 <= ToSeq(inv2)[ee]
                                             and ToSeq(inv2)[ee] < len(mp2)
                                             and mp2[ToSeq(inv2)[ee]] == ee),
                                     [[ToSeq(mode)[ee]]])))
    # Math: b ∈ [0,n2) ∩ [0,|start2|-1) ∧ 0 ≤ start2[b] ≤ start2[b+1] ≤ |evt2| ≤ |dst2|
    # Why: b is a state of G2 and its block can be read.
    Requires(0 <= b and b < n2 and b + 1 < len(ToSeq(start2)) and 0 <= ToSeq(start2)[b]
             and ToSeq(start2)[b] <= ToSeq(start2)[b + 1]
             and ToSeq(start2)[b + 1] <= len(ToSeq(evt2))
             and len(ToSeq(evt2)) <= len(ToSeq(dst2)))
    # Math: ∀ k ∈ block2(b): dst2[k] ∈ [0,n2)
    # Why: G2 is valid: targets are states. Trigger dst2[k].
    Requires(Forall(int, lambda k: (Implies(ToSeq(start2)[b] <= k and k < ToSeq(start2)[b + 1],
                                            0 <= ToSeq(dst2)[k] and ToSeq(dst2)[k] < n2),
                                    [[ToSeq(dst2)[k]]])))
    # Math: ∀ j < i in block2(b): evt2[j] ≤ evt2[i]
    # Why: G2 is valid: its blocks are sorted (for the binary search).
    Requires(Forall2(int, int, lambda j, i: (Implies(
        ToSeq(start2)[b] <= j and j < i and i < ToSeq(start2)[b + 1],
        ToSeq(evt2)[j] <= ToSeq(evt2)[i]), [[ToSeq(evt2)[j], ToSeq(evt2)[i]]])))
    # Math: h ∈ [0,|p1|) ∧ φ(h) = (a, b) ∧ |p2| = |p1| ≤ cap
    # Why: h is the current state, with the pair (a, b).
    Requires(len(ToSeq(p2)) == len(ToSeq(p1)) and 0 <= h and h < len(ToSeq(p1))
             and ToSeq(p1)[h] == a and ToSeq(p2)[h] == b and len(p1) <= cap)
    # Math: |own| = |src1| = |src2| = |evt|
    # Why: the lengths (hidden in walk_ok).
    Requires(len(ToSeq(own)) == len(ToSeq(evt)) and len(ToSeq(src1)) == len(ToSeq(evt))
             and len(ToSeq(src2)) == len(ToSeq(evt)))
    # Math: walk_ok(h, last, dt) ∧ last ≤ evt1[k1]
    # Why: the invariant before; k1's event comes after the earlier ones.
    Requires(walk_ok(n1, n2, ToSeq(start1), ToSeq(evt1), ToSeq(dst1), ToSeq(start2),
                     ToSeq(evt2), ToSeq(dst2), mp2, ToSeq(mode), St, ToSeq(p1), ToSeq(p2),
                     ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1), ToSeq(src2), h, last, dt))
    Requires(last <= ToSeq(evt1)[k1])
    # Math: |wit| = c + k1 ∧ c + start1[a] ≥ 0
    # Why: the witness of q is wit[c + q]; the next one is k1's.
    Requires(len(ToSeq(wit)) == c + k1 and 0 <= c + ToSeq(start1)[a])
    # Math: left_done(k1)
    # Why: completeness so far: the moves by the G1 transitions before k1.
    Requires(left_done(ToSeq(start1), ToSeq(evt1), ToSeq(mode), ToSeq(start2), ToSeq(evt2),
                       ToSeq(inv2), mp2, ToSeq(wit), ToSeq(own), ToSeq(src1), ToSeq(src2),
                       h, a, b, c, k1))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start1), 1 / 2) and Acc(list_pred(evt1), 1 / 2)
            and Acc(list_pred(dst1), 1 / 2) and Acc(list_pred(start2), 1 / 2)
            and Acc(list_pred(evt2), 1 / 2) and Acc(list_pred(dst2), 1 / 2)
            and Acc(list_pred(mode), 1 / 2) and Acc(list_pred(inv2), 1 / 2))
    Ensures(Acc(dict_pred(pos)) and Acc(list_pred(p1)) and Acc(list_pred(p2)))
    Ensures(Acc(list_pred(evt)) and Acc(list_pred(dst)) and Acc(list_pred(own))
            and Acc(list_pred(src1)) and Acc(list_pred(src2)) and Acc(list_pred(wit)))
    # Math: the inputs are unchanged
    # Why: the caller passes on facts about them.
    Ensures(ToSeq(start1) == Old(ToSeq(start1)) and ToSeq(evt1) == Old(ToSeq(evt1))
            and ToSeq(dst1) == Old(ToSeq(dst1)) and ToSeq(start2) == Old(ToSeq(start2))
            and ToSeq(evt2) == Old(ToSeq(evt2)) and ToSeq(dst2) == Old(ToSeq(dst2))
            and ToSeq(mode) == Old(ToSeq(mode)) and ToSeq(inv2) == Old(ToSeq(inv2)))
    # Math: r ∈ {-1, 0, 1} ∧ (r = 1 → dt)
    # Why: the flag after the walk, or -1 no room.
    Ensures(Result() >= -1 and Result() <= 1 and Implies(Result() == 1, dt))
    # Math: L_old ⊑ L for p1, p2, own, src1, src2, wit ∧ |p2| = |p1| ≤ cap ∧ φ(h) = (a, b)
    # Why: only appends; the current state's pair.
    Ensures(ext(Old(ToSeq(p1)), ToSeq(p1)) and ext(Old(ToSeq(p2)), ToSeq(p2))
            and ext(Old(ToSeq(own)), ToSeq(own)) and ext(Old(ToSeq(src1)), ToSeq(src1))
            and ext(Old(ToSeq(src2)), ToSeq(src2)) and ext(Old(ToSeq(wit)), ToSeq(wit))
            and len(p1) <= cap and len(ToSeq(p2)) == len(ToSeq(p1)) and h < len(ToSeq(p1))
            and ToSeq(p1)[h] == a and ToSeq(p2)[h] == b)
    # Math: r ≥ 0 → walk_ok(h, evt1[k1], r = 1) ∧ |own| = |src1| = |src2| = |evt|
    #       ∧ |wit| = c + k1 + 1
    # Why: the invariant after (k1's event is the last one), and one witness more.
    Ensures(Implies(Result() >= 0,
                    walk_ok(n1, n2, ToSeq(start1), ToSeq(evt1), ToSeq(dst1), ToSeq(start2),
                            ToSeq(evt2), ToSeq(dst2), mp2, ToSeq(mode), St, ToSeq(p1),
                            ToSeq(p2), ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1),
                            ToSeq(src2), h, ToSeq(evt1)[k1], Result() == 1)
                    and len(ToSeq(own)) == len(ToSeq(evt))
                    and len(ToSeq(src1)) == len(ToSeq(evt))
                    and len(ToSeq(src2)) == len(ToSeq(evt))
                    and len(ToSeq(wit)) == c + k1 + 1))
    # Math: r ≥ 0 → left_done(k1 + 1)
    # Why: completeness one G1 transition further.
    Ensures(Implies(Result() >= 0,
                    left_done(ToSeq(start1), ToSeq(evt1), ToSeq(mode), ToSeq(start2),
                              ToSeq(evt2), ToSeq(inv2), mp2, ToSeq(wit), ToSeq(own),
                              ToSeq(src1), ToSeq(src2), h, a, b, c, k1 + 1)))
    # Math: evt1[k1] ∈ [0,top] ∧ dst1[k1] ∈ [0,n1)
    # Why (hint): left_one's preconditions at k1, from the quantifiers above (mentioning
    #      evt1[k1] and dst1[k1] triggers them; the map fact is then triggered by mode[evt1[k1]]
    #      in left_one's precondition).
    Assert(0 <= ToSeq(evt1)[k1] and ToSeq(evt1)[k1] <= top and 0 <= ToSeq(dst1)[k1]
           and ToSeq(dst1)[k1] < n1)
    W0 = ToSeq(wit)                  # snapshots before left_one (proof only)
    O0 = ToSeq(own)
    A0 = ToSeq(src1)
    B0 = ToSeq(src2)
    r = left_one(n1, n2, cap, start1, evt1, dst1, start2, evt2, dst2, mp2, mode, inv2, St,
                 pos, p1, p2, evt, dst, own, src1, src2, wit, h, a, b, k1, last, dt)  # k1
    if r < 0:
        return -1                    # no room (never with a working dict)
    # Math: the `left` and `both` completeness facts for all q ∈ [start1[a],k1]
    # Why: q < k1 carried over left_one's appends, q = k1 from left_one (a lemma: written here,
    #      the proofs made walk_left too long for Silicon, which crashed, 2026-11-03).
    carry_left(ToSeq(start1), ToSeq(evt1), ToSeq(mode), ToSeq(start2), ToSeq(evt2),
               ToSeq(inv2), mp2, W0, O0, A0, B0, ToSeq(wit), ToSeq(own), ToSeq(src1),
               ToSeq(src2), h, a, b, c, k1)
    return r


# walk_left: the moves of the current state h by G1's transitions k1 .. end of a = p1[h]
# (end = start1[a+1]), one left_one each, collecting their completeness witnesses.
# Called from: the per-state method (k1 = start1[a]), and itself (k1 + 1).
# Recursive rather than a loop, as both_run. The witness of the G1 transition q is wit[c + q]
# (c = |wit| - start1[a] when the state's walk begins).
# At the end the bound of cur_ok is raised to top (≥ every G1 event), so the G2-only events
# (numbers > top) can follow.
def walk_left(n1: int, n2: int, cap: int,
              start1: List[int], evt1: List[int], dst1: List[int],
              start2: List[int], evt2: List[int], dst2: List[int], mp2: PSeq[int],
              mode: List[int], inv2: List[int], St: PSeq[int], pos: Dict[int, int],
              p1: List[int], p2: List[int], evt: List[int], dst: List[int], own: List[int],
              src1: List[int], src2: List[int], wit: List[int], h: int, a: int, b: int,
              c: int, k1: int, top: int, last: int, dt: bool) -> int:
    """Emit the moves of h by G1's transitions k1 .. start1[a+1] - 1, with their witnesses.
    Returns the flag after them (1 true, 0 false), or -1 if find_or_add failed."""
    # Why: read access to the inputs (all passed on to left_one, which gives them back
    #      unchanged).
    Requires(Acc(list_pred(start1), 1 / 2) and Acc(list_pred(evt1), 1 / 2)
             and Acc(list_pred(dst1), 1 / 2) and Acc(list_pred(start2), 1 / 2)
             and Acc(list_pred(evt2), 1 / 2) and Acc(list_pred(dst2), 1 / 2)
             and Acc(list_pred(mode), 1 / 2) and Acc(list_pred(inv2), 1 / 2))
    # Why: write access to the dict, the labels, the transition lists and the witnesses.
    Requires(Acc(dict_pred(pos)) and Acc(list_pred(p1)) and Acc(list_pred(p2)))
    Requires(Acc(list_pred(evt)) and Acc(list_pred(dst)) and Acc(list_pred(own))
             and Acc(list_pred(src1)) and Acc(list_pred(src2)) and Acc(list_pred(wit)))
    # Math: a ∈ [0,|start1|-1) ∧ 0 ≤ start1[a] ≤ k1 ≤ start1[a+1] ≤ |evt1| ≤ |dst1|
    # Why: k1 runs over a's block, which can be read.
    Requires(0 <= a and a + 1 < len(ToSeq(start1)) and 0 <= ToSeq(start1)[a]
             and ToSeq(start1)[a] <= k1 and k1 <= ToSeq(start1)[a + 1]
             and ToSeq(start1)[a + 1] <= len(ToSeq(evt1))
             and len(ToSeq(evt1)) <= len(ToSeq(dst1)))
    # Math: termination measure start1[a+1] - k1 + |evt2| + 7.
    # Why: decreases with each recursive call (k1 + 1); left_one has |evt2| + 6.
    Requires(MustTerminate(ToSeq(start1)[a + 1] - k1 + len(ToSeq(evt2)) + 7))
    # Math: top < |mode| ∧ ∀ k ∈ block1(a): evt1[k] ∈ [0,top]
    # Why: G1 is valid: its events are output events, all ≤ top. Trigger evt1[k].
    Requires(top < len(ToSeq(mode)))
    Requires(Forall(int, lambda k: (Implies(ToSeq(start1)[a] <= k and k < ToSeq(start1)[a + 1],
                                            0 <= ToSeq(evt1)[k] and ToSeq(evt1)[k] <= top),
                                    [[ToSeq(evt1)[k]]])))
    # Math: ∀ k ∈ block1(a): dst1[k] ∈ [0,n1)
    # Why: G1 is valid: targets are states. Trigger dst1[k].
    Requires(Forall(int, lambda k: (Implies(ToSeq(start1)[a] <= k and k < ToSeq(start1)[a + 1],
                                            0 <= ToSeq(dst1)[k] and ToSeq(dst1)[k] < n1),
                                    [[ToSeq(dst1)[k]]])))
    # Math: ∀ j < i in block1(a): evt1[j] ≤ evt1[i]
    # Why: G1 is valid: its blocks are sorted (the moves come in event order).
    Requires(Forall2(int, int, lambda j, i: (Implies(
        ToSeq(start1)[a] <= j and j < i and i < ToSeq(start1)[a + 1],
        ToSeq(evt1)[j] <= ToSeq(evt1)[i]), [[ToSeq(evt1)[j], ToSeq(evt1)[i]]])))
    # Math: ∀ e ∈ [0,|mode|): mode[e] = 0 → e ∈ [0,|inv2|) ∧ inv2[e] ∈ [0,|map2|)
    #                                        ∧ map2[inv2[e]] = e
    # Why: every shared event has a G2 number (the event map checks). Trigger mode[e].
    Requires(Forall(int, lambda ee: (Implies(0 <= ee and ee < len(ToSeq(mode))
                                             and ToSeq(mode)[ee] == 0,
                                             ee < len(ToSeq(inv2)) and 0 <= ToSeq(inv2)[ee]
                                             and ToSeq(inv2)[ee] < len(mp2)
                                             and mp2[ToSeq(inv2)[ee]] == ee),
                                     [[ToSeq(mode)[ee]]])))
    # Math: b ∈ [0,n2) ∩ [0,|start2|-1) ∧ 0 ≤ start2[b] ≤ start2[b+1] ≤ |evt2| ≤ |dst2|
    # Why: b is a state of G2 and its block can be read.
    Requires(0 <= b and b < n2 and b + 1 < len(ToSeq(start2)) and 0 <= ToSeq(start2)[b]
             and ToSeq(start2)[b] <= ToSeq(start2)[b + 1]
             and ToSeq(start2)[b + 1] <= len(ToSeq(evt2))
             and len(ToSeq(evt2)) <= len(ToSeq(dst2)))
    # Math: ∀ k ∈ block2(b): dst2[k] ∈ [0,n2)
    # Why: G2 is valid: targets are states. Trigger dst2[k].
    Requires(Forall(int, lambda k: (Implies(ToSeq(start2)[b] <= k and k < ToSeq(start2)[b + 1],
                                            0 <= ToSeq(dst2)[k] and ToSeq(dst2)[k] < n2),
                                    [[ToSeq(dst2)[k]]])))
    # Math: ∀ j < i in block2(b): evt2[j] ≤ evt2[i]
    # Why: G2 is valid: its blocks are sorted (for the binary search).
    Requires(Forall2(int, int, lambda j, i: (Implies(
        ToSeq(start2)[b] <= j and j < i and i < ToSeq(start2)[b + 1],
        ToSeq(evt2)[j] <= ToSeq(evt2)[i]), [[ToSeq(evt2)[j], ToSeq(evt2)[i]]])))
    # Math: h ∈ [0,|p1|) ∧ φ(h) = (a, b) ∧ |p2| = |p1| ≤ cap
    # Why: h is the current state, with the pair (a, b).
    Requires(len(ToSeq(p2)) == len(ToSeq(p1)) and 0 <= h and h < len(ToSeq(p1))
             and ToSeq(p1)[h] == a and ToSeq(p2)[h] == b and len(p1) <= cap)
    # Math: |own| = |src1| = |src2| = |evt|
    # Why: the lengths (hidden in walk_ok).
    Requires(len(ToSeq(own)) == len(ToSeq(evt)) and len(ToSeq(src1)) == len(ToSeq(evt))
             and len(ToSeq(src2)) == len(ToSeq(evt)))
    # Math: walk_ok(h, last, dt) ∧ last ≤ top ∧ (k1 < start1[a+1] → last ≤ evt1[k1])
    # Why: the invariant before; the next event comes after the earlier ones.
    Requires(walk_ok(n1, n2, ToSeq(start1), ToSeq(evt1), ToSeq(dst1), ToSeq(start2),
                     ToSeq(evt2), ToSeq(dst2), mp2, ToSeq(mode), St, ToSeq(p1), ToSeq(p2),
                     ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1), ToSeq(src2), h, last, dt))
    Requires(last <= top and Implies(k1 < ToSeq(start1)[a + 1], last <= ToSeq(evt1)[k1]))
    # Math: |wit| = c + k1 ∧ c + start1[a] ≥ 0
    # Why: the witness of q is wit[c + q]; the next one is k1's.
    Requires(len(ToSeq(wit)) == c + k1 and 0 <= c + ToSeq(start1)[a])
    # Math: left_done(k1)
    # Why: completeness so far: the moves by the G1 transitions before k1.
    Requires(left_done(ToSeq(start1), ToSeq(evt1), ToSeq(mode), ToSeq(start2), ToSeq(evt2),
                       ToSeq(inv2), mp2, ToSeq(wit), ToSeq(own), ToSeq(src1), ToSeq(src2),
                       h, a, b, c, k1))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start1), 1 / 2) and Acc(list_pred(evt1), 1 / 2)
            and Acc(list_pred(dst1), 1 / 2) and Acc(list_pred(start2), 1 / 2)
            and Acc(list_pred(evt2), 1 / 2) and Acc(list_pred(dst2), 1 / 2)
            and Acc(list_pred(mode), 1 / 2) and Acc(list_pred(inv2), 1 / 2))
    Ensures(Acc(dict_pred(pos)) and Acc(list_pred(p1)) and Acc(list_pred(p2)))
    Ensures(Acc(list_pred(evt)) and Acc(list_pred(dst)) and Acc(list_pred(own))
            and Acc(list_pred(src1)) and Acc(list_pred(src2)) and Acc(list_pred(wit)))
    # Math: the inputs are unchanged
    # Why: the caller passes on facts about them.
    Ensures(ToSeq(start1) == Old(ToSeq(start1)) and ToSeq(evt1) == Old(ToSeq(evt1))
            and ToSeq(dst1) == Old(ToSeq(dst1)) and ToSeq(start2) == Old(ToSeq(start2))
            and ToSeq(evt2) == Old(ToSeq(evt2)) and ToSeq(dst2) == Old(ToSeq(dst2))
            and ToSeq(mode) == Old(ToSeq(mode)) and ToSeq(inv2) == Old(ToSeq(inv2)))
    # Math: r ∈ {-1, 0, 1} ∧ (r = 1 → dt)
    # Why: the flag after the walk, or -1 no room.
    Ensures(Result() >= -1 and Result() <= 1 and Implies(Result() == 1, dt))
    # Math: L_old ⊑ L for p1, p2, own, src1, src2, wit ∧ |p2| = |p1| ≤ cap ∧ φ(h) = (a, b)
    # Why: only appends; the current state's pair.
    Ensures(ext(Old(ToSeq(p1)), ToSeq(p1)) and ext(Old(ToSeq(p2)), ToSeq(p2))
            and ext(Old(ToSeq(own)), ToSeq(own)) and ext(Old(ToSeq(src1)), ToSeq(src1))
            and ext(Old(ToSeq(src2)), ToSeq(src2)) and ext(Old(ToSeq(wit)), ToSeq(wit))
            and len(p1) <= cap and len(ToSeq(p2)) == len(ToSeq(p1)) and h < len(ToSeq(p1))
            and ToSeq(p1)[h] == a and ToSeq(p2)[h] == b)
    # Math: r ≥ 0 → walk_ok(h, top, r = 1) ∧ |own| = |src1| = |src2| = |evt|
    #       ∧ |wit| = c + start1[a+1]
    # Why: the invariant after (bound raised to top), and one witness per G1 transition.
    Ensures(Implies(Result() >= 0,
                    walk_ok(n1, n2, ToSeq(start1), ToSeq(evt1), ToSeq(dst1), ToSeq(start2),
                            ToSeq(evt2), ToSeq(dst2), mp2, ToSeq(mode), St, ToSeq(p1),
                            ToSeq(p2), ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1),
                            ToSeq(src2), h, top, Result() == 1)
                    and len(ToSeq(own)) == len(ToSeq(evt))
                    and len(ToSeq(src1)) == len(ToSeq(evt))
                    and len(ToSeq(src2)) == len(ToSeq(evt))
                    and len(ToSeq(wit)) == c + ToSeq(start1)[a + 1]))
    # Math: r ≥ 0 → left_done(start1[a+1])
    # Why: completeness for the whole block: every move of h by a G1 transition.
    Ensures(Implies(Result() >= 0,
                    left_done(ToSeq(start1), ToSeq(evt1), ToSeq(mode), ToSeq(start2),
                              ToSeq(evt2), ToSeq(inv2), mp2, ToSeq(wit), ToSeq(own),
                              ToSeq(src1), ToSeq(src2), h, a, b, c, ToSeq(start1)[a + 1])))
    if k1 == start1[a + 1]:
        # the block is done: raise the bound of cur_ok from last to top
        raise_last(n1, n2, ToSeq(start1), ToSeq(evt1), ToSeq(dst1), ToSeq(start2), ToSeq(evt2),
                   ToSeq(dst2), mp2, ToSeq(mode), St, ToSeq(p1), ToSeq(p2), ToSeq(evt),
                   ToSeq(dst), ToSeq(own), ToSeq(src1), ToSeq(src2), h, last, top, dt)
        # Math: L ⊑ L for the six lists
        # Why (hint): nothing changed (ext of a list with itself).
        Assert(ext(ToSeq(p1), ToSeq(p1)) and ext(ToSeq(p2), ToSeq(p2))
               and ext(ToSeq(own), ToSeq(own)) and ext(ToSeq(src1), ToSeq(src1))
               and ext(ToSeq(src2), ToSeq(src2)) and ext(ToSeq(wit), ToSeq(wit)))
        if dt:
            return 1
        return 0
    r = left_next(n1, n2, cap, start1, evt1, dst1, start2, evt2, dst2, mp2, mode, inv2, St,
                  pos, p1, p2, evt, dst, own, src1, src2, wit, h, a, b, c, k1, top, last,
                  dt)                # the moves by k1
    if r < 0:
        return -1                    # no room (never with a working dict)
    # Math: k1 + 1 < start1[a+1] → evt1[k1] ≤ evt1[k1+1]
    # Why (hint): the block is sorted, so the next event is not smaller (the order fact for
    #      the recursive call).
    Assert(Implies(k1 + 1 < ToSeq(start1)[a + 1], ToSeq(evt1)[k1] <= ToSeq(evt1)[k1 + 1]))
    P11 = ToSeq(p1)                  # snapshots after left_next (proof only)
    P21 = ToSeq(p2)
    O1 = ToSeq(own)
    A1 = ToSeq(src1)
    B1 = ToSeq(src2)
    W1 = ToSeq(wit)
    r = walk_left(n1, n2, cap, start1, evt1, dst1, start2, evt2, dst2, mp2, mode, inv2, St,
                  pos, p1, p2, evt, dst, own, src1, src2, wit, h, a, b, c, k1 + 1, top,
                  ToSeq(evt1)[k1], r == 1)   # the rest of the block
    # Math: L_old ⊑ L for the six lists
    # Why: chain the two calls' "only appends".
    ext_trans(Old(ToSeq(p1)), P11, ToSeq(p1))
    ext_trans(Old(ToSeq(p2)), P21, ToSeq(p2))
    ext_trans(Old(ToSeq(own)), O1, ToSeq(own))
    ext_trans(Old(ToSeq(src1)), A1, ToSeq(src1))
    ext_trans(Old(ToSeq(src2)), B1, ToSeq(src2))
    ext_trans(Old(ToSeq(wit)), W1, ToSeq(wit))
    return r
