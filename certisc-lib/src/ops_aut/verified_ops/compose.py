"""
Verified composition of two encoded automata: parallel and product (certisc-proof/spec/parallel.md).

STATUS: experiment (2026-10-29), step 1 of spec §3. Only the soundness invariant and the two
appends that must keep it (a new state, a new transition). This is the step that timed out on
2026-10-20; if it verifies quickly, the search is built on it.

Lean target: `IsComposition` (DESopsProof/Parallel.lean). This file proves the `step_sound`
field: every output transition is a move of the composition (`syncF mode`).

Encoding as in core_aut/verified_core/check.py. Input r (r = 1, 2): states 0 .. n_r-1; state x owns
the positions block_r(x) = [start_r[x], start_r[x+1]) of evt_r / dst_r; events in G_r's own
numbering. The output numbers its events 0 .. m-1; map_r[e_r] is the output number of G_r's event
e_r (built by trusted code from the event names, spec question 3).

Verify, from certisc-lib/ (Python >= 3.12, `verify` extra, Java):

    nagini src/ops_aut/verified_ops/compose.py

Math notation used in the comments:
    [a, b)        the integers a, a+1, ..., b-1
    |l|           the length of list (or sequence) l
    block_r(x)    [start_r[x], start_r[x+1]), the transitions of state x of G_r
    x --e-->_k y  in G_r: k ∈ block_r(x), map_r[evt_r[k]] = e and dst_r[k] = y
    mode[e]       0 both, 1 left (G1 alone), 2 right (G2 alone), 3 none (Lean: Mode)
    φ(i)          (p1[i], p2[i]), the pair of output state i (Lean: φ)
    l_old         the value of l when the method was called (Old(...))

How to read the contracts (all removed before the code runs; core_aut/trusted/_strip.py):
- Requires(P) / Ensures(P)   precondition (the caller makes P true) / postcondition.
- Assert(P)                  a proof step, checked by Nagini. "Why (hint)": a fact Nagini can
                             prove but would not find by itself.
- Acc(list_pred(l), q)       permission to use list l: q = 1 read and write; q < 1 read only.
                             (A permission, not a formula: no Math.)
- MustTerminate(t)           the method terminates; a method only calls methods with a smaller t.
- ToSeq(l)                   the contents of list l as a value (a sequence).
- PSeq[int]                  the type of such a value.
- Old(e)                     e when the method was called.
- Implies(a, b)              a → b.
- Forall(int, lambda i: (P, [[t]]))   ∀ i ∈ ℤ: P; used by Nagini for an i where the term t
                             appears (the trigger).
- @Pure                      a side-effect-free function, usable in contracts (a definition).
- Lemma                      a method that only proves a fact (its calls are removed before
                             running).

Map of the file:
- specification: step_in, move, sound_ok (what "every transition is good" means);
- lemmas: keep_sound_state, keep_sound_trans (the invariant survives each kind of append);
- add_pair, emit: the only methods that write.
"""

from typing import List

from nagini_contracts.contracts import *
from nagini_contracts.obligations import MustTerminate

# appended: "list o is o0 with y appended", one fact per append (shared with reach.py).
from ops_aut.verified_ops.reach import appended


# --- specification ---------------------------------------------------------------------------
# The inputs are passed as sequences (ToSeq of the lists): values, so they stay known unchanged
# while the output lists grow (the lesson of reach.py).


# step_in: one transition of an input automaton, in output event numbers.
# Used in: move (both inputs).
@Pure
def step_in(st: PSeq[int], ev: PSeq[int], ds: PSeq[int], mp: PSeq[int], x: int, e: int,
            k: int, y: int) -> bool:
    """Transition k of the input goes from x to y with the output event e."""
    # Math: x ∈ [0,|start|-1) ∧ k ∈ block(x) ∧ k ∈ [0,|dst|) ∧ k < |evt|
    #       ∧ evt[k] ∈ [0,|map|) ∧ map[evt[k]] = e ∧ dst[k] = y          (x --e-->_k y)
    # Why: the Lean `y ∈ f_r(x, e)` (by the encoding, wrapper.md §4), with the transition k as
    #      the witness. The bounds come first, so every read below them is valid.
    return (0 <= x and x + 1 < len(st) and st[x] <= k and k < st[x + 1]
            and 0 <= k and k < len(ds) and k < len(ev)
            and 0 <= ev[k] and ev[k] < len(mp) and mp[ev[k]] == e and ds[k] == y)


# move: one move of the composition, by mode (Lean: q ∈ syncF mode f1 f2 p e).
# Used in: sound_ok, and the precondition of emit.
@Pure
def move(st1: PSeq[int], ev1: PSeq[int], ds1: PSeq[int], mp1: PSeq[int],
         st2: PSeq[int], ev2: PSeq[int], ds2: PSeq[int], mp2: PSeq[int],
         m: int, x1: int, x2: int, e: int, y1: int, y2: int, k1: int, k2: int) -> bool:
    """(x1, x2) --e--> (y1, y2) is a move with mode m, using transitions k1 of G1 and k2 of G2
    (-1 for a side that stays)."""
    # Math: (m = 0 ∧ x1 --e-->_k1 y1 ∧ x2 --e-->_k2 y2)
    #     ∨ (m = 1 ∧ x1 --e-->_k1 y1 ∧ k2 = -1 ∧ y2 = x2)
    #     ∨ (m = 2 ∧ k1 = -1 ∧ y1 = x1 ∧ x2 --e-->_k2 y2)
    # Why: the three non-empty cases of syncF (Lean: mem_syncF_both, mem_syncF_left,
    #      mem_syncF_right); mode 3 (none) has no move (syncF_none).
    return ((m == 0 and step_in(st1, ev1, ds1, mp1, x1, e, k1, y1)
             and step_in(st2, ev2, ds2, mp2, x2, e, k2, y2))
            or (m == 1 and step_in(st1, ev1, ds1, mp1, x1, e, k1, y1)
                and k2 == -1 and y2 == x2)
            or (m == 2 and k1 == -1 and y1 == x1
                and step_in(st2, ev2, ds2, mp2, x2, e, k2, y2)))


# sound_ok: every output transition written so far is a move (Lean: step_sound).
# Used in: the invariants of the search; here, add_pair and emit keep it.
@Pure
def sound_ok(st1: PSeq[int], ev1: PSeq[int], ds1: PSeq[int], mp1: PSeq[int],
             st2: PSeq[int], ev2: PSeq[int], ds2: PSeq[int], mp2: PSeq[int], md: PSeq[int],
             P1: PSeq[int], P2: PSeq[int], Ev: PSeq[int], Ds: PSeq[int], Ow: PSeq[int],
             S1: PSeq[int], S2: PSeq[int]) -> bool:
    """Each output transition k (from own[k] to dst[k], event evt[k]) is a move between the pairs
    of its two states, with the input transitions src1[k], src2[k]."""
    # Math: |p2| = |p1| ∧ |dst| = |own| = |src1| = |src2| = |evt|
    # Why: so every read below is of an existing entry.
    # Math: ∀ k ∈ [0,|evt|): own[k], dst[k] ∈ [0,|p1|) ∧ evt[k] ∈ [0,|mode|)
    #       ∧ move(mode[evt[k]], φ(own[k]), evt[k], φ(dst[k]), src1[k], src2[k])
    # Why: Lean `step_sound`: y ∈ f_H(i, e) → φ(y) ∈ syncF mode f1 f2 (φ(i)) e, with i = own[k],
    #      y = dst[k], e = evt[k]; the witnesses src1, src2 replace the "∃ transition".
    #      Trigger own[k]: read wherever a transition's source is used.
    return (len(P2) == len(P1) and len(Ds) == len(Ev) and len(Ow) == len(Ev)
            and len(S1) == len(Ev) and len(S2) == len(Ev)
            and Forall(int, lambda k: (Implies(
                0 <= k and k < len(Ev),
                0 <= Ow[k] and Ow[k] < len(P1) and 0 <= Ds[k] and Ds[k] < len(P1)
                and 0 <= Ev[k] and Ev[k] < len(md)
                and move(st1, ev1, ds1, mp1, st2, ev2, ds2, mp2, md[Ev[k]],
                         P1[Ow[k]], P2[Ow[k]], Ev[k], P1[Ds[k]], P2[Ds[k]], S1[k], S2[k])),
                [[Ow[k]]])))


# --- lemmas ----------------------------------------------------------------------------------


# keep_sound_state: sound_ok survives appending a new pair (y1, y2) to p1, p2.
# Used in: add_pair.
# Idea: every old transition reads p1, p2 only at states < |p1_old|, which keep their pairs.
def keep_sound_state(st1: PSeq[int], ev1: PSeq[int], ds1: PSeq[int], mp1: PSeq[int],
                     st2: PSeq[int], ev2: PSeq[int], ds2: PSeq[int], mp2: PSeq[int],
                     md: PSeq[int], P10: PSeq[int], P20: PSeq[int], P1: PSeq[int],
                     P2: PSeq[int], Ev: PSeq[int], Ds: PSeq[int], Ow: PSeq[int],
                     S1: PSeq[int], S2: PSeq[int], y1: int, y2: int) -> None:
    """Lemma: a new state does not change the moves of the existing transitions."""
    # Math: termination measure 1.
    # Why: no loops and no calls.
    Requires(MustTerminate(1))
    # Math: sound_ok(p1_old, p2_old, ...)
    # Why: the invariant before.
    Requires(sound_ok(st1, ev1, ds1, mp1, st2, ev2, ds2, mp2, md, P10, P20, Ev, Ds, Ow, S1, S2))
    # Math: p1 = p1_old · [y1] ∧ p2 = p2_old · [y2]
    # Why: the update.
    Requires(appended(P10, P1, y1) and appended(P20, P2, y2))
    # Math: sound_ok(p1, p2, ...)
    # Why: the invariant after.
    Ensures(sound_ok(st1, ev1, ds1, mp1, st2, ev2, ds2, mp2, md, P1, P2, Ev, Ds, Ow, S1, S2))
    # Math: the body of sound_ok(p1, p2, ...).
    # Why (hint): for each k, own[k], dst[k] < |p1_old|, so p1[own[k]] = p1_old[own[k]] (and the
    #      same for dst[k], and for p2): the move is the old one. Trigger own[k], as in sound_ok.
    Assert(Forall(int, lambda k: (Implies(
        0 <= k and k < len(Ev),
        0 <= Ow[k] and Ow[k] < len(P1) and 0 <= Ds[k] and Ds[k] < len(P1)
        and 0 <= Ev[k] and Ev[k] < len(md)
        and move(st1, ev1, ds1, mp1, st2, ev2, ds2, mp2, md[Ev[k]],
                 P1[Ow[k]], P2[Ow[k]], Ev[k], P1[Ds[k]], P2[Ds[k]], S1[k], S2[k])),
        [[Ow[k]]])))


# keep_sound_trans: sound_ok survives appending one transition that is a move.
# Used in: emit.
def keep_sound_trans(st1: PSeq[int], ev1: PSeq[int], ds1: PSeq[int], mp1: PSeq[int],
                     st2: PSeq[int], ev2: PSeq[int], ds2: PSeq[int], mp2: PSeq[int],
                     md: PSeq[int], P1: PSeq[int], P2: PSeq[int],
                     Ev0: PSeq[int], Ds0: PSeq[int], Ow0: PSeq[int], S10: PSeq[int],
                     S20: PSeq[int], Ev: PSeq[int], Ds: PSeq[int], Ow: PSeq[int],
                     S1: PSeq[int], S2: PSeq[int], i: int, e: int, j: int, k1: int,
                     k2: int) -> None:
    """Lemma: the old transitions are unchanged, and the new one (i --e--> j) is a move."""
    # Math: termination measure 1.
    # Why: no loops and no calls.
    Requires(MustTerminate(1))
    # Math: sound_ok(evt_old, dst_old, own_old, src1_old, src2_old)
    # Why: the invariant before.
    Requires(sound_ok(st1, ev1, ds1, mp1, st2, ev2, ds2, mp2, md, P1, P2,
                      Ev0, Ds0, Ow0, S10, S20))
    # Math: evt = evt_old · [e] ∧ dst = dst_old · [j] ∧ own = own_old · [i]
    #       ∧ src1 = src1_old · [k1] ∧ src2 = src2_old · [k2]
    # Why: the update: one entry added to each of the five lists.
    Requires(appended(Ev0, Ev, e) and appended(Ds0, Ds, j) and appended(Ow0, Ow, i)
             and appended(S10, S1, k1) and appended(S20, S2, k2))
    # Math: i, j ∈ [0,|p1|) ∧ e ∈ [0,|mode|) ∧ move(mode[e], φ(i), e, φ(j), k1, k2)
    # Why: the new transition is a move.
    Requires(0 <= i and i < len(P1) and 0 <= j and j < len(P1) and 0 <= e and e < len(md))
    Requires(move(st1, ev1, ds1, mp1, st2, ev2, ds2, mp2, md[e], P1[i], P2[i], e, P1[j], P2[j],
                  k1, k2))
    # Math: sound_ok(evt, dst, own, src1, src2)
    # Why: the invariant after.
    Ensures(sound_ok(st1, ev1, ds1, mp1, st2, ev2, ds2, mp2, md, P1, P2, Ev, Ds, Ow, S1, S2))
    # Math: own[|evt_old|] = i ∧ evt[|evt_old|] = e ∧ dst[|evt_old|] = j
    #       ∧ src1[|evt_old|] = k1 ∧ src2[|evt_old|] = k2
    # Why (hint): the new entry, read at its position (so the quantifier below meets it).
    Assert(Ow[len(Ev0)] == i and Ev[len(Ev0)] == e and Ds[len(Ev0)] == j
           and S1[len(Ev0)] == k1 and S2[len(Ev0)] == k2)
    # Math: the body of sound_ok(evt, dst, own, src1, src2).
    # Why (hint): old positions read the old entries (appended); the new position is the move
    #      above. Trigger own[k], as in sound_ok.
    Assert(Forall(int, lambda k: (Implies(
        0 <= k and k < len(Ev),
        0 <= Ow[k] and Ow[k] < len(P1) and 0 <= Ds[k] and Ds[k] < len(P1)
        and 0 <= Ev[k] and Ev[k] < len(md)
        and move(st1, ev1, ds1, mp1, st2, ev2, ds2, mp2, md[Ev[k]],
                 P1[Ow[k]], P2[Ow[k]], Ev[k], P1[Ds[k]], P2[Ds[k]], S1[k], S2[k])),
        [[Ow[k]]])))


# --- the writing methods ---------------------------------------------------------------------


# add_pair: a new output state with the pair (y1, y2).
# Called from: the search, when a target pair is new (experiment: not called yet).
def add_pair(st1: PSeq[int], ev1: PSeq[int], ds1: PSeq[int], mp1: PSeq[int],
             st2: PSeq[int], ev2: PSeq[int], ds2: PSeq[int], mp2: PSeq[int], md: PSeq[int],
             p1: List[int], p2: List[int], evt: List[int], dst: List[int], own: List[int],
             src1: List[int], src2: List[int], y1: int, y2: int) -> None:
    """Append the pair (y1, y2) as a new state; the transitions are unchanged."""
    # Why: write access to the labels; read access to the transition lists (1/4: the caller
    #      keeps a share, so they are known unchanged after the call).
    Requires(Acc(list_pred(p1)) and Acc(list_pred(p2)))
    Requires(Acc(list_pred(evt), 1 / 4) and Acc(list_pred(dst), 1 / 4)
             and Acc(list_pred(own), 1 / 4) and Acc(list_pred(src1), 1 / 4)
             and Acc(list_pred(src2), 1 / 4))
    # Math: termination measure 2.
    # Why: calls keep_sound_state (measure 1).
    Requires(MustTerminate(2))
    # Math: sound_ok
    # Why: the invariant before.
    Requires(sound_ok(st1, ev1, ds1, mp1, st2, ev2, ds2, mp2, md, ToSeq(p1), ToSeq(p2),
                      ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1), ToSeq(src2)))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(p1)) and Acc(list_pred(p2)))
    Ensures(Acc(list_pred(evt), 1 / 4) and Acc(list_pred(dst), 1 / 4)
            and Acc(list_pred(own), 1 / 4) and Acc(list_pred(src1), 1 / 4)
            and Acc(list_pred(src2), 1 / 4))
    # Math: p1 = p1_old · [y1] ∧ p2 = p2_old · [y2]
    # Why: the caller learns the new state's pair and that the old pairs are kept.
    Ensures(appended(Old(ToSeq(p1)), ToSeq(p1), y1) and appended(Old(ToSeq(p2)), ToSeq(p2), y2))
    # Math: sound_ok
    # Why: the invariant after (from keep_sound_state).
    Ensures(sound_ok(st1, ev1, ds1, mp1, st2, ev2, ds2, mp2, md, ToSeq(p1), ToSeq(p2),
                     ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1), ToSeq(src2)))
    p1.append(y1)                    # the new state's G1 state ...
    p2.append(y2)                    # ... and G2 state
    # Math: p1 = p1_old · [y1] ∧ p2 = p2_old · [y2]
    # Why (hint): the two appends, as one fact each (the lemma uses them).
    Assert(appended(Old(ToSeq(p1)), ToSeq(p1), y1) and appended(Old(ToSeq(p2)), ToSeq(p2), y2))
    # Math: sound_ok with the new p1, p2
    # Why: the old transitions are still moves.
    keep_sound_state(st1, ev1, ds1, mp1, st2, ev2, ds2, mp2, md, Old(ToSeq(p1)), Old(ToSeq(p2)),
                     ToSeq(p1), ToSeq(p2), ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1),
                     ToSeq(src2), y1, y2)


# emit: a new output transition i --e--> j that is a move, with its witnesses k1, k2.
# Called from: the search, for each move of the state being processed (experiment: not called).
def emit(st1: PSeq[int], ev1: PSeq[int], ds1: PSeq[int], mp1: PSeq[int],
         st2: PSeq[int], ev2: PSeq[int], ds2: PSeq[int], mp2: PSeq[int], md: PSeq[int],
         p1: List[int], p2: List[int], evt: List[int], dst: List[int], own: List[int],
         src1: List[int], src2: List[int], i: int, e: int, j: int, k1: int, k2: int) -> None:
    """Append the transition i --e--> j (input transitions k1, k2) to the output."""
    # Why: read access to the labels (1/4: the caller keeps a share); write access to the
    #      transition lists.
    Requires(Acc(list_pred(p1), 1 / 4) and Acc(list_pred(p2), 1 / 4))
    Requires(Acc(list_pred(evt)) and Acc(list_pred(dst)) and Acc(list_pred(own))
             and Acc(list_pred(src1)) and Acc(list_pred(src2)))
    # Math: termination measure 2.
    # Why: calls keep_sound_trans (measure 1).
    Requires(MustTerminate(2))
    # Math: sound_ok
    # Why: the invariant before.
    Requires(sound_ok(st1, ev1, ds1, mp1, st2, ev2, ds2, mp2, md, ToSeq(p1), ToSeq(p2),
                      ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1), ToSeq(src2)))
    # Math: i, j ∈ [0,|p1|) ∧ e ∈ [0,|mode|) ∧ move(mode[e], φ(i), e, φ(j), k1, k2)
    # Why: the new transition is a move (the search establishes it from the input transitions).
    Requires(0 <= i and i < len(p1) and 0 <= j and j < len(p1) and 0 <= e and e < len(md))
    Requires(move(st1, ev1, ds1, mp1, st2, ev2, ds2, mp2, md[e], ToSeq(p1)[i], ToSeq(p2)[i], e,
                  ToSeq(p1)[j], ToSeq(p2)[j], k1, k2))
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(p1), 1 / 4) and Acc(list_pred(p2), 1 / 4))
    Ensures(Acc(list_pred(evt)) and Acc(list_pred(dst)) and Acc(list_pred(own))
            and Acc(list_pred(src1)) and Acc(list_pred(src2)))
    # Math: |evt| = |evt_old| + 1 = |own| ∧ own[|evt_old|] = i
    # Why: the caller learns where the new transition is, and whose it is (|own| first, so the
    #      read own[|evt_old|] is valid).
    Ensures(len(evt) == Old(len(evt)) + 1 and len(own) == len(evt)
            and ToSeq(own)[Old(len(evt))] == i)
    # Math: sound_ok
    # Why: the invariant after (from keep_sound_trans).
    Ensures(sound_ok(st1, ev1, ds1, mp1, st2, ev2, ds2, mp2, md, ToSeq(p1), ToSeq(p2),
                     ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1), ToSeq(src2)))
    evt.append(e)                    # the event ...
    dst.append(j)                    # ... the target state ...
    own.append(i)                    # ... the source state ...
    src1.append(k1)                  # ... and the input transitions used (-1: that side stays)
    src2.append(k2)
    # Math: each list is its old value with one entry appended
    # Why (hint): the five appends, as one fact each (the lemma uses them).
    Assert(appended(Old(ToSeq(evt)), ToSeq(evt), e) and appended(Old(ToSeq(dst)), ToSeq(dst), j)
           and appended(Old(ToSeq(own)), ToSeq(own), i)
           and appended(Old(ToSeq(src1)), ToSeq(src1), k1)
           and appended(Old(ToSeq(src2)), ToSeq(src2), k2))
    # Math: sound_ok with the new transition lists
    # Why: the old transitions are unchanged, and the new one is a move.
    keep_sound_trans(st1, ev1, ds1, mp1, st2, ev2, ds2, mp2, md, ToSeq(p1), ToSeq(p2),
                     Old(ToSeq(evt)), Old(ToSeq(dst)), Old(ToSeq(own)), Old(ToSeq(src1)),
                     Old(ToSeq(src2)), ToSeq(evt), ToSeq(dst), ToSeq(own), ToSeq(src1),
                     ToSeq(src2), i, e, j, k1, k2)
