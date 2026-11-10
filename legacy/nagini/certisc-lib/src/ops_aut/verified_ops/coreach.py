"""
Verified coreachability on an encoded automaton (certisc-proof/spec/coreach.md).

- coreachable  the states from which some target state (default: the marked states) can be
               reached (Lean: `coreach f Xm`), each once, with witnesses: each state has the
               next state on a shortest path to a target, and the transition taken.

How: the reverse index (core_aut/verified_core/reverse_index.py) encodes the reversed automaton
as (rstart, rsrc). A breadth-first search on it from the targets, the verified `reachable` of
reach.py, finds the coreachable states. This file runs that search and translates its results
back to the automaton itself, using the four facts the reverse-index checker proved. The search
proof is not repeated.

Verify, from certisc-lib/ (Python >= 3.12, `verify` extra, Java):

    nagini src/ops_aut/verified_ops/coreach.py

Math notation used in the comments:
    [a, b)       the integers a, a+1, ..., b-1
    |l|          the length of list (or sequence) l
    T            |dst|, the number of transitions
    block(x)     [start[x], start[x+1]), the transitions out of x
    rblock(y)    [rstart[y], rstart[y+1]), the reverse positions of the transitions into y
    x --_k--> y  transition k goes from x to y: k ∈ block(x) and dst[k] = y
    mk, o, p, v  mark, out, nxt, via, as sequences
    st, ds, rst, rk, rs, ps, Xq   ToSeq of start, dst, rstart, rk, rsrc, pos, Xm

How to read the contracts (all removed before the code runs; core_aut/trusted/_strip.py):
- Requires(P) / Ensures(P)   precondition (the caller makes P true) / postcondition.
- Assert(P)                  a proof step, checked by Nagini. "Why (hint)": a fact Nagini can
                             prove but would not find by itself.
- Acc(list_pred(l), q)       permission to use list l: q = 1 read and write; q < 1 read only.
                             A caller that passes only part of its share knows the list is
                             unchanged after the call. (A permission, not a formula: no Math.)
- MustTerminate(t)           the method terminates; t goes down; a method only calls methods
                             with a smaller t.
- ToSeq(l)                   the contents of list l as a value (a sequence).
- PSeq[int]                  the type of such a value.
- Implies(a, b)              a → b.
- Forall(int, lambda i: (P, [[t]]))   ∀ i ∈ ℤ: P; Nagini uses it for an i where the term t
                             appears (the trigger).
- @Pure                      a side-effect-free function, usable in contracts (a definition).
- Lemma                      a method that only proves a fact (no runtime effect; its calls are
                             removed before running).

Map of the file:
- specification: co_closed (backward closed), co_wit_ok (witnesses toward the targets);
- lemmas: co_closed_from, co_wit_from (the translation from the reversed search);
- coreachable: the operation.
"""

from typing import List

from nagini_contracts.contracts import *
from nagini_contracts.obligations import MustTerminate

# The block structure, from the verified validity checker; in_blk (shared with reach.py).
from core_aut.verified_core.check import blocks_ok
from core_aut.verified_core.blocks import in_blk
# The four facts proved by the reverse-index checker.
from core_aut.verified_core.reverse_index import own_ok, pos_ok, src_ok, tgt_ok
# The verified breadth-first search and its result predicates.
from ops_aut.verified_ops.reach import (closed_all, contains_S, marks_ok, reachable,
                                        targets_ok, wit_ok)


# --- specification ---------------------------------------------------------------------------
# Definitions used in the contracts. They say what "correct" means; they run no code.


# co_closed: the marked states are backward closed (completeness, part 2).
# Used in: the result of coreachable. With contains_S and lemma C1 (Lean,
# coreach_subset_of_closed) it gives "every coreachable state is in out".
@Pure
def co_closed(st: PSeq[int], ds: PSeq[int], mk: PSeq[int]) -> bool:
    """A transition into a marked state comes from a marked state."""
    # Math: ∀ k ∈ [0,T). ∀ x. k ∈ block(x) ∧ x < |mk| ∧ dst[k] ∈ [0,|mk|) ∧ mk[dst[k]] ≥ 0
    #                          → mk[x] ≥ 0
    # Why: "backward closed" of lemma C1, for R = the marked states. Triggers: ds[k] for the
    #      outer ∀; in_blk(st, x, k) for the inner (as in reach.closed_all).
    return Forall(int, lambda k: (Implies(
        0 <= k and k < len(ds),
        Forall(int, lambda x: (Implies(
            in_blk(st, x, k) and x < len(mk) and 0 <= ds[k] and ds[k] < len(mk)
            and mk[ds[k]] >= 0,
            mk[x] >= 0),
            [[in_blk(st, x, k)]]))),
        [[ds[k]]]))


# co_wit_ok: every entry of out has a witness (soundness: everything in out is coreachable).
# Used in: the result of coreachable. With lemma C2 (Lean, mem_coreach_of_witness) it gives
# "every entry of out is in coreach f Xm".
@Pure
def co_wit_ok(st: PSeq[int], ds: PSeq[int], Xq: PSeq[int], rk: PSeq[int], o: PSeq[int],
              p: PSeq[int], v: PSeq[int]) -> bool:
    """Each entry of out is a target, or has a transition to an earlier entry."""
    # Math: |p| = |o| ∧ |v| = |o|
    # Why: so p[i] and v[i] are valid reads for every entry i of o.
    Requires(len(p) == len(o) and len(v) == len(o))
    # Math: ∀ i ∈ [0,|o|): (p[i] = -1 → Xm[v[i]] = o[i])
    #                     ∧ (p[i] ≠ -1 → 0 ≤ p[i] < i ∧ o[i] --_{rk[v[i]]}--> o[p[i]])
    # Why: the witnesses of lemma C2: o[i] is a target, or its transition rk[v[i]] leads to the
    #      earlier entry o[p[i]] (the next state toward a target). Trigger v[i], as in
    #      reach.wit_ok (an o-trigger would chain along p: a matching loop).
    return Forall(int, lambda i: (Implies(
        0 <= i and i < len(o),
        Implies(p[i] == -1, 0 <= v[i] and v[i] < len(Xq) and Xq[v[i]] == o[i])
        and Implies(p[i] != -1,
                    0 <= p[i] and p[i] < i and 0 <= v[i] and v[i] < len(rk)
                    and in_blk(st, o[i], rk[v[i]])
                    and 0 <= rk[v[i]] and rk[v[i]] < len(ds) and ds[rk[v[i]]] == o[p[i]])),
        [[v[i]]]))


# --- lemmas ----------------------------------------------------------------------------------
# Methods with no runtime effect: each proves one fact.


# co_closed_from: the reversed search's "closed" is the automaton's "backward closed".
# Used in: coreachable, after the search.
# Idea: for a transition k from x into a marked y: j = pos[k] is in rblock(y) (pos_ok), and
# rsrc[j] = x (own_ok); the reversed search is closed at j (closed_all), so x is marked.
def co_closed_from(st: PSeq[int], ds: PSeq[int], rst: PSeq[int], rk: PSeq[int],
                   rs: PSeq[int], ps: PSeq[int], mk: PSeq[int]) -> None:
    """Lemma: closed_all on the reverse encoding gives co_closed on the automaton."""
    # Math: termination measure 1.
    # Why: no loops and no calls.
    Requires(MustTerminate(1))
    # Math: closed_all(rst, rs, mk)
    # Why: the reversed search's result: every reverse transition out of a marked state goes
    #      to a marked state.
    Requires(closed_all(rst, rs, mk))
    # Math: pos_ok(rst, ds, rk, ps) ∧ own_ok(st, rs, ps)
    # Why: the reverse-index facts that locate each transition k in the reverse encoding.
    Requires(pos_ok(rst, ds, rk, ps) and own_ok(st, rs, ps))
    # Math: |rs| = |ds|
    # Why: so pos[k] is a valid reverse position of rs.
    Requires(len(rs) == len(ds))
    # Math: co_closed(st, ds, mk)
    # Why: the fact proved.
    Ensures(co_closed(st, ds, mk))
    # Math: ∀ k ∈ [0,T). ∀ x. k ∈ block(x) ∧ x < |mk| ∧ dst[k] ∈ [0,|mk|) ∧ mk[dst[k]] ≥ 0
    #                          → pos[k] ∈ rblock(dst[k]) ∧ rsrc[pos[k]] = x ∧ mk[x] ≥ 0
    # Why (hint): the body of co_closed, with the steps written out: the term ps[k] triggers
    #      pos_ok and own_ok; in_blk(rst, ds[k], ps[k]) and rs[ps[k]] trigger closed_all.
    Assert(Forall(int, lambda k: (Implies(
        0 <= k and k < len(ds),
        Forall(int, lambda x: (Implies(
            in_blk(st, x, k) and x < len(mk) and 0 <= ds[k] and ds[k] < len(mk)
            and mk[ds[k]] >= 0,
            0 <= ps[k] and ps[k] < len(rs) and in_blk(rst, ds[k], ps[k])
            and rs[ps[k]] == x and mk[x] >= 0),
            [[in_blk(st, x, k)]]))),
        [[ds[k]]])))


# co_wit_from: the reversed search's witnesses are witnesses toward the targets.
# Used in: coreachable, after the search.
# Idea: a reverse witness says o[i] = rsrc[v[i]] with v[i] ∈ rblock(o[p[i]]). By src_ok,
# rk[v[i]] is a transition out of rsrc[v[i]] = o[i]; by tgt_ok, it goes into o[p[i]].
def co_wit_from(n: int, st: PSeq[int], ds: PSeq[int], Xq: PSeq[int], rst: PSeq[int],
                rk: PSeq[int], rs: PSeq[int], o: PSeq[int], p: PSeq[int],
                v: PSeq[int]) -> None:
    """Lemma: wit_ok on the reverse encoding gives co_wit_ok on the automaton."""
    # Math: termination measure 1.
    # Why: no loops and no calls.
    Requires(MustTerminate(1))
    # Math: |p| = |v| = |o| ∧ wit_ok(rst, rs, Xq, o, p, v)
    # Why: the reversed search's witnesses.
    Requires(len(p) == len(o) and len(v) == len(o) and wit_ok(rst, rs, Xq, o, p, v))
    # Math: src_ok(n, st, T, rk, rs) ∧ tgt_ok(rst, ds, rk)
    # Why: the reverse-index facts that turn a reverse position into a forward transition.
    Requires(src_ok(n, st, len(ds), rk, rs) and tgt_ok(rst, ds, rk))
    # Math: co_wit_ok(st, ds, Xq, rk, o, p, v)
    # Why: the fact proved.
    Ensures(co_wit_ok(st, ds, Xq, rk, o, p, v))
    # Math: ∀ i ∈ [0,|o|): p[i] ≠ -1 → v[i] ∈ rblock(o[p[i]]) ∧ rs[v[i]] = o[i]
    #                                   ∧ o[i] --_{rk[v[i]]}--> o[p[i]]
    # Why (hint): the body of co_wit_ok's second case, with the steps written out: rs[v[i]]
    #      triggers src_ok; rk[v[i]] and in_blk(rst, o[p[i]], v[i]) trigger tgt_ok.
    #      Trigger v[i], as in wit_ok.
    Assert(Forall(int, lambda i: (Implies(
        0 <= i and i < len(o) and p[i] != -1,
        0 <= p[i] and p[i] < i and 0 <= v[i] and v[i] < len(rs)
        and in_blk(rst, o[p[i]], v[i]) and rs[v[i]] == o[i]
        and 0 <= v[i] and v[i] < len(rk) and in_blk(st, o[i], rk[v[i]])
        and 0 <= rk[v[i]] and rk[v[i]] < len(ds) and ds[rk[v[i]]] == o[p[i]]),
        [[v[i]]])))


# --- the operation ---------------------------------------------------------------------------


# coreachable: the operation. The caller (ops_aut/basic_ops.py) passes the encoded automaton,
# its checked reverse index, the target states, a mark list of n entries all -1, and three
# empty lists to fill. It runs the verified breadth-first search on the reverse encoding, then
# translates the result. The result is the certificate of the Lean theorem
# coreach_eq_of_certificate: contains Xm, backward closed, witnesses.
def coreachable(n: int, start: List[int], dst: List[int], rstart: List[int], rk: List[int],
                rsrc: List[int], pos: List[int], Xm: List[int], mark: List[int],
                out: List[int], nxt: List[int], via: List[int]) -> None:
    """The states from which a state of Xm can be reached, breadth-first from Xm.

    On return: out lists them, each once; mark[x] is the position of x in out, or -1 (not
    coreachable). Witnesses: if nxt[i] = -1, out[i] = Xm[via[i]] (a target); otherwise the
    transition rk[via[i]] goes from out[i] to out[nxt[i]] (with nxt[i] < i): the next state on
    a shortest path to a target.

    Proved (spec: certisc-proof/spec/coreach.md): in range and no duplicates; contains Xm;
    backward closed; witnesses. With the Lean theorem coreach_eq_of_certificate: the entries of
    out are exactly coreach f Xm."""
    # Why: read access to the automaton (1/2).
    Requires(Acc(list_pred(start), 1 / 2) and Acc(list_pred(dst), 1 / 2))
    # Why: read access to the reverse index and the targets. 3/4: the search takes 1/2 of
    #      rstart, rsrc, Xm; the 1/4 kept here means they are known unchanged after it.
    Requires(Acc(list_pred(rstart), 3 / 4) and Acc(list_pred(rk), 1 / 2)
             and Acc(list_pred(rsrc), 3 / 4) and Acc(list_pred(pos), 1 / 2)
             and Acc(list_pred(Xm), 3 / 4))
    # Why: write access to mark and the three outputs.
    Requires(Acc(list_pred(mark)) and Acc(list_pred(out)) and Acc(list_pred(nxt))
             and Acc(list_pred(via)))
    # Math: termination measure n + 7 (calls reachable, measure n + 6).
    # Why: the operation always terminates.
    Requires(MustTerminate(n + 7))
    # Math: blocks_ok(n, start, T) ∧ targets_ok(n, dst)
    # Why: a validated automaton.
    Requires(blocks_ok(n, start, len(dst)) and targets_ok(n, dst))
    # Math: blocks_ok(n, rstart, |rsrc|) ∧ |rk| = |rsrc| = |pos| = T
    # Why: from check_reverse: the reverse encoding has valid blocks.
    Requires(blocks_ok(n, rstart, len(rsrc)) and len(rk) == len(dst) and len(rsrc) == len(dst)
             and len(pos) == len(dst))
    # Math: src_ok ∧ tgt_ok ∧ pos_ok ∧ own_ok
    # Why: from check_reverse: the reverse index is correct.
    Requires(src_ok(n, ToSeq(start), len(dst), ToSeq(rk), ToSeq(rsrc))
             and tgt_ok(ToSeq(rstart), ToSeq(dst), ToSeq(rk))
             and pos_ok(ToSeq(rstart), ToSeq(dst), ToSeq(rk), ToSeq(pos))
             and own_ok(ToSeq(start), ToSeq(rsrc), ToSeq(pos)))
    # Math: ∀ j ∈ [0,|Xm|): Xm[j] ∈ [0,n)
    # Why: "targets in range". Repeats are allowed. Trigger Xm[j]: reachable reads it.
    Requires(Forall(int, lambda j: (Implies(0 <= j and j < len(Xm), 0 <= Xm[j] and Xm[j] < n),
                                    [[Xm[j]]])))
    # Math: |mark| = n ∧ ∀ y ∈ [0,n): mark[y] = -1
    # Why: nothing is reached yet (as reachable requires). Trigger mark[y].
    Requires(len(mark) == n)
    Requires(Forall(int, lambda y: (Implies(0 <= y and y < len(mark), ToSeq(mark)[y] == -1),
                                    [[ToSeq(mark)[y]]])))
    # Math: |out| = |nxt| = |via| = 0
    # Why: the outputs start empty.
    Requires(len(out) == 0 and len(nxt) == 0 and len(via) == 0)
    # Why: gives the permissions back.
    Ensures(Acc(list_pred(start), 1 / 2) and Acc(list_pred(dst), 1 / 2))
    Ensures(Acc(list_pred(rstart), 3 / 4) and Acc(list_pred(rk), 1 / 2)
            and Acc(list_pred(rsrc), 3 / 4) and Acc(list_pred(pos), 1 / 2)
            and Acc(list_pred(Xm), 3 / 4))
    Ensures(Acc(list_pred(mark)) and Acc(list_pred(out)) and Acc(list_pred(nxt))
            and Acc(list_pred(via)))
    # Math: |mark| = n ∧ |nxt| = |via| = |out| ≤ n
    # Why: the sizes; one witness per entry.
    Ensures(len(mark) == n and len(nxt) == len(out) and len(via) == len(out)
            and len(out) <= n)
    # THE RESULT.
    # Math: ∀ i: out[i] ∈ [0,n) ∧ mark[out[i]] = i;  ∀ y: mark[y] ≠ -1 → out[mark[y]] = y
    # Why: in range, no duplicates, and "marked" = "in out".
    Ensures(marks_ok(ToSeq(mark), ToSeq(out)))
    # Math: ∀ j ∈ [0,|Xm|): mark[Xm[j]] ≥ 0                                  (contains Xm)
    # Why: hypothesis "Xm ⊆ R" of lemma C1.
    Ensures(contains_S(ToSeq(Xm), ToSeq(mark), len(Xm)))
    # Math: ∀ x, k ∈ block(x): mark[dst[k]] ≥ 0 → mark[x] ≥ 0               (backward closed)
    # Why: hypothesis "R backward closed" of lemma C1; with contains Xm: coreach f Xm ⊆ out.
    Ensures(co_closed(ToSeq(start), ToSeq(dst), ToSeq(mark)))
    # Math: ∀ i: out[i] = Xm[via[i]] (nxt[i] = -1) ∨ out[i] --_{rk[via[i]]}--> out[nxt[i]],
    #       nxt[i] < i
    # Why: hypothesis of lemma C2: out ⊆ coreach f Xm.
    Ensures(co_wit_ok(ToSeq(start), ToSeq(dst), ToSeq(Xm), ToSeq(rk), ToSeq(out), ToSeq(nxt),
                      ToSeq(via)))
    # Math: targets_ok(n, rsrc): ∀ j ∈ [0,T): rsrc[j] ∈ [0,n)
    # Why (hint): from src_ok; the search needs it (rsrc is the reversed automaton's "dst").
    Assert(Forall(int, lambda j: (Implies(0 <= j and j < len(rsrc),
                                          ToSeq(rsrc)[j] == rsrc[j]
                                          and 0 <= rsrc[j] and rsrc[j] < n),
                                  [[rsrc[j]]])))
    Assert(targets_ok(n, rsrc))
    # Math: out = breadth-first search on the reverse encoding (rstart, rsrc) from Xm
    # Why: "reachable backward from Xm" is coreachable; reach.py proves the search.
    reachable(n, rstart, rsrc, Xm, mark, out, nxt, via)
    # Math: co_closed(st, ds, mk)
    # Why: the reversed "closed" is the automaton's "backward closed".
    co_closed_from(ToSeq(start), ToSeq(dst), ToSeq(rstart), ToSeq(rk), ToSeq(rsrc), ToSeq(pos),
                   ToSeq(mark))
    # Math: co_wit_ok(st, ds, Xq, rk, o, p, v)
    # Why: the reversed witnesses are witnesses toward the targets.
    co_wit_from(n, ToSeq(start), ToSeq(dst), ToSeq(Xm), ToSeq(rstart), ToSeq(rk), ToSeq(rsrc),
                ToSeq(out), ToSeq(nxt), ToSeq(via))
