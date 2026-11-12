//! The completion of a specification `H` (spec: certisc-proof/spec/supervisor.md §2, step 1;
//! the refinement form, Lean `supcon_strict_sub` / `supervisor_L`).
//!
//! `Hc` = `H` plus one **dump** state `d = n_H`:
//! - for a state `x` of `H` and an event `e` of `E_H`: `H`'s own `e`-moves, or `x --e--> d` if
//!   `H` has none;
//! - for an *extra* event (numbers `m_H .. m-1`: the plant's events that `H` does not mention):
//!   a self-loop `x --e--> x` (they are not constrained by `H`, spec Q1 (b));
//! - `d` loops on every event of `Hc`.
//!
//! So every state of `Hc` has every event of `E_Hc`: `G × Hc` keeps all of `G`'s moves
//! (`L(G × Hc) = L(G)`), and the pairs whose `Hc` state is not `d` are exactly `G ‖ H`.
//!
//! Glossary (in addition to `aut.rs`, `supcon.rs`):
//! - `comp(h, m, x, e, y)`: `y ∈ f_Hc(x, e)` (the completion relation, defined from `h`).
//! - `block_done(...)`: positions `[lo, hi)` of the output lists are a finished block of state
//!   `x`: each one is a move of `Hc` (sound), sorted by event, and every move of `Hc` from `x`
//!   is among them (complete).
//! - `&mut v` parameters: `old(v)` is the value at the call, `final(v)` at the return.

use crate::core_aut::aut::*;
// Why: `en` is used only by proofs (erased in a plain build).
#[allow(unused_imports)]
use crate::sup::supcon::*;
use vstd::prelude::*;

verus! {

/// `y ∈ f_Hc(x, e)`: the moves of the completion of `h` with `m` event numbers (`m_H .. m-1`
/// are the extra events) and the dump state `d = n_H`.
pub open spec fn comp(h: &Aut, m: int, x: int, e: int, y: int) -> bool {
    // Math: d = n_H
    let d = h.n as int;
    // Math: x ∈ X_H, e ∈ E_H: y ∈ f_H(x, e), or y = d when f_H(x, e) = ∅
    ||| (0 <= x < h.n && h@.E.contains(e) && (h@.f(x, e, y) || (y == d && !en(h@, x, e))))
    // Math: x ∈ X_H, e extra: y = x (self-loop)
    ||| (0 <= x < h.n && h.m <= e < m && y == x)
    // Math: x = d: y = d for every event of Hc
    ||| (x == d && y == d && (h@.E.contains(e) || (h.m <= e < m)))
}

/// Every move of `Hc` from `x` on an event below `eb` is at some position of `[lo, hi)`.
pub open spec fn complete_upto(h: &Aut, m: int, evt2: Seq<usize>, dst2: Seq<usize>, x: int, lo: int, hi: int, eb: int) -> bool {
    // Math: ∀ e < eb, y: comp(x, e, y) → ∃ kp ∈ [lo, hi): evt2[kp] = e ∧ dst2[kp] = y
    forall|e: int, y: int| e < eb && #[trigger] comp(h, m, x, e, y)
        ==> exists|kp: int| lo <= kp < hi && #[trigger] evt2[kp] as int == e && dst2[kp] as int == y
}

/// Positions `[lo, hi)` are a finished block of state `x` of `Hc`.
pub open spec fn block_done(h: &Aut, m: int, evt2: Seq<usize>, dst2: Seq<usize>, x: int, lo: int, hi: int) -> bool {
    // Math: lo ≤ hi ≤ |evt2| = |dst2|
    &&& 0 <= lo <= hi <= evt2.len()
    &&& dst2.len() == evt2.len()
    // Math: sound: ∀ kp ∈ [lo, hi): comp(x, evt2[kp], dst2[kp])
    &&& forall|kp: int| lo <= kp < hi ==> #[trigger] comp(h, m, x, evt2[kp] as int, dst2[kp] as int)
    // Math: sorted: ∀ a ≤ b in [lo, hi): evt2[a] ≤ evt2[b]
    &&& forall|a: int, b: int| lo <= a <= b < hi ==> #[trigger] evt2[a] <= #[trigger] evt2[b]
    // Math: complete (every event of Hc is below m)
    &&& complete_upto(h, m, evt2, dst2, x, lo, hi, m)
}

/// Appending to the lists keeps a finished block finished (its positions are unchanged).
pub proof fn lemma_extend(h: &Aut, m: int, s: Seq<usize>, s2: Seq<usize>, t: Seq<usize>, t2: Seq<usize>, x: int, lo: int, hi: int)
    requires
        // Math: block_done in (s, s2); (t, t2) extends (s, s2)
        block_done(h, m, s, s2, x, lo, hi),
        s.len() <= t.len(),
        t2.len() == t.len(),
        forall|j: int| 0 <= j < s.len() ==> #[trigger] t[j] == s[j],
        forall|j: int| 0 <= j < s.len() ==> #[trigger] t2[j] == s2[j],
    ensures
        block_done(h, m, t, t2, x, lo, hi),
{
    // Math: sound: t[kp] = s[kp], t2[kp] = s2[kp] for kp < hi ≤ |s|
    assert forall|kp: int| lo <= kp < hi implies #[trigger] comp(h, m, x, t[kp] as int, t2[kp] as int) by {
        assert(t[kp] == s[kp] && t2[kp] == s2[kp]);
        assert(comp(h, m, x, s[kp] as int, s2[kp] as int));
    }
    // Math: sorted: the same entries
    assert forall|a: int, b: int| lo <= a <= b < hi implies #[trigger] t[a] <= #[trigger] t[b] by {
        assert(t[a] == s[a] && t[b] == s[b]);
    }
    // Math: complete: the same witness position
    assert forall|e: int, y: int| e < m && #[trigger] comp(h, m, x, e, y)
        implies exists|kp: int| lo <= kp < hi && #[trigger] t[kp] as int == e && t2[kp] as int == y by {
        let kp = choose|kp: int| lo <= kp < hi && #[trigger] s[kp] as int == e && s2[kp] as int == y;
        assert(t[kp] == s[kp] && t2[kp] == s2[kp]);
    }
}

/// Appends the block of state `x < n_H` of `Hc` (events walked in increasing order).
// Why: some variables are used only in proofs (unused once they are erased).
#[allow(unused_variables)]
fn build_block(h: &Aut, m: usize, x: usize, evt2: &mut Vec<usize>, dst2: &mut Vec<usize>)
    requires
        // Math: wf(H), x ∈ X_H, m_H ≤ m; |evt2| = |dst2|
        h.wf(),
        x < h.n,
        h.m <= m,
        old(evt2)@.len() == old(dst2)@.len(),
    ensures
        // Math: the old entries are kept; [|old|, |final|) is the finished block of x
        final(evt2)@.len() == final(dst2)@.len(),
        old(evt2)@.len() <= final(evt2)@.len(),
        forall|j: int| 0 <= j < old(evt2)@.len() ==> #[trigger] final(evt2)@[j] == old(evt2)@[j],
        forall|j: int| 0 <= j < old(evt2)@.len() ==> #[trigger] final(dst2)@[j] == old(dst2)@[j],
        block_done(h, m as int, final(evt2)@, final(dst2)@, x as int, old(evt2)@.len() as int, final(evt2)@.len() as int),
{
    // Why: ghost copies of the lists at the call (the prefix to keep).
    let ghost e0 = evt2@;
    let ghost d0 = dst2@;
    // Math: b0 = |evt2|, the start of the block
    let b0 = evt2.len();
    // Math: d = n_H, the dump state
    let d = h.n;
    // Math: [lo, hi) = x's block in H
    let lo = h.start[x];
    let hi = h.start[x + 1];
    // Math: start_H[x] ≤ start_H[x+1] ≤ T_H; blk_sorted(x)
    assert(h.start@[x as int] <= h.start@[x + 1] <= h.start@[h.n as int]);
    assert(h.blk_sorted(x as int));
    // Math: k = lo (k walks x's block in H); e = 0 (e walks the events of Hc)
    let mut k = lo;
    let mut e: usize = 0;
    while e < m
        invariant
            // Why: facts restated in each loop (a loop only knows its invariant).
            h.wf(),
            x < h.n,
            d == h.n,
            h.m <= m,
            h.blk_sorted(x as int),
            lo == h.start@[x as int],
            hi == h.start@[x + 1],
            hi <= h.evt@.len(),
            lo <= k <= hi,
            e <= m,
            // Math: the prefix is kept
            b0 == e0.len(),
            b0 <= evt2@.len(),
            dst2@.len() == evt2@.len(),
            forall|j: int| 0 <= j < b0 ==> #[trigger] evt2@[j] == e0[j],
            forall|j: int| 0 <= j < b0 ==> #[trigger] dst2@[j] == d0[j],
            // Math: H's positions before k have events < e; from k on, ≥ e
            forall|q: int| lo <= q < k ==> #[trigger] h.evt@[q] < e,
            forall|q: int| k <= q < hi ==> #[trigger] h.evt@[q] >= e,
            // Math: the block so far: sound, sorted, below e, complete for events < e
            forall|kp: int| b0 <= kp < evt2@.len() ==> #[trigger] comp(h, m as int, x as int, evt2@[kp] as int, dst2@[kp] as int),
            forall|a: int, b: int| b0 <= a <= b < evt2@.len() ==> #[trigger] evt2@[a] <= #[trigger] evt2@[b],
            forall|kp: int| b0 <= kp < evt2@.len() ==> #[trigger] evt2@[kp] < e,
            complete_upto(h, m as int, evt2@, dst2@, x as int, b0 as int, evt2@.len() as int, e as int),
        // Math: m - e decreases
        decreases m - e,
    {
        // Why: ghost copies of the lists before this event.
        let ghost ev1 = evt2@;
        let ghost ds1 = dst2@;
        // Math: b1 = |evt2|, where the entries for e start
        let b1 = evt2.len();
        if e < h.m {
            if h.in_e[e] {
                // Math: e ∈ E_H: copy H's e-moves (positions [k0, k) of x's block)
                let k0 = k;
                while k < hi && h.evt[k] == e
                    invariant
                        // Why: facts restated in each loop (a loop only knows its invariant).
                        h.wf(),
                        x < h.n,
                        h.m <= m,
                        e < h.m,
                        h.in_e@[e as int],
                        h.blk_sorted(x as int),
                        lo == h.start@[x as int],
                        hi == h.start@[x + 1],
                        hi <= h.evt@.len(),
                        lo <= k0 <= k <= hi,
                        // Math: [k0, k) carry e; the lists grew by k - k0 copies
                        forall|q: int| k0 <= q < k ==> #[trigger] h.evt@[q] == e,
                        forall|q: int| lo <= q < k0 ==> #[trigger] h.evt@[q] < e,
                        forall|q: int| k0 <= q < hi ==> #[trigger] h.evt@[q] >= e,
                        evt2@.len() == b1 + (k - k0),
                        dst2@.len() == evt2@.len(),
                        b1 == ev1.len(),
                        forall|j: int| 0 <= j < b1 ==> #[trigger] evt2@[j] == ev1[j],
                        forall|j: int| 0 <= j < b1 ==> #[trigger] dst2@[j] == ds1[j],
                        forall|j: int| b1 <= j < evt2@.len() ==> #[trigger] evt2@[j] == e && dst2@[j] == h.dst@[k0 + (j - b1)],
                    // Math: hi - k decreases
                    decreases hi - k,
                {
                    // Math: evt2 := evt2 · [e]; dst2 := dst2 · [dst_H[k]]
                    evt2.push(e);
                    dst2.push(h.dst[k]);
                    // Math: k := k + 1
                    k += 1;
                }
                // Math: from k on, events > e (k = hi, or evt_H[k] ≠ e and sorted)
                assert forall|q: int| k <= q < hi implies #[trigger] h.evt@[q] >= e + 1 by {
                    assert(h.evt@[k as int] <= h.evt@[q]);
                }
                if k == k0 {
                    // Math: no e-move in H: f_H(x, e) = ∅
                    assert(!en(h@, x as int, e as int)) by {
                        if en(h@, x as int, e as int) {
                            let y = choose|y: int| #[trigger] h@.f(x as int, e as int, y);
                            let q = choose|q: int| #[trigger] h.in_blk(x as int, q) && h.evt@[q] as int == e && h.dst@[q] as int == y;
                            // Math: q ∈ [k0, hi) has evt ≥ e+1, and q < k0 has evt < e
                            assert(lo <= q < hi);
                        }
                    }
                    // Math: evt2 := evt2 · [e]; dst2 := dst2 · [d] (the move to the dump state)
                    evt2.push(e);
                    dst2.push(d);
                }
                proof {
                    // Math: the new entries are moves of Hc
                    assert forall|j: int| b1 <= j < evt2@.len() implies #[trigger] comp(h, m as int, x as int, evt2@[j] as int, dst2@[j] as int) by {
                        if k > k0 {
                            // Math: a copy of position q = k0 + (j - b1): x --e--> dst_H[q]
                            let q = k0 + (j - b1);
                            assert(h.in_blk(x as int, q));
                            assert(h.trans(x as int, e as int, h.dst@[q] as int));
                            assert(h@.f(x as int, e as int, h.dst@[q] as int));
                        }
                    }
                    // Math: complete for e: every y ∈ f_Hc(x, e) is now in the block
                    assert forall|y: int| #[trigger] comp(h, m as int, x as int, e as int, y)
                        implies exists|kp: int| b0 <= kp < evt2@.len() && #[trigger] evt2@[kp] as int == e && dst2@[kp] as int == y by {
                        if h@.f(x as int, e as int, y) {
                            // Math: y = dst_H[q] for a position q ∈ [k0, k) of x's block
                            let q = choose|q: int| #[trigger] h.in_blk(x as int, q) && h.evt@[q] as int == e && h.dst@[q] as int == y;
                            assert(k0 <= q < k);
                            let kp = b1 + (q - k0);
                            assert(evt2@[kp] as int == e && dst2@[kp] as int == y);
                        } else {
                            // Math: y = d and f_H(x, e) = ∅, so nothing was copied: the dump entry
                            if k > k0 {
                                assert(h.in_blk(x as int, k0 as int));
                                assert(h.trans(x as int, e as int, h.dst@[k0 as int] as int));
                                assert(h@.f(x as int, e as int, h.dst@[k0 as int] as int));
                            }
                            assert(evt2@[b1 as int] as int == e && dst2@[b1 as int] as int == y);
                        }
                    }
                }
            } else {
                // Math: e ∉ E_H: no position has e (trans_ok), so from k on, events > e
                assert forall|q: int| k <= q < hi implies #[trigger] h.evt@[q] >= e + 1 by {
                    assert(h.in_e@[h.evt@[q] as int]);
                }
                // Math: no move of Hc from x on e (e is neither in E_H nor extra)
                assert forall|y: int| !#[trigger] comp(h, m as int, x as int, e as int, y) by {}
            }
        } else {
            // Math: e extra: from k on there are no positions (H's events are < m_H ≤ e)
            assert forall|q: int| k <= q < hi implies #[trigger] h.evt@[q] >= e + 1 by {
                assert(h.evt@[q] < h.m);
            }
            // Math: evt2 := evt2 · [e]; dst2 := dst2 · [x] (the self-loop)
            evt2.push(e);
            dst2.push(x);
            proof {
                // Math: comp(x, e, y) ↔ y = x: the entry at b1
                assert forall|y: int| #[trigger] comp(h, m as int, x as int, e as int, y)
                    implies exists|kp: int| b0 <= kp < evt2@.len() && #[trigger] evt2@[kp] as int == e && dst2@[kp] as int == y by {
                    assert(evt2@[b1 as int] as int == e && dst2@[b1 as int] as int == y);
                }
            }
        }
        proof {
            // Math: the old entries are unchanged
            assert forall|j: int| 0 <= j < b1 implies #[trigger] evt2@[j] == ev1[j] && dst2@[j] == ds1[j] by {}
            // Math: complete for events < e + 1: old witnesses (< b1) are unchanged
            assert forall|ee: int, y: int| ee < e + 1 && #[trigger] comp(h, m as int, x as int, ee, y)
                implies exists|kp: int| b0 <= kp < evt2@.len() && #[trigger] evt2@[kp] as int == ee && dst2@[kp] as int == y by {
                if ee < e {
                    let kp = choose|kp: int| b0 <= kp < ev1.len() && #[trigger] ev1[kp] as int == ee && ds1[kp] as int == y;
                    assert(evt2@[kp] == ev1[kp] && dst2@[kp] == ds1[kp]);
                }
            }
            // Math: the new entries are e: below e + 1, and sorted after the old ones (< e)
            assert forall|kp: int| b0 <= kp < evt2@.len() implies #[trigger] evt2@[kp] < e + 1 by {
                if kp < b1 {
                    assert(evt2@[kp] == ev1[kp]);
                }
            }
            assert forall|a: int, b: int| b0 <= a <= b < evt2@.len() implies #[trigger] evt2@[a] <= #[trigger] evt2@[b] by {
                if b < b1 {
                    assert(evt2@[a] == ev1[a] && evt2@[b] == ev1[b]);
                } else if a < b1 {
                    assert(evt2@[a] == ev1[a]);
                }
            }
            assert forall|kp: int| b0 <= kp < evt2@.len() implies #[trigger] comp(h, m as int, x as int, evt2@[kp] as int, dst2@[kp] as int) by {
                if kp < b1 {
                    assert(evt2@[kp] == ev1[kp] && dst2@[kp] == ds1[kp]);
                }
            }
        }
        // Math: e := e + 1
        e += 1;
    }
}

/// Appends the block of the dump state `d = n_H`: a self-loop on every event of `Hc`.
// Why: some variables are used only in proofs (unused once they are erased).
#[allow(unused_variables)]
fn build_dump(h: &Aut, m: usize, evt2: &mut Vec<usize>, dst2: &mut Vec<usize>)
    requires
        h.wf(),
        h.m <= m,
        old(evt2)@.len() == old(dst2)@.len(),
    ensures
        final(evt2)@.len() == final(dst2)@.len(),
        old(evt2)@.len() <= final(evt2)@.len(),
        forall|j: int| 0 <= j < old(evt2)@.len() ==> #[trigger] final(evt2)@[j] == old(evt2)@[j],
        forall|j: int| 0 <= j < old(evt2)@.len() ==> #[trigger] final(dst2)@[j] == old(dst2)@[j],
        block_done(h, m as int, final(evt2)@, final(dst2)@, h.n as int, old(evt2)@.len() as int, final(evt2)@.len() as int),
{
    // Why: ghost copies of the lists at the call.
    let ghost e0 = evt2@;
    let ghost d0 = dst2@;
    let b0 = evt2.len();
    let d = h.n;
    let mut e: usize = 0;
    while e < m
        invariant
            h.wf(),
            h.m <= m,
            d == h.n,
            e <= m,
            b0 == e0.len(),
            b0 <= evt2@.len(),
            dst2@.len() == evt2@.len(),
            forall|j: int| 0 <= j < b0 ==> #[trigger] evt2@[j] == e0[j],
            forall|j: int| 0 <= j < b0 ==> #[trigger] dst2@[j] == d0[j],
            // Math: the block so far: entries (e', d) for e' < e in E_Hc, increasing
            forall|kp: int| b0 <= kp < evt2@.len() ==> #[trigger] comp(h, m as int, d as int, evt2@[kp] as int, dst2@[kp] as int),
            forall|a: int, b: int| b0 <= a <= b < evt2@.len() ==> #[trigger] evt2@[a] <= #[trigger] evt2@[b],
            forall|kp: int| b0 <= kp < evt2@.len() ==> #[trigger] evt2@[kp] < e,
            complete_upto(h, m as int, evt2@, dst2@, d as int, b0 as int, evt2@.len() as int, e as int),
        decreases m - e,
    {
        let ghost ev1 = evt2@;
        let ghost ds1 = dst2@;
        let b1 = evt2.len();
        // Math: e ∈ E_Hc (extra, or in E_H) → evt2 := evt2 · [e]; dst2 := dst2 · [d]
        if e >= h.m || h.in_e[e] {
            evt2.push(e);
            dst2.push(d);
        }
        proof {
            assert forall|j: int| 0 <= j < b1 implies #[trigger] evt2@[j] == ev1[j] && dst2@[j] == ds1[j] by {}
            // Math: complete for events < e + 1 (the new entry for e, old witnesses kept)
            assert forall|ee: int, y: int| ee < e + 1 && #[trigger] comp(h, m as int, d as int, ee, y)
                implies exists|kp: int| b0 <= kp < evt2@.len() && #[trigger] evt2@[kp] as int == ee && dst2@[kp] as int == y by {
                if ee < e {
                    let kp = choose|kp: int| b0 <= kp < ev1.len() && #[trigger] ev1[kp] as int == ee && ds1[kp] as int == y;
                    assert(evt2@[kp] == ev1[kp] && dst2@[kp] == ds1[kp]);
                } else {
                    assert(evt2@[b1 as int] as int == ee && dst2@[b1 as int] as int == y);
                }
            }
            assert forall|kp: int| b0 <= kp < evt2@.len() implies #[trigger] evt2@[kp] < e + 1 by {
                if kp < b1 {
                    assert(evt2@[kp] == ev1[kp]);
                }
            }
            assert forall|a: int, b: int| b0 <= a <= b < evt2@.len() implies #[trigger] evt2@[a] <= #[trigger] evt2@[b] by {
                if b < b1 {
                    assert(evt2@[a] == ev1[a] && evt2@[b] == ev1[b]);
                } else if a < b1 {
                    assert(evt2@[a] == ev1[a]);
                }
            }
            assert forall|kp: int| b0 <= kp < evt2@.len() implies #[trigger] comp(h, m as int, d as int, evt2@[kp] as int, dst2@[kp] as int) by {
                if kp < b1 {
                    assert(evt2@[kp] == ev1[kp] && dst2@[kp] == ds1[kp]);
                }
            }
        }
        e += 1;
    }
}

/// `a · b`.
fn concat_bools(a: &Vec<bool>, b: &Vec<bool>) -> (c: Vec<bool>)
    ensures
        c@ == a@ + b@,
{
    let mut c: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a@.len(),
            c@ == a@.subrange(0, i as int),
        decreases a@.len() - i,
    {
        c.push(a[i]);
        i += 1;
        assert(c@ =~= a@.subrange(0, i as int));
    }
    assert(c@ =~= a@);
    let mut j: usize = 0;
    while j < b.len()
        invariant
            j <= b@.len(),
            c@ == a@ + b@.subrange(0, j as int),
        decreases b@.len() - j,
    {
        c.push(b[j]);
        j += 1;
        assert(c@ =~= a@ + b@.subrange(0, j as int));
    }
    assert(c@ =~= a@ + b@);
    c
}

/// `n` copies of `v`.
fn fill(n: usize, v: bool) -> (c: Vec<bool>)
    ensures
        c@.len() == n,
        forall|i: int| 0 <= i < n ==> #[trigger] c@[i] == v,
{
    let mut c: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            c@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] c@[j] == v,
        decreases n - i,
    {
        c.push(v);
        i += 1;
    }
    c
}

/// The completion `Hc` of `h` (module doc). `extra` event numbers `m_H .. m_H + extra - 1` are
/// added, with the given uncontrollable / unobservable flags; the dump state is `n_H`.
// Why: some variables are used only in proofs (unused once they are erased).
#[allow(unused_variables)]
pub fn complete(h: &Aut, extra: usize, euc_x: &Vec<bool>, euo_x: &Vec<bool>) -> (hc: Aut)
    requires
        // Math: wf(H) with a state; one flag per extra event; no overflow
        h.wf(),
        h.n > 0,
        euc_x@.len() == extra,
        euo_x@.len() == extra,
        h.n + 1 <= usize::MAX,
        h.m + extra <= usize::MAX,
    ensures
        // Math: Hc is valid; n_Hc = n_H + 1, m_Hc = m_H + extra
        hc.wf(),
        hc.n == h.n + 1,
        hc.m == h.m + extra,
        // Math: H's event flags are kept; the extra events are in E, with the given flags
        forall|e: int| 0 <= e < h.m ==> #[trigger] hc.in_e@[e] == h.in_e@[e] && hc.in_euc@[e] == h.in_euc@[e] && hc.in_euo@[e] == h.in_euo@[e],
        forall|e: int| h.m <= e < hc.m ==> #[trigger] hc.in_e@[e] && hc.in_euc@[e] == euc_x@[e - h.m] && hc.in_euo@[e] == euo_x@[e - h.m],
        // Math: initial and marked states of H kept; d neither
        forall|x: int| 0 <= x < h.n ==> #[trigger] hc.init@[x] == h.init@[x] && hc.marked@[x] == h.marked@[x],
        !hc.init@[h.n as int],
        !hc.marked@[h.n as int],
        // Math: y ∈ f_Hc(x, e) ↔ comp(x, e, y)
        forall|x: int, e: int, y: int| #[trigger] hc@.f(x, e, y) <==> comp(h, hc.m as int, x, e, y),
{
    // Math: m = m_H + extra; d = n_H
    let m = h.m + extra;
    let d = h.n;
    // Math: start2 = [0]; evt2 = dst2 = []; own = [] (ghost: the state of each position)
    let mut start2: Vec<usize> = Vec::new();
    start2.push(0);
    let mut evt2: Vec<usize> = Vec::new();
    let mut dst2: Vec<usize> = Vec::new();
    let ghost mut own: Seq<int> = Seq::empty();
    // Math: x = 0 (x walks the states of Hc, the dump state d last)
    let mut x: usize = 0;
    while x <= d
        invariant
            // Why: facts restated in each loop (a loop only knows its invariant).
            h.wf(),
            d == h.n,
            m == h.m + extra,
            h.n + 1 <= usize::MAX,
            x <= d + 1,
            // Math: |start2| = x + 1, start2[0] = 0, start2[x] = |evt2|, monotone
            start2@.len() == x + 1,
            start2@[0] == 0,
            start2@[x as int] == evt2@.len(),
            forall|a: int, b: int| 0 <= a <= b <= x ==> #[trigger] start2@[a] <= #[trigger] start2@[b],
            dst2@.len() == evt2@.len(),
            // Math: blocks 0 .. x-1 are done
            forall|z: int| 0 <= z < x ==> #[trigger] block_done(h, m as int, evt2@, dst2@, z, start2@[z] as int, start2@[z + 1] as int),
            // Math: every position belongs to a done block: start2[own[kp]] ≤ kp < start2[own[kp]+1]
            own.len() == evt2@.len(),
            forall|kp: int| 0 <= kp < evt2@.len() ==> 0 <= #[trigger] own[kp] < x && start2@[own[kp]] <= kp < start2@[own[kp] + 1],
        // Math: d + 1 - x decreases
        decreases d + 1 - x,
    {
        // Why: ghost copies before the block.
        let ghost ev1 = evt2@;
        let ghost ds1 = dst2@;
        let ghost st1 = start2@;
        let b0 = evt2.len();
        // Math: append x's block (a state of H, or the dump state)
        if x < d {
            build_block(h, m, x, &mut evt2, &mut dst2);
        } else {
            build_dump(h, m, &mut evt2, &mut dst2);
        }
        // Math: start2 := start2 · [|evt2|]
        start2.push(evt2.len());
        proof {
            // Math: earlier blocks stay done (the lists only grew)
            assert forall|z: int| 0 <= z < x implies #[trigger] block_done(h, m as int, evt2@, dst2@, z, start2@[z] as int, start2@[z + 1] as int) by {
                assert(start2@[z] == st1[z] && start2@[z + 1] == st1[z + 1]);
                lemma_extend(h, m as int, ev1, ds1, evt2@, dst2@, z, st1[z] as int, st1[z + 1] as int);
            }
            // Math: the new block x is done
            assert(block_done(h, m as int, evt2@, dst2@, x as int, start2@[x as int] as int, start2@[x + 1] as int));
            // Math: own := own · [x, ..., x] (one per new position)
            let own0 = own;
            own = own + Seq::new((evt2@.len() - b0) as nat, |j: int| x as int);
            assert forall|kp: int| 0 <= kp < evt2@.len() implies 0 <= #[trigger] own[kp] < x + 1 && start2@[own[kp]] <= kp < start2@[own[kp] + 1] by {
                if kp < b0 {
                    assert(own[kp] == own0[kp]);
                    assert(start2@[own0[kp]] == st1[own0[kp]] && start2@[own0[kp] + 1] == st1[own0[kp] + 1]);
                } else {
                    assert(own[kp] == x);
                }
            }
            // Math: start2 still monotone
            assert forall|a: int, b: int| 0 <= a <= b <= x + 1 implies #[trigger] start2@[a] <= #[trigger] start2@[b] by {
                if b == x + 1 && a <= x {
                    assert(start2@[a] <= start2@[x as int]);
                }
            }
        }
        // Math: x := x + 1
        x += 1;
    }
    // Math: the flags: E_H's, then the extra events (in E, with the given flags)
    let in_e = concat_bools(&h.in_e, &fill(extra, true));
    let in_euc = concat_bools(&h.in_euc, euc_x);
    let in_euo = concat_bools(&h.in_euo, euo_x);
    // Math: init and marked: H's, then false for d
    let init = concat_bools(&h.init, &fill(1, false));
    let marked = concat_bools(&h.marked, &fill(1, false));
    let hc = Aut { n: d + 1, m, in_e, in_euc, in_euo, init, marked, start: start2, evt: evt2, dst: dst2 };
    proof {
        let n = hc.n as int;
        // Math: flags as stated
        assert forall|e: int| 0 <= e < h.m implies #[trigger] hc.in_e@[e] == h.in_e@[e] && hc.in_euc@[e] == h.in_euc@[e] && hc.in_euo@[e] == h.in_euo@[e] by {}
        assert forall|e: int| h.m <= e < hc.m implies #[trigger] hc.in_e@[e] && hc.in_euc@[e] == euc_x@[e - h.m] && hc.in_euo@[e] == euo_x@[e - h.m] by {}
        assert forall|z: int| 0 <= z < h.n implies #[trigger] hc.init@[z] == h.init@[z] && hc.marked@[z] == h.marked@[z] by {}
        // --- wf(hc) ---
        // Math: sorted_ok: each block is sorted (block_done)
        assert forall|z: int| 0 <= z < n implies #[trigger] hc.blk_sorted(z) by {
            assert(block_done(h, m as int, hc.evt@, hc.dst@, z, hc.start@[z] as int, hc.start@[z + 1] as int));
        }
        // Math: a move of Hc has an event of Hc and a target that is a state of Hc
        assert forall|z: int, ee: int, y: int| #[trigger] comp(h, m as int, z, ee, y) implies 0 <= ee < m && hc.in_e@[ee] && 0 <= y < n by {
            if 0 <= z < h.n && h@.E.contains(ee) && h@.f(z, ee, y) {
                // Math: y = dst_H[q] < n_H (trans_ok of H)
                let q = choose|q: int| #[trigger] h.in_blk(z, q) && h.evt@[q] as int == ee && h.dst@[q] as int == y;
                assert(h.start@[z + 1] <= h.start@[h.n as int]);
                assert(h.dst@[q] < h.n);
            }
        }
        // Math: trans_ok: position k is in block own[k], so it is a move of Hc
        assert forall|k: int| 0 <= k < hc.num_trans() implies hc.evt@[k] < hc.m && hc.in_e@[#[trigger] hc.evt@[k] as int] && hc.dst@[k] < hc.n by {
            let z = own[k];
            assert(block_done(h, m as int, hc.evt@, hc.dst@, z, hc.start@[z] as int, hc.start@[z + 1] as int));
            assert(comp(h, m as int, z, hc.evt@[k] as int, hc.dst@[k] as int));
        }
        assert forall|k: int| 0 <= k < hc.num_trans() implies hc.evt@[k] < hc.m && hc.in_e@[hc.evt@[k] as int] && #[trigger] hc.dst@[k] < hc.n by {
            let z = own[k];
            assert(block_done(h, m as int, hc.evt@, hc.dst@, z, hc.start@[z] as int, hc.start@[z + 1] as int));
            assert(comp(h, m as int, z, hc.evt@[k] as int, hc.dst@[k] as int));
        }
        // Math: events_ok: H's flags (W2 of H), and the extra events are in E
        assert forall|ee: int| 0 <= ee < hc.m implies (#[trigger] hc.in_euc@[ee] ==> hc.in_e@[ee]) && (hc.in_euo@[ee] ==> hc.in_e@[ee]) by {
            if ee < h.m {
                assert(h.in_euc@[ee] ==> h.in_e@[ee]);
                assert(h.in_euo@[ee] ==> h.in_e@[ee]);
            }
        }
        assert forall|ee: int| 0 <= ee < hc.m implies (hc.in_euc@[ee] ==> hc.in_e@[ee]) && (#[trigger] hc.in_euo@[ee] ==> hc.in_e@[ee]) by {
            if ee < h.m {
                assert(h.in_euo@[ee] ==> h.in_e@[ee]);
            }
        }
        // Math: init_ok: an initial state of H (n_H > 0) is initial in Hc
        let x0 = choose|z: int| 0 <= z < h.n && #[trigger] h.init@[z];
        assert(hc.init@[x0]);
        assert(hc.wf());
        // --- the moves ---
        assert forall|z: int, ee: int, y: int| #[trigger] hc@.f(z, ee, y) <==> comp(h, hc.m as int, z, ee, y) by {
            if hc@.f(z, ee, y) {
                // Math: a position k of z's block carries (ee, y): sound part of block_done(z)
                let k = choose|k: int| #[trigger] hc.in_blk(z, k) && hc.evt@[k] as int == ee && hc.dst@[k] as int == y;
                assert(block_done(h, m as int, hc.evt@, hc.dst@, z, hc.start@[z] as int, hc.start@[z + 1] as int));
                assert(comp(h, m as int, z, hc.evt@[k] as int, hc.dst@[k] as int));
            }
            if comp(h, hc.m as int, z, ee, y) {
                // Math: z ∈ [0, n]; complete part of block_done(z) gives the position
                assert(0 <= z < n);
                assert(block_done(h, m as int, hc.evt@, hc.dst@, z, hc.start@[z] as int, hc.start@[z + 1] as int));
                assert(ee < m);
                let k = choose|k: int| hc.start@[z] <= k < hc.start@[z + 1] && #[trigger] hc.evt@[k] as int == ee && hc.dst@[k] as int == y;
                assert(hc.in_blk(z, k));
                assert(hc.trans(z, ee, y));
            }
        }
    }
    hc
}

} // verus!
