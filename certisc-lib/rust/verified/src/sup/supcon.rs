//! Supervisory control, prefix-closed (spec: certisc-proof/spec/supervisor.md; Lean:
//! `Supervisor.lean`, `supcon_escape` and `supervisor_escape_L`).
//!
//! Input: `p` = P0 = G ‖ H (built by the verified `compose_aut`), the plant `g`, and `p1`, the
//! plant state of each state of `p`. This file computes, all verified:
//! - `bad0`: the states with an uncontrollable *escape* (an event the plant can do there but
//!   P0 cannot; Lean `bad0`);
//! - `keep_events`: P0 with only the uncontrollable transitions (Lean `ucOnly`);
//! - `supervisor_pc`: the whole chain: Bad = coreach over the uncontrollable part from Bad0
//!   (Lean `badE`), then delete Bad, then the accessible part. Its contract states the
//!   hypotheses of Lean's `supervisor_escape_L`.
//!
//! Glossary (in addition to `aut.rs`, `reach.rs`, `delete.rs`):
//! - `en(v, x, e)`: event `e` is enabled at state `x` of the view `v` (some `y ∈ f(x, e)`).
//! - `AutView { delta: ..., ..v }`: the view `v` with only its `delta` field replaced.
//! - `Ghost(v)`: a value returned for the proof only (erased when compiled).

use crate::core_aut::aut::*;
use crate::ops_aut::delete::*;
use crate::ops_aut::reach::*;
use crate::ops_aut::basic_ops::lower_bound;
use vstd::prelude::*;

verus! {

/// `e` is enabled at `x` in `v`: `f(x, e) ≠ ∅` (Lean: `(f x e).Nonempty`).
pub open spec fn en(v: AutView, x: int, e: int) -> bool {
    // Math: ∃ y: y ∈ f(x, e)
    exists|y: int| #[trigger] v.f(x, e, y)
}

/// Event `e` escapes at state `i` of `p`: it is uncontrollable, the plant can do it at its
/// state `p1[i]`, and `p` cannot do it at `i`.
pub open spec fn esc_at(p: AutView, g: AutView, p1: Seq<usize>, i: int, e: int) -> bool {
    // Math: e ∈ Euc_P ∧ en(G, p1[i], e) ∧ ¬en(P, i, e)
    &&& p.Euc.contains(e)
    &&& en(g, p1[i] as int, e)
    &&& !en(p, i, e)
}

/// The states of `p` with an uncontrollable escape (Lean: `bad0`).
pub open spec fn esc_set(p: AutView, g: AutView, p1: Seq<usize>) -> ISet<int> {
    // Math: {i ∈ [0, n) | ∃ e: esc_at(i, e)}
    ISet::new(|i: int| 0 <= i < p.n && exists|e: int| #[trigger] esc_at(p, g, p1, i, e))
}

/// The uncontrollable part of `v`: the same automaton with only the transitions on events of
/// `Euc` (Lean: `ucOnly f Euc`).
pub open spec fn uc_part(v: AutView) -> AutView {
    // Math: delta' = {(x, e, y) ∈ delta | e ∈ Euc}; every other field unchanged
    AutView { delta: ISet::new(|t: (int, int, int)| v.f(t.0, t.1, t.2) && v.Euc.contains(t.1)), ..v }
}

/// Whether `e` is enabled at `x` (binary search in `x`'s block).
pub fn enabled(g: &Aut, x: usize, e: usize) -> (r: bool)
    requires
        // Math: wf(g) ∧ x < n
        // Why: lower_bound needs a valid automaton and a state.
        g.wf(),
        x < g.n,
    ensures
        // Math: r ↔ en(G, x, e)
        r == en(g@, x as int, e as int),
{
    // Math: lo = the first position of x's block with evt ≥ e
    let lo = lower_bound(g, x, e);
    // Math: start[x+1] ≤ T
    // Why: hint: so evt[lo] can be read when lo < start[x+1].
    assert(g.start@[x + 1] <= g.start@[g.n as int]);
    // Math: r = (lo < start[x+1] ∧ evt[lo] = e)
    let r = lo < g.start[x + 1] && g.evt[lo] == e;
    proof {
        if r {
            // Math: x --e--> dst[lo]: the witness of en
            assert(g.in_blk(x as int, lo as int));
            assert(g.trans(x as int, e as int, g.dst@[lo as int] as int));
            assert(g@.f(x as int, e as int, g.dst@[lo as int] as int));
        } else {
            // Math: no y ∈ f(x, e): a position k with evt[k] = e would be ≥ lo (lower_bound),
            //       and then evt[lo] ≤ evt[k] = e ≤ evt[lo] (sorted), so evt[lo] = e.
            assert forall|y: int| !g@.f(x as int, e as int, y) by {
                if g@.f(x as int, e as int, y) {
                    // Math: k: the position of x --e--> y
                    let k = choose|k: int| #[trigger] g.in_blk(x as int, k) && g.evt@[k] as int == e && g.dst@[k] as int == y;
                    // Math: blk_sorted(x)
                    assert(g.blk_sorted(x as int));
                    // Math: k ≥ lo, so lo < start[x+1] and evt[lo] ≤ evt[k] = e
                    assert(lo <= k);
                    assert(g.evt@[lo as int] <= g.evt@[k]);
                }
            }
        }
    }
    r
}

/// `r[i]` ↔ state `i` of `p` has an uncontrollable escape (Lean: `bad0`), for `p` = G ‖ H with
/// plant labels `p1`.
pub fn bad0(p: &Aut, g: &Aut, p1: &Vec<usize>) -> (r: Vec<bool>)
    requires
        // Math: wf(P), wf(G); one plant state per state of P; m_G ≤ m_P
        // Why: G's event numbers are P's (G is the first input of the composition), so a G
        //      event indexes P's flags.
        p.wf(),
        g.wf(),
        p1@.len() == p.n,
        forall|i: int| 0 <= i < p.n ==> #[trigger] p1@[i] < g.n,
        g.m <= p.m,
    ensures
        // Math: |r| = n_P
        r@.len() == p.n,
        // Math: ∀ i: r[i] ↔ i ∈ esc_set
        forall|i: int| 0 <= i < p.n ==> (#[trigger] r@[i] <==> esc_set(p@, g@, p1@).contains(i)),
{
    // Math: r = []
    let mut r: Vec<bool> = Vec::new();
    // Math: i = 0 (i walks the states of P)
    let mut i: usize = 0;
    while i < p.n
        invariant
            // Why: facts restated in each loop (a loop only knows its invariant).
            p.wf(),
            g.wf(),
            p1@.len() == p.n,
            forall|i: int| 0 <= i < p.n ==> #[trigger] p1@[i] < g.n,
            g.m <= p.m,
            i <= p.n,
            // Math: |r| = i, and r[i'] is right for i' < i
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> (#[trigger] r@[j] <==> esc_set(p@, g@, p1@).contains(j)),
        // Math: n_P - i decreases
        decreases p.n - i,
    {
        // Math: a = p1[i], the plant state of i; [lo, hi) = a's block in G
        let a = p1[i];
        let lo = g.start[a];
        let hi = g.start[a + 1];
        // Math: start_G[a] ≤ start_G[a+1] ≤ T_G
        // Why: hint: the block lies inside evt_G.
        assert(g.start@[a as int] <= g.start@[a + 1] <= g.start@[g.n as int]);
        // Math: found = false; k = lo (k walks a's block)
        let mut found = false;
        let mut k = lo;
        while k < hi
            invariant
                // Why: facts restated in each loop (a loop only knows its invariant).
                p.wf(),
                g.wf(),
                g.m <= p.m,
                i < p.n,
                a == p1@[i as int],
                a < g.n,
                lo == g.start@[a as int],
                hi == g.start@[a + 1],
                hi <= g.evt@.len(),
                lo <= k <= hi,
                // Math: found ↔ ∃ k' ∈ [lo, k): esc_at(i, evt_G[k'])
                found <==> exists|kk: int| lo <= kk < k && #[trigger] esc_at(p@, g@, p1@, i as int, g.evt@[kk] as int),
            // Math: hi - k decreases
            decreases hi - k,
        {
            // Math: e = evt_G[k]; e < m_G ≤ m_P (trans_ok of G)
            let e = g.evt[k];
            assert(g.evt@[k as int] < g.m);
            // Math: en(G, a, e): the transition at k
            proof {
                assert(g.in_blk(a as int, k as int));
                assert(g.trans(a as int, e as int, g.dst@[k as int] as int));
                assert(g@.f(a as int, e as int, g.dst@[k as int] as int));
            }
            // Math: e ∈ Euc_P ∧ ¬en(P, i, e) → found := true
            if p.in_euc[e] && !enabled(p, i, e) {
                // Math: esc_at(i, e) with k as the witness position
                assert(esc_at(p@, g@, p1@, i as int, g.evt@[k as int] as int));
                found = true;
            } else {
                // Math: ¬esc_at(i, evt_G[k])
                // Why: hint: names the case for the invariant (e ∉ Euc_P, or en(P, i, e)).
                assert(!esc_at(p@, g@, p1@, i as int, g.evt@[k as int] as int));
            }
            // Math: k := k + 1
            k += 1;
        }
        proof {
            // Math: found ↔ ∃ e: esc_at(i, e)
            // Why: an escaping e is enabled in G at a, so it is the event of a position of
            //      a's block, which the loop walked.
            if exists|e: int| #[trigger] esc_at(p@, g@, p1@, i as int, e) {
                let e = choose|e: int| #[trigger] esc_at(p@, g@, p1@, i as int, e);
                // Math: y ∈ f_G(a, e), at a position kk of a's block
                let y = choose|y: int| #[trigger] g@.f(a as int, e, y);
                let kk = choose|kk: int| #[trigger] g.in_blk(a as int, kk) && g.evt@[kk] as int == e && g.dst@[kk] as int == y;
                // Math: kk ∈ [lo, hi)
                assert(lo <= kk < hi);
                assert(esc_at(p@, g@, p1@, i as int, g.evt@[kk] as int));
            }
        }
        // Math: r := r · [found]
        r.push(found);
        // Math: i := i + 1
        i += 1;
    }
    r
}

/// A copy of a list of flags.
fn copy_bools(v: &Vec<bool>) -> (w: Vec<bool>)
    ensures
        // Math: w = v
        w@ == v@,
{
    // Math: w = []; i = 0
    let mut w: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            // Math: w = v[0 .. i-1]
            w@ == v@.subrange(0, i as int),
        // Math: |v| - i decreases
        decreases v@.len() - i,
    {
        // Math: w := w · [v[i]]; i := i + 1
        w.push(v[i]);
        i += 1;
        // Math: w = v[0 .. i-1] (extensionality)
        assert(w@ =~= v@.subrange(0, i as int));
    }
    // Math: w = v
    assert(w@ =~= v@);
    w
}

/// Facts about output position `kp` of `keep_events`: it lies in the block of state `s2[kp]`
/// (finished if `s2[kp] < i`), comes from position `w[kp]` of the same state's block in `g`,
/// copies its event and target, and that event is kept.
pub open spec fn kpos_ok(
    g: &Aut,
    keep: Seq<bool>,
    start2: Seq<usize>,
    evt2: Seq<usize>,
    dst2: Seq<usize>,
    w: Seq<int>,
    s2: Seq<int>,
    i: int,
    kp: int,
) -> bool {
    // Math: 0 ≤ s2[kp] ≤ i; start2[s2[kp]] ≤ kp (< start2[s2[kp]+1] if that block is finished)
    &&& 0 <= s2[kp] <= i
    &&& start2[s2[kp]] <= kp
    &&& s2[kp] < i ==> kp < start2[s2[kp] + 1]
    // Math: w[kp] ∈ block_G(s2[kp])
    &&& g.in_blk(s2[kp], w[kp])
    // Math: evt2[kp] = evt[w[kp]], dst2[kp] = dst[w[kp]], keep[evt[w[kp]]]
    &&& evt2[kp] == g.evt@[w[kp]]
    &&& dst2[kp] == g.dst@[w[kp]]
    &&& keep[g.evt@[w[kp]] as int]
}

/// `g` with only the transitions whose event is kept (`keep[e]`); same states, events, flags,
/// initial and marked states. With `keep` = the `Euc` flags, this is the uncontrollable part
/// `uc_part(g@)` (Lean: `ucOnly f Euc`).
pub fn keep_events(g: &Aut, keep: &Vec<bool>) -> (h: Aut)
    requires
        // Math: wf(G); one flag per event
        g.wf(),
        keep@.len() == g.m,
    ensures
        // Math: the result is a valid automaton
        h.wf(),
        // Math: same n, m, flags, initial and marked states
        h.n == g.n,
        h.m == g.m,
        h.in_e@ == g.in_e@,
        h.in_euc@ == g.in_euc@,
        h.in_euo@ == g.in_euo@,
        h.init@ == g.init@,
        h.marked@ == g.marked@,
        // Math: y ∈ f_H(x, e) ↔ y ∈ f_G(x, e) ∧ e ∈ [0, m) ∧ keep[e]
        // Why: the kept transitions, and no other.
        forall|x: int, e: int, y: int| #[trigger] h@.f(x, e, y) <==> (g@.f(x, e, y) && 0 <= e < g.m && keep@[e]),
{
    // Math: start2 = [0]; evt2 = dst2 = []
    let mut start2: Vec<usize> = Vec::new();
    start2.push(0);
    let mut evt2: Vec<usize> = Vec::new();
    let mut dst2: Vec<usize> = Vec::new();
    // Math: w = s2 = [] (ghost); pos = [0] * T (ghost)
    // Why: w[kp]: source position of output position kp; s2[kp]: its state; pos[k]: the
    //      output position of kept source position k.
    let ghost mut w: Seq<int> = Seq::empty();
    let ghost mut s2: Seq<int> = Seq::empty();
    let ghost mut pos: Seq<int> = Seq::new(g.evt@.len(), |k: int| 0);
    // Math: i = 0 (i walks the states: blocks 0 .. i-1 are done)
    let mut i: usize = 0;
    while i < g.n
        invariant
            // Why: facts restated in each loop (a loop only knows its invariant).
            g.wf(),
            keep@.len() == g.m,
            i <= g.n,
            // Math: |start2| = i + 1, start2[0] = 0, start2[i] = |evt2|, monotone
            start2@.len() == i + 1,
            start2@[0] == 0,
            start2@[i as int] == evt2@.len(),
            forall|a: int, b: int| 0 <= a <= b <= i ==> #[trigger] start2@[a] <= #[trigger] start2@[b],
            // Math: |dst2| = |w| = |s2| = |evt2|, |pos| = T
            dst2@.len() == evt2@.len(),
            w.len() == evt2@.len(),
            s2.len() == evt2@.len(),
            pos.len() == g.evt@.len(),
            // Math: ∀ kp: kpos_ok(kp), s2[kp] < i
            forall|kp: int| 0 <= kp < evt2@.len() ==> #[trigger] kpos_ok(g, keep@, start2@, evt2@, dst2@, w, s2, i as int, kp),
            forall|kp: int| 0 <= kp < evt2@.len() ==> #[trigger] s2[kp] < i,
            // Math: w is increasing
            forall|a: int, b: int| 0 <= a < b < evt2@.len() ==> #[trigger] w[a] < #[trigger] w[b],
            // Math: completeness for the states done: kept k in block(x), x < i → pos[k] is right
            forall|x: int, k: int|
                0 <= x < i && #[trigger] g.in_blk(x, k) && keep@[g.evt@[k] as int] ==> {
                    let kp = pos[k];
                    0 <= kp < evt2@.len() && s2[kp] == x && w[kp] == k
                },
        // Math: n - i decreases
        decreases g.n - i,
    {
        // Math: [lo, hi) = i's block
        let lo = g.start[i];
        let hi = g.start[i + 1];
        // Math: start[i] ≤ start[i+1] ≤ T
        assert(g.start@[i as int] <= g.start@[i + 1] <= g.start@[g.n as int]);
        // Why: earlier output positions come from blocks of earlier states, so before lo.
        assert forall|kp: int| 0 <= kp < evt2@.len() implies #[trigger] w[kp] < lo by {
            // Math: kpos_ok(kp): w[kp] ∈ block(s2[kp]), s2[kp] < i
            assert(kpos_ok(g, keep@, start2@, evt2@, dst2@, w, s2, i as int, kp));
            // Math: w[kp] < start[s2[kp]+1] ≤ start[i] = lo
            assert(g.start@[s2[kp] + 1] <= g.start@[i as int]);
        }
        // Math: k = lo (k walks i's block)
        let mut k = lo;
        while k < hi
            invariant
                // Why: facts restated in each loop (a loop only knows its invariant).
                g.wf(),
                keep@.len() == g.m,
                i < g.n,
                lo == g.start@[i as int],
                hi == g.start@[i + 1],
                hi <= g.evt@.len(),
                lo <= k <= hi,
                start2@.len() == i + 1,
                start2@[0] == 0,
                start2@[i as int] <= evt2@.len(),
                forall|a: int, b: int| 0 <= a <= b <= i ==> #[trigger] start2@[a] <= #[trigger] start2@[b],
                dst2@.len() == evt2@.len(),
                w.len() == evt2@.len(),
                s2.len() == evt2@.len(),
                pos.len() == g.evt@.len(),
                forall|kp: int| 0 <= kp < evt2@.len() ==> #[trigger] kpos_ok(g, keep@, start2@, evt2@, dst2@, w, s2, i as int, kp),
                // Math: the positions of the current block are those from start2[i] on
                forall|kp: int| 0 <= kp < evt2@.len() ==> (#[trigger] s2[kp] == i <==> start2@[i as int] <= kp),
                forall|a: int, b: int| 0 <= a < b < evt2@.len() ==> #[trigger] w[a] < #[trigger] w[b],
                // Math: ∀ kp: w[kp] < k
                // Why: so appending source k keeps w increasing.
                forall|kp: int| 0 <= kp < evt2@.len() ==> #[trigger] w[kp] < k,
                forall|x: int, kk: int|
                    0 <= x < i && #[trigger] g.in_blk(x, kk) && keep@[g.evt@[kk] as int] ==> {
                        let kp = pos[kk];
                        0 <= kp < evt2@.len() && s2[kp] == x && w[kp] == kk
                    },
                // Math: ∀ k' ∈ [lo, k): keep[evt[k']] → pos[k'] is its output position
                forall|kk: int|
                    lo <= kk < k && keep@[#[trigger] g.evt@[kk] as int] ==> {
                        let kp = pos[kk];
                        0 <= kp < evt2@.len() && s2[kp] == i && w[kp] == kk
                    },
            // Math: hi - k decreases
            decreases hi - k,
        {
            // Math: e = evt[k] < m (trans_ok)
            let e = g.evt[k];
            assert(g.evt@[k as int] < g.m);
            // Math: kept event? then copy the transition
            if keep[e] {
                // Math: kp = |evt2|, the new output position
                let ghost kp = evt2@.len() as int;
                // Why: ghost copies of evt2 and dst2 before the push.
                let ghost e0 = evt2@;
                let ghost d0 = dst2@;
                // Math: evt2 := evt2 · [e]; dst2 := dst2 · [dst[k]]
                evt2.push(e);
                dst2.push(g.dst[k]);
                proof {
                    // Why: ghost copies to show the old positions keep their facts.
                    let w0 = w;
                    let s20 = s2;
                    let pos0 = pos;
                    // Math: w := w · [k]; s2 := s2 · [i]; pos[k] := kp
                    w = w.push(k as int);
                    s2 = s2.push(i as int);
                    pos = pos.update(k as int, kp);
                    // Math: k ∈ block(i)
                    assert(g.in_blk(i as int, k as int));
                    // Math: ∀ q: kpos_ok(q) after the push
                    assert forall|q: int| 0 <= q < evt2@.len() implies #[trigger] kpos_ok(g, keep@, start2@, evt2@, dst2@, w, s2, i as int, q) by {
                        if q < kp {
                            // Old position: same facts as before the push.
                            assert(kpos_ok(g, keep@, start2@, e0, d0, w0, s20, i as int, q));
                            assert(w[q] == w0[q] && s2[q] == s20[q]);
                            assert(evt2@[q] == e0[q] && dst2@[q] == d0[q]);
                        } else {
                            // The new position: from source position k of state i.
                            assert(w[q] == k && s2[q] == i);
                            assert(evt2@[q] == e && dst2@[q] == g.dst@[k as int]);
                        }
                    }
                    // Math: inner completeness for k + 1
                    assert forall|kk: int| lo <= kk <= k && keep@[#[trigger] g.evt@[kk] as int] implies {
                        let q = pos[kk];
                        0 <= q < evt2@.len() && s2[q] == i && w[q] == kk
                    } by {
                        if kk < k {
                            // Math: pos[k'] unchanged (k' ≠ k); w there unchanged
                            assert(pos[kk] == pos0[kk]);
                            assert(w[pos0[kk]] == w0[pos0[kk]]);
                        }
                    }
                    // Math: outer completeness: earlier blocks end before lo ≤ k, so pos unchanged
                    assert forall|x: int, kk: int|
                        0 <= x < i && #[trigger] g.in_blk(x, kk) && keep@[g.evt@[kk] as int] implies {
                            let q = pos[kk];
                            0 <= q < evt2@.len() && s2[q] == x && w[q] == kk
                        } by {
                        // Math: block(x) ends at start[x+1] ≤ start[i] = lo ≤ k
                        assert(g.start@[x + 1] <= g.start@[i as int]);
                        assert(pos[kk] == pos0[kk]);
                        assert(w[pos0[kk]] == w0[pos0[kk]]);
                    }
                }
            }
            // Math: k := k + 1
            k += 1;
        }
        // Why: ghost copy of start2 before closing the block.
        let ghost st0 = start2@;
        // Math: start2 := start2 · [|evt2|] (block i ends here)
        start2.push(evt2.len());
        proof {
            // Why: the finished block i ends at |evt2|; earlier facts carry over.
            assert forall|q: int| 0 <= q < evt2@.len() implies #[trigger] kpos_ok(g, keep@, start2@, evt2@, dst2@, w, s2, i + 1, q) && s2[q] < i + 1 by {
                assert(kpos_ok(g, keep@, st0, evt2@, dst2@, w, s2, i as int, q));
                assert(start2@[s2[q]] == st0[s2[q]]);
                if s2[q] < i {
                    assert(start2@[s2[q] + 1] == st0[s2[q] + 1]);
                }
            }
            // Why: all output positions so far belong to blocks 0 .. i (trigger s2[q]).
            assert forall|q: int| 0 <= q < evt2@.len() implies #[trigger] s2[q] < i + 1 by {
                assert(kpos_ok(g, keep@, st0, evt2@, dst2@, w, s2, i as int, q));
            }
            // Math: start2 still monotone: the new entry |evt2| ≥ start2[i]
            assert forall|a: int, b: int| 0 <= a <= b <= i + 1 implies #[trigger] start2@[a] <= #[trigger] start2@[b] by {
                if b == i + 1 && a <= i {
                    assert(start2@[a] <= start2@[i as int]);
                }
            }
            // Math: completeness now also for state i
            assert forall|x: int, kk: int|
                0 <= x < i + 1 && #[trigger] g.in_blk(x, kk) && keep@[g.evt@[kk] as int] implies {
                    let q = pos[kk];
                    0 <= q < evt2@.len() && s2[q] == x && w[q] == kk
                } by {
                if x == i {
                    // Math: k' ∈ [lo, hi): the inner invariant at k = hi
                    assert(lo <= kk < hi);
                }
            }
        }
        // Math: i := i + 1
        i += 1;
    }
    // Math: h = g's flags, init, marked, with the kept blocks
    let h = Aut {
        n: g.n,
        m: g.m,
        in_e: copy_bools(&g.in_e),
        in_euc: copy_bools(&g.in_euc),
        in_euo: copy_bools(&g.in_euo),
        init: copy_bools(&g.init),
        marked: copy_bools(&g.marked),
        start: start2,
        evt: evt2,
        dst: dst2,
    };
    proof {
        // Why: names for the proof.
        let n = g.n as int;
        // Block membership: a position of block x of h has s2 = x.
        // Math: start2[x] ≤ kp < start2[x+1] → s2[kp] = x (blocks are disjoint)
        assert forall|x: int, kp: int| #[trigger] h.in_blk(x, kp) implies 0 <= kp < h.evt@.len() && s2[kp] == x by {
            // Math: start2[x+1] ≤ start2[n] = |evt2|
            assert(h.start@[x + 1] <= h.start@[n]);
            // Math: kpos_ok(kp)
            assert(kpos_ok(g, keep@, h.start@, h.evt@, h.dst@, w, s2, n, kp));
            let sk = s2[kp];
            if sk < x {
                // Math: start2[sk+1] ≤ start2[x] ≤ kp, contradicting kp < start2[sk+1]
                assert(h.start@[sk + 1] <= h.start@[x]);
            } else if sk > x {
                // Math: start2[x+1] ≤ start2[sk] ≤ kp, contradicting kp < start2[x+1]
                assert(h.start@[x + 1] <= h.start@[sk]);
            }
        }
        // --- wf(h) ---
        // Math: sorted_ok: within block x, w increases and stays in g's block x (sorted)
        assert forall|x: int| 0 <= x < n implies #[trigger] h.blk_sorted(x) by {
            assert forall|k: int, l: int| h.start@[x] <= k <= l < h.start@[x + 1] implies #[trigger] h.evt@[k] <= #[trigger] h.evt@[l] by {
                // Math: s2[k] = s2[l] = x
                assert(h.in_blk(x, k) && h.in_blk(x, l));
                assert(kpos_ok(g, keep@, h.start@, h.evt@, h.dst@, w, s2, n, k));
                assert(kpos_ok(g, keep@, h.start@, h.evt@, h.dst@, w, s2, n, l));
                // Math: w[k] ≤ w[l], both in g's block x, which is sorted
                assert(g.blk_sorted(x));
                if k < l {
                    assert(w[k] < w[l]);
                }
            }
        }
        // Math: trans_ok: evt2[kp] = evt[w[kp]] ∈ E, dst2[kp] = dst[w[kp]] < n
        assert forall|kp: int| 0 <= kp < h.num_trans() implies h.evt@[kp] < h.m && h.in_e@[#[trigger] h.evt@[kp] as int] && h.dst@[kp] < h.n by {
            assert(kpos_ok(g, keep@, h.start@, h.evt@, h.dst@, w, s2, n, kp));
            assert(g.evt@[w[kp]] < g.m);
        }
        assert forall|kp: int| 0 <= kp < h.num_trans() implies h.evt@[kp] < h.m && h.in_e@[h.evt@[kp] as int] && #[trigger] h.dst@[kp] < h.n by {
            assert(kpos_ok(g, keep@, h.start@, h.evt@, h.dst@, w, s2, n, kp));
            assert(g.evt@[w[kp]] < g.m);
        }
        // Math: blocks_ok: start2[n] = |evt2|, monotone (loop invariant at i = n)
        assert(h.blocks_ok());
        // Math: events_ok, init_ok: the same flags as g
        assert(h.events_ok());
        // Math: n > 0 → an initial state x of g, which is initial in h (same flags)
        // Why: hint: the witness of init_ok's ∃.
        if n > 0 {
            let x = choose|x: int| 0 <= x < g.n && #[trigger] g.init@[x];
            assert(h.init@[x]);
        }
        assert(h.init_ok());
        assert(h.wf());
        // --- the transitions ---
        assert forall|x: int, e: int, y: int| #[trigger] h@.f(x, e, y) <==> (g@.f(x, e, y) && 0 <= e < g.m && keep@[e]) by {
            if h@.f(x, e, y) {
                // Math: kp ∈ block_H(x) with evt2 = e, dst2 = y; then w[kp] ∈ block_G(x)
                let kp = choose|kp: int| #[trigger] h.in_blk(x, kp) && h.evt@[kp] as int == e && h.dst@[kp] as int == y;
                assert(s2[kp] == x);
                assert(kpos_ok(g, keep@, h.start@, h.evt@, h.dst@, w, s2, n, kp));
                assert(g.trans(x, e, y));
                assert(g.evt@[w[kp]] < g.m);
            }
            if g@.f(x, e, y) && 0 <= e < g.m && keep@[e] {
                // Math: k ∈ block_G(x) with evt = e, dst = y; pos[k] is in block_H(x)
                let k = choose|k: int| #[trigger] g.in_blk(x, k) && g.evt@[k] as int == e && g.dst@[k] as int == y;
                let kp = pos[k];
                assert(kpos_ok(g, keep@, h.start@, h.evt@, h.dst@, w, s2, n, kp));
                assert(h.in_blk(x, kp));
                assert(h.trans(x, e, y));
            }
        }
    }
    h
}

/// `dele[x]` is true exactly for the states `x` in `out`.
fn in_flags(n: usize, out: &Vec<usize>) -> (dele: Vec<bool>)
    requires
        // Math: ∀ i: out[i] < n
        forall|i: int| 0 <= i < out@.len() ==> #[trigger] out@[i] < n,
    ensures
        // Math: |dele| = n; dele[x] ↔ x ∈ set_of(out)
        dele@.len() == n,
        forall|x: int| 0 <= x < n ==> #[trigger] dele@[x] == set_of(out@).contains(x),
{
    // Math: dele = [false] * n
    let mut dele = falses(n);
    // Math: i = 0 (i walks out)
    let mut i: usize = 0;
    while i < out.len()
        invariant
            forall|i: int| 0 <= i < out@.len() ==> #[trigger] out@[i] < n,
            i <= out@.len(),
            dele@.len() == n,
            // Math: dele[x] ↔ x ∈ {out[0], ..., out[i-1]}
            forall|x: int|
                0 <= x < n ==> #[trigger] dele@[x] == (exists|j: int| 0 <= j < i && #[trigger] out@[j] as int == x),
        // Math: |out| - i decreases
        decreases out@.len() - i,
    {
        // Math: out[i] < n; dele[out[i]] := true
        assert(out@[i as int] < n);
        dele.set(out[i], true);
        // Math: i := i + 1
        i += 1;
    }
    dele
}

/// The result of `sup_tail` for the start set `T` (the states to delete first): the deleted
/// flags are `D1 = coreach(uc_part(P), T)`, `Q` is `P` without `D1`, `S` is `Ac(Q)`, and `old`
/// gives each state of `S` its state of `P`. These are the deletion hypotheses of Lean's
/// `supervisor_L` (`T` = the states outside `I`) and `supervisor_escape_L` (`T` = `Bad0`).
pub open spec fn tail_ok(p: &Aut, T: ISet<int>, s: &Aut, old: Seq<usize>, q: AutView, old1: Seq<usize>, old2: Seq<usize>, dele: Seq<bool>) -> bool {
    // Math: S is a valid automaton
    &&& s.wf()
    // Math: D1: ∀ x ∈ [0, n): dele[x] ↔ x ∈ CoAc_uc(T)  (Lean hD1)
    &&& dele.len() == p.n
    &&& forall|x: int| 0 <= x < p.n ==> (#[trigger] dele[x] <==> uc_part(p@).coreach(T).contains(x))
    // Math: Q = P with D1 deleted (Lean h1), or empty when every initial state is deleted
    &&& (exists|x: int| 0 <= x < p.n && p.init@[x] && !#[trigger] dele[x]) ==> is_deletion(p@, del_set(dele, p.n as int), q, old1)
    &&& !(exists|x: int| 0 <= x < p.n && p.init@[x] && !#[trigger] dele[x]) ==> q.n == 0
    // Math: S = Q without the states outside Ac(Q) (Lean h2), or empty
    &&& q.n > 0 ==> is_deletion(q, q.Ac().complement(), s@, old2)
    &&& q.n == 0 ==> s.n == 0
    // Math: old[i] = old1[old2[i]] < n_P
    &&& old.len() == s.n
    &&& forall|i: int| 0 <= i < s.n ==> #[trigger] old[i] == old1[old2[i] as int] && old[i] < p.n
}

/// The common tail of the supervisor: from the start set `s0` (states of `p` to delete
/// first), delete everything that reaches it by uncontrollable events only, then keep the
/// accessible part. Returns `S`, `old`, and, for the proof only, `Q`, the two renumberings and
/// the deleted flags (`tail_ok`).
pub fn sup_tail(p: &Aut, s0: &Vec<usize>) -> (r: (
    Aut,
    Vec<usize>,
    Ghost<AutView>,
    Ghost<Seq<usize>>,
    Ghost<Seq<usize>>,
    Ghost<Seq<bool>>,
))
    requires
        // Math: wf(P); s0 lists states of P
        p.wf(),
        states_in(p, s0@),
    ensures
        tail_ok(p, set_of(s0@), &r.0, r.1@, r.2@, r.3@, r.4@, r.5@),
{
    // Math: h = the uncontrollable part of P0
    let keep = copy_bools(&p.in_euc);
    let h = keep_events(p, &keep);
    proof {
        // Math: h@ = uc_part(P0@): same fields, and delta' = the uncontrollable transitions
        assert(h@.E =~= p@.E);
        assert(h@.Euc =~= p@.Euc);
        assert(h@.Euo =~= p@.Euo);
        assert(h@.X0 =~= p@.X0);
        assert(h@.Xm =~= p@.Xm);
        assert forall|t: (int, int, int)| #[trigger] h@.delta.contains(t) == uc_part(p@).delta.contains(t) by {
            // Math: keep_events at (t.0, t.1, t.2); keep[e] ↔ e ∈ Euc
            assert(h@.f(t.0, t.1, t.2) == (p@.f(t.0, t.1, t.2) && 0 <= t.1 < p.m && keep@[t.1]));
        }
        assert(h@.delta =~= uc_part(p@).delta);
        assert(h@ == uc_part(p@));
        // Math: states_in(h, s0) (h.n = p.n)
        assert(states_in(&h, s0@));
    }
    // Math: set_of(badl) = coreach_h(set_of(s0)) = D1
    let (badl, _wit) = coreachable(&h, &s0);
    // Math: dele[x] ↔ x ∈ D1
    let dele = in_flags(p.n, &badl);
    // Math: Q = P without D1; S = Ac(Q)
    let (q, old1) = delete_states(p, &dele);
    let (s, old2) = accessible(&q);
    proof {
        // Math: |old1| = n_Q and old2[i] < n_Q in every case
        if exists|x: int| 0 <= x < p.n && p.init@[x] && !#[trigger] dele@[x] {
            assert(is_deletion(p@, del_set(dele@, p.n as int), q@, old1@));
        }
        if q.n > 0 {
            assert(is_deletion(q@, q@.Ac().complement(), s@, old2@));
        }
    }
    // Math: old = [old1[old2[i]] for i]
    let mut old: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < old2.len()
        invariant
            // Math: old2 indexes old1, old1 indexes P0
            old1@.len() == q.n,
            forall|j: int| 0 <= j < q.n ==> #[trigger] old1@[j] < p.n,
            old2@.len() == s.n,
            forall|j: int| 0 <= j < s.n ==> #[trigger] old2@[j] < q.n,
            i <= old2@.len(),
            // Math: old = [old1[old2[j]] for j < i]
            old@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] old@[j] == old1@[old2@[j] as int] && old@[j] < p.n,
        // Math: |old2| - i decreases
        decreases old2@.len() - i,
    {
        // Math: old2[i] < n_Q = |old1|
        assert(old2@[i as int] < q.n);
        // Math: old := old · [old1[old2[i]]]
        old.push(old1[old2[i]]);
        // Math: i := i + 1
        i += 1;
    }
    // Why: ghost copies of the proof-only results.
    let ghost qv = q@;
    let ghost o1 = old1@;
    let ghost o2 = old2@;
    let ghost dv = dele@;
    (s, old, Ghost(qv), Ghost(o1), Ghost(o2), Ghost(dv))
}


/// The supervisor, prefix-closed (spec §2, escape form): from `p` = P0 = G ‖ H with plant
/// labels `p1`, delete `Bad = coreach over the uncontrollable part from Bad0`, then keep the
/// accessible part (`sup_tail` with `T = Bad0`).
///
/// The contract is the list of hypotheses of Lean's `supervisor_escape_L` (with `D1` = the
/// deleted flags, `en` = `en(G, p1[x], e)`); the plant facts (`hen`, `hK`) come from
/// `IsComposition` and are stated in Lean.
pub fn supervisor_pc(p: &Aut, g: &Aut, p1: &Vec<usize>) -> (r: (
    Aut,
    Vec<usize>,
    Ghost<AutView>,
    Ghost<Seq<usize>>,
    Ghost<Seq<usize>>,
    Ghost<Seq<bool>>,
))
    requires
        // Math: as bad0
        p.wf(),
        g.wf(),
        p1@.len() == p.n,
        forall|i: int| 0 <= i < p.n ==> #[trigger] p1@[i] < g.n,
        g.m <= p.m,
    ensures
        tail_ok(p, esc_set(p@, g@, p1@), &r.0, r.1@, r.2@, r.3@, r.4@, r.5@),
{
    // Math: b[i] ↔ i ∈ Bad0; s0 lists Bad0
    let b = bad0(p, g, p1);
    let s0 = states_with(p, &b);
    // Math: set_of(s0) = esc_set
    assert(set_of(s0@) =~= esc_set(p@, g@, p1@));
    sup_tail(p, &s0)
}

/// The supervisor on a strict subautomaton (spec §2, refinement form): `inside[x]` marks the
/// states of `I`; delete `Bad = coreach over the uncontrollable part from X \ I`, then keep
/// the accessible part (`sup_tail` with `T = X \ I`). The contract is the list of deletion
/// hypotheses of Lean's `supervisor_L`.
pub fn supervisor_sub(p: &Aut, inside: &Vec<bool>) -> (r: (
    Aut,
    Vec<usize>,
    Ghost<AutView>,
    Ghost<Seq<usize>>,
    Ghost<Seq<usize>>,
    Ghost<Seq<bool>>,
))
    requires
        // Math: wf(P); one flag per state
        p.wf(),
        inside@.len() == p.n,
    ensures
        tail_ok(p, ISet::new(|x: int| 0 <= x < p.n && !inside@[x]), &r.0, r.1@, r.2@, r.3@, r.4@, r.5@),
{
    // Math: outside[x] = ¬inside[x]; s0 lists X \ I
    let outside = negate(inside);
    let s0 = states_with(p, &outside);
    // Math: set_of(s0) = X \ I
    assert(set_of(s0@) =~= ISet::new(|x: int| 0 <= x < p.n && !inside@[x]));
    sup_tail(p, &s0)
}

/// `r[i] = ¬v[i]`.
pub fn negate(v: &Vec<bool>) -> (r: Vec<bool>)
    ensures
        r@.len() == v@.len(),
        forall|i: int| 0 <= i < v@.len() ==> #[trigger] r@[i] == !v@[i],
{
    let mut r: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            r@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] r@[j] == !v@[j],
        decreases v@.len() - i,
    {
        // Math: r := r · [¬v[i]]
        r.push(!v[i]);
        i += 1;
    }
    r
}

/// `inside[i]` ↔ `p2[i] ≠ d`: the states of `G × Hc` whose specification state is not the
/// dump state `d` (the inside states `I` of the refinement form).
pub fn not_label(p2: &Vec<usize>, d: usize) -> (inside: Vec<bool>)
    ensures
        inside@.len() == p2@.len(),
        forall|i: int| 0 <= i < p2@.len() ==> #[trigger] inside@[i] == (p2@[i] != d),
{
    let mut inside: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < p2.len()
        invariant
            i <= p2@.len(),
            inside@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] inside@[j] == (p2@[j] != d),
        decreases p2@.len() - i,
    {
        // Math: inside := inside · [p2[i] ≠ d]
        inside.push(p2[i] != d);
        i += 1;
    }
    inside
}

/// `a = b` for lists of flags.
fn eq_bools(a: &Vec<bool>, b: &Vec<bool>) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a@.len() == b@.len(),
            i <= a@.len(),
            // Math: a[0 .. i-1] = b[0 .. i-1]
            forall|j: int| 0 <= j < i ==> #[trigger] a@[j] == b@[j],
        decreases a@.len() - i,
    {
        if a[i] != b[i] {
            // Math: a[i] ≠ b[i], so a ≠ b
            assert(a@[i as int] != b@[i as int]);
            return false;
        }
        i += 1;
    }
    // Math: a = b (extensionality)
    assert(a@ =~= b@);
    true
}

/// `a = b` for lists of numbers.
fn eq_nums(a: &Vec<usize>, b: &Vec<usize>) -> (r: bool)
    ensures
        r == (a@ == b@),
{
    if a.len() != b.len() {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len()
        invariant
            a@.len() == b@.len(),
            i <= a@.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] a@[j] == b@[j],
        decreases a@.len() - i,
    {
        if a[i] != b[i] {
            assert(a@[i as int] != b@[i as int]);
            return false;
        }
        i += 1;
    }
    assert(a@ =~= b@);
    true
}

/// Whether `a` and `b` are the same automaton (same storage, so the same view). Used to check
/// that a specification given as a strict subautomaton really is the plant with some states
/// deleted (`b` = the specification re-encoded in the plant's event numbering, `a` = the
/// verified `delete_states` of the plant).
pub fn same_aut(a: &Aut, b: &Aut) -> (r: bool)
    ensures
        // Math: r → a@ = b@
        r ==> a@ == b@,
{
    // Math: every field equal
    let r = a.n == b.n && a.m == b.m && eq_bools(&a.in_e, &b.in_e) && eq_bools(&a.in_euc, &b.in_euc)
        && eq_bools(&a.in_euo, &b.in_euo) && eq_bools(&a.init, &b.init) && eq_bools(&a.marked, &b.marked)
        && eq_nums(&a.start, &b.start) && eq_nums(&a.evt, &b.evt) && eq_nums(&a.dst, &b.dst);
    proof {
        if r {
            // Math: equal fields give equal views (each set by extensionality)
            assert(a@.E =~= b@.E);
            assert(a@.Euc =~= b@.Euc);
            assert(a@.Euo =~= b@.Euo);
            assert(a@.X0 =~= b@.X0);
            assert(a@.Xm =~= b@.Xm);
            assert forall|t: (int, int, int)| #[trigger] a@.delta.contains(t) == b@.delta.contains(t) by {
                // Math: in_blk, evt, dst are the same in a and b
                if a.trans(t.0, t.1, t.2) {
                    let k = choose|k: int| #[trigger] a.in_blk(t.0, k) && a.evt@[k] as int == t.1 && a.dst@[k] as int == t.2;
                    assert(b.in_blk(t.0, k));
                }
                if b.trans(t.0, t.1, t.2) {
                    let k = choose|k: int| #[trigger] b.in_blk(t.0, k) && b.evt@[k] as int == t.1 && b.dst@[k] as int == t.2;
                    assert(a.in_blk(t.0, k));
                }
            }
            assert(a@.delta =~= b@.delta);
        }
    }
    r
}

} // verus!
