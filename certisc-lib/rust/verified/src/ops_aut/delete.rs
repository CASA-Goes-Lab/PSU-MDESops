//! `delete_states`, `accessible`, `coaccessible`, `trim`.
//! Python: `ops_aut/basic_ops.py` (`_delete`), `trusted/delete_states.py` (builder),
//! `verified_ops/delete.py` (checker). Lean: `IsDeletion` (Automaton.lean).
//!
//! In Python the builder was trusted and a verified checker re-checked its output (the checker
//! took most of the time). Here the builder itself is verified, and the result is proved to be
//! a valid automaton (deferred in Nagini).
//!
//! Glossary (in addition to `aut.rs`, `check.rs`, `basic_ops.rs`, `reach.rs`):
//! - `Ghost<T>` / `let ghost x`: a value that exists only in the proof (erased when compiled).
//! - `s.update(i, a)`: the sequence `s` with entry `i` replaced by `a`.
//! - `Seq::new(n, |i| a)`: the sequence `[a, a, ..., a]` of length `n`.

use crate::core_aut::aut::*;
// Why: used only by proofs (erased in a plain build).
#[allow(unused_imports)]
use crate::ops_aut::reach::*;
use vstd::prelude::*;

verus! {

/// `h` is `g` with the states of `D` deleted, `old[i]` being the state of `g` that state `i` of
/// `h` comes from (Lean: `IsDeletion G D G' old`).
pub open spec fn is_deletion(g: AutView, D: ISet<int>, h: AutView, old: Seq<usize>) -> bool {
    // Math: |old| = n'
    &&& old.len() == h.n
    // Math: ∀ i ∈ [0, n'): old[i] < n
    &&& forall|i: int| 0 <= i < h.n ==> #[trigger] old[i] < g.n
    // Math: ∀ i < j < n': old[i] < old[j]
    // Why: Lean `mono`: kept states keep their order.
    &&& forall|i: int, j: int| 0 <= i < j < h.n ==> #[trigger] old[i] < #[trigger] old[j]
    // Math: ∀ x ∈ [0, n): x ∉ D ↔ ∃ i: old[i] = x
    // Why: Lean `range`: exactly the states not in D are kept.
    &&& forall|x: int|
        0 <= x < g.n ==> (!D.contains(x) <==> exists|i: int| 0 <= i < h.n && #[trigger] old[i] as int == x)
    // Math: ∀ i, e, j ∈ [0, n'): j ∈ f'(i, e) ↔ old[j] ∈ f(old[i], e)
    // Why: Lean `f`: every transition between kept states, and no other.
    &&& forall|i: int, e: int, j: int|
        0 <= i < h.n && 0 <= j < h.n ==> (#[trigger] h.f(i, e, j) <==> g.f(old[i] as int, e, old[j] as int))
    // Math: ∀ i ∈ [0, n'): i ∈ X0' ↔ old[i] ∈ X0, and i ∈ Xm' ↔ old[i] ∈ Xm
    &&& forall|i: int| 0 <= i < h.n ==> (#[trigger] h.X0.contains(i) <==> g.X0.contains(old[i] as int))
    &&& forall|i: int| 0 <= i < h.n ==> (#[trigger] h.Xm.contains(i) <==> g.Xm.contains(old[i] as int))
    // Math: m' = m, E' = E, Euc' = Euc, Euo' = Euo
    &&& h.m == g.m
    &&& h.E == g.E
    &&& h.Euc == g.Euc
    &&& h.Euo == g.Euo
}

/// The set of states marked for deletion: `{x ∈ [0, n) | dele[x]}`.
pub open spec fn del_set(dele: Seq<bool>, n: int) -> ISet<int> {
    ISet::new(|x: int| 0 <= x < n && dele[x])
}

/// `new_of` and `old` renumber the kept states (`dele[x]` false) as `0, 1, ...` in order.
pub open spec fn renum_ok(g: &Aut, dele: Seq<bool>, new_of: Seq<usize>, old: Seq<usize>) -> bool {
    // Math: |new_of| = n
    &&& new_of.len() == g.n
    // Math: ∀ x ∈ [0, n): ¬dele[x] → new_of[x] < |old| ∧ old[new_of[x]] = x
    &&& forall|x: int|
        0 <= x < g.n && !dele[x] ==> #[trigger] new_of[x] < old.len() && old[new_of[x] as int] == x
    // Math: ∀ i ∈ [0, |old|): old[i] < n ∧ ¬dele[old[i]] ∧ new_of[old[i]] = i
    &&& forall|i: int|
        0 <= i < old.len() ==> #[trigger] old[i] < g.n && !dele[old[i] as int] && new_of[old[i] as int] == i
    // Math: ∀ i < j: old[i] < old[j]
    &&& forall|i: int, j: int| 0 <= i < j < old.len() ==> #[trigger] old[i] < #[trigger] old[j]
}

/// Number the kept states in order: `old` lists them, `new_of[x]` is the new number of `x`.
fn renumber(g: &Aut, dele: &Vec<bool>) -> (r: (Vec<usize>, Vec<usize>))
    requires
        // Why: facts restated in each loop (a loop only knows its invariant).
        g.wf(),
        // Math: |dele| = n
        dele@.len() == g.n,
    // Math/Why: see each line below.
    ensures
        // Math: renum_ok(g, dele, new_of, old)
        // Why: the kept states are numbered 0, 1, ... in order.
        renum_ok(g, dele@, r.0@, r.1@),
{
    // Math: new_of = [], old = []
    let mut new_of: Vec<usize> = Vec::new();
    let mut old: Vec<usize> = Vec::new();
    // Math: x = 0 (x walks the states)
    let mut x: usize = 0;
    while x < g.n
        invariant
            // Why: facts restated in each loop (a loop only knows its invariant).
            g.wf(),
            // Math: |dele| = n
            dele@.len() == g.n,
            // Math: 0 ≤ x ≤ n
            x <= g.n,
            // Math: |new_of| = x, |old| ≤ x
            new_of@.len() == x,
            old@.len() <= x,
            // Math: ∀ z < x: ¬dele[z] → new_of[z] < |old| ∧ old[new_of[z]] = z
            forall|z: int|
                0 <= z < x && !dele@[z] ==> #[trigger] new_of@[z] < old@.len() && old@[new_of@[z] as int] == z,
            // Math: ∀ i: old[i] < x ∧ ¬dele[old[i]] ∧ new_of[old[i]] = i
            forall|i: int|
                0 <= i < old@.len() ==> #[trigger] old@[i] < x && !dele@[old@[i] as int] && new_of@[old@[i] as int] == i,
            // Math: old is increasing
            forall|i: int, j: int| 0 <= i < j < old@.len() ==> #[trigger] old@[i] < #[trigger] old@[j],
        // Math: n - x decreases
        decreases g.n - x,
    {
        // Math: x kept?
        if !dele[x] {
            // Math: new_of[x] := |old|; old := old · [x]
            new_of.push(old.len());
            old.push(x);
        } else {
            // Why: deleted states get a number that is never used.
            new_of.push(usize::MAX);
        }
        // Math: x := x + 1
        x += 1;
    }
    (new_of, old)
}

/// A copy of a list of flags.
fn copy_flags(v: &Vec<bool>) -> (w: Vec<bool>)
    // Math/Why: see each line below.
    ensures
        w@ == v@,
{
    // Math: w = []
    let mut w: Vec<bool> = Vec::new();
    // Math: i = 0
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
        // Math: i := i + 1
        i += 1;
        // Math: w = v[0 .. i-1] (extensionality)
        assert(w@ =~= v@.subrange(0, i as int));
    }
    // Math: w = v
    assert(w@ =~= v@);
    w
}

/// Facts about output position `kp` of the deletion (Python: `trans_ok`/`keep_ok` in
/// delete.py): it lies in the block of output state `s2[kp]`, comes from source position
/// `w[kp]` of the kept state `old[s2[kp]]`, and carries its event and renumbered target.
pub open spec fn out_pos_ok(
    g: &Aut,
    dele: Seq<bool>,
    new_of: Seq<usize>,
    old: Seq<usize>,
    start2: Seq<usize>,
    evt2: Seq<usize>,
    dst2: Seq<usize>,
    w: Seq<int>,
    s2: Seq<int>,
    i: int,
    kp: int,
) -> bool {
    // Math: 0 ≤ s2[kp] < i (the block is finished) or = i (the block being built)
    &&& 0 <= s2[kp] <= i
    // Math: start2[s2[kp]] ≤ kp, and kp < start2[s2[kp] + 1] if that block is finished
    &&& start2[s2[kp]] <= kp
    &&& s2[kp] < i ==> kp < start2[s2[kp] + 1]
    // Math: w[kp] ∈ block(old[s2[kp]])
    &&& g.in_blk(old[s2[kp]] as int, w[kp])
    // Math: evt2[kp] = evt[w[kp]], ¬dele[dst[w[kp]]], dst2[kp] = new_of[dst[w[kp]]]
    &&& evt2[kp] == g.evt@[w[kp]]
    &&& !dele[g.dst@[w[kp]] as int]
    &&& dst2[kp] == new_of[g.dst@[w[kp]] as int]
}

/// The kept transitions, block by block. Returns `start2`, `evt2`, `dst2`, and ghost lists:
/// `w` (source position of each output position), `s2` (its output state), `pos` (output
/// position of each kept source position).
fn build_blocks(g: &Aut, dele: &Vec<bool>, new_of: &Vec<usize>, old: &Vec<usize>) -> (r: (
    Vec<usize>,
    Vec<usize>,
    Vec<usize>,
    Ghost<Seq<int>>,
    Ghost<Seq<int>>,
    Ghost<Seq<int>>,
))
    requires
        // Why: facts restated in each loop (a loop only knows its invariant).
        g.wf(),
        // Math: |dele| = n
        dele@.len() == g.n,
        // Math: renum_ok (restated)
        renum_ok(g, dele@, new_of@, old@),
    // Math/Why: see each line below.
    ensures
        ({
            // Why: names for the parts of the result.
            let (start2, evt2, dst2, w, s2, pos) = r;
            // Math: n' = |old|, the number of kept states
            let n2 = old@.len() as int;
            // Math: start2 cuts the output positions into n' blocks: |start2| = n'+1, start2[0] = 0, start2[n'] = |evt2|, monotone
            &&& start2@.len() == n2 + 1
            &&& start2@[0] == 0
            &&& start2@[n2] == evt2@.len()
            &&& forall|a: int, b: int| 0 <= a <= b <= n2 ==> #[trigger] start2@[a] <= #[trigger] start2@[b]
            // Math: |dst2| = |w| = |s2| = |evt2|
            &&& dst2@.len() == evt2@.len()
            &&& w@.len() == evt2@.len()
            &&& s2@.len() == evt2@.len()
            // Math: ∀ kp: out_pos_ok(kp)  (each output position: its block, source, event, target)
            &&& forall|kp: int| 0 <= kp < evt2@.len() ==> #[trigger] out_pos_ok(g, dele@, new_of@, old@, start2@, evt2@, dst2@, w@, s2@, n2, kp)
            // Math: w is increasing (sources are walked in order)
            // Why: gives sorted output blocks.
            &&& forall|a: int, b: int| 0 <= a < b < evt2@.len() ==> #[trigger] w@[a] < #[trigger] w@[b]
            // Math: ∀ kept i', k ∈ block(old[i']), ¬dele[dst[k]]: pos[k] is an output position of block i' with source k
            // Why: completeness: every kept transition is emitted.
            &&& forall|ii: int, k: int|
                0 <= ii < n2 && #[trigger] g.in_blk(old@[ii] as int, k) && !dele@[g.dst@[k] as int] ==> {
                    let kp = pos@[k];
                    0 <= kp < evt2@.len() && s2@[kp] == ii && w@[kp] == k
                }
        }),
{
    // Math: start2 = [0]; evt2 = dst2 = []
    let mut start2: Vec<usize> = Vec::new();
    start2.push(0);
    let mut evt2: Vec<usize> = Vec::new();
    let mut dst2: Vec<usize> = Vec::new();
    // Math: w = [], s2 = [] (ghost)
    // Why: w[kp]: source position of output position kp; s2[kp]: its output state.
    let ghost mut w: Seq<int> = Seq::empty();
    let ghost mut s2: Seq<int> = Seq::empty();
    // Math: pos = [0] * T (ghost)
    // Why: pos[k]: output position of kept source position k (set when emitted).
    let ghost mut pos: Seq<int> = Seq::new(g.evt@.len(), |k: int| 0);
    // Math: i = 0 (i walks the kept states: blocks 0 .. i-1 are done)
    let mut i: usize = 0;
    while i < old.len()
        invariant
            // Why: facts restated in each loop (a loop only knows its invariant).
            g.wf(),
            // Math: |dele| = n
            dele@.len() == g.n,
            // Math: renum_ok (restated)
            renum_ok(g, dele@, new_of@, old@),
            // Math: 0 ≤ i ≤ n'
            i <= old@.len(),
            // Math: |start2| = i + 1, start2[0] = 0
            start2@.len() == i + 1,
            start2@[0] == 0,
            // Math: start2[i] = |evt2| (block i starts at the end)
            start2@[i as int] == evt2@.len(),
            // Math: start2 is monotone
            forall|a: int, b: int| 0 <= a <= b <= i ==> #[trigger] start2@[a] <= #[trigger] start2@[b],
            // Math: |dst2| = |w| = |s2| = |evt2|, |pos| = T
            dst2@.len() == evt2@.len(),
            w.len() == evt2@.len(),
            s2.len() == evt2@.len(),
            pos.len() == g.evt@.len(),
            // Math: ∀ kp: out_pos_ok(kp) (with i the current block)
            forall|kp: int| 0 <= kp < evt2@.len() ==> #[trigger] out_pos_ok(g, dele@, new_of@, old@, start2@, evt2@, dst2@, w, s2, i as int, kp),
            // Why: every finished output position is before the current block.
            forall|kp: int| 0 <= kp < evt2@.len() ==> #[trigger] s2[kp] < i,
            // Math: w is increasing
            forall|a: int, b: int| 0 <= a < b < evt2@.len() ==> #[trigger] w[a] < #[trigger] w[b],
            // Math: completeness for the kept states done (i' < i)
            forall|ii: int, k: int|
                0 <= ii < i && #[trigger] g.in_blk(old@[ii] as int, k) && !dele@[g.dst@[k] as int] ==> {
                    // Math: kp = pos[k], where it was emitted (completeness)
                    let kp = pos[k];
                    0 <= kp < evt2@.len() && s2[kp] == ii && w[kp] == k
                },
        // Math: n' - i decreases
        decreases old@.len() - i,
    {
        // Math: x = old[i], the kept state whose block is copied
        let x = old[i];
        // Math: x < n (renum_ok)
        assert(old@[i as int] < g.n);
        // Math: [lo, hi) = x's block
        let lo = g.start[x];
        let hi = g.start[x + 1];
        // Math: start[x] ≤ start[x+1] ≤ T
        // Why: hint: the block lies inside evt.
        assert(g.start@[x as int] <= g.start@[x + 1] <= g.start@[g.n as int]);
        // Why: every earlier output position comes from a block of an earlier (smaller) kept
        //      state, so from a position before lo.
        assert forall|kp: int| 0 <= kp < evt2@.len() implies #[trigger] w[kp] < lo by {
            // Math: out_pos_ok(kp): w[kp] ∈ block(old[s2[kp]]), s2[kp] < i
            assert(out_pos_ok(g, dele@, new_of@, old@, start2@, evt2@, dst2@, w, s2, i as int, kp));
            // Math: si = s2[kp]
            let si = s2[kp];
            // Math: old[si] < old[i] = x (old increasing)
            assert(old@[si] < old@[i as int]);
            // Math: w[kp] < start[old[si]+1] ≤ start[x] = lo
            assert(g.start@[old@[si] + 1] <= g.start@[x as int]);
        }
        // Math: k = lo (k walks x's block)
        let mut k = lo;
        while k < hi
            invariant
                // Why: facts restated in each loop (a loop only knows its invariant).
                g.wf(),
                // Math: |dele| = n
                dele@.len() == g.n,
                // Math: renum_ok (restated)
                renum_ok(g, dele@, new_of@, old@),
                // Math: i < n'
                i < old@.len(),
                // Math: x = old[i] < n
                x == old@[i as int],
                x < g.n,
                // Math: [lo, hi) = x's block, inside evt; lo ≤ k ≤ hi
                lo == g.start@[x as int],
                hi == g.start@[x + 1],
                hi <= g.evt@.len(),
                lo <= k <= hi,
                // Math: |start2| = i + 1, start2[0] = 0
                start2@.len() == i + 1,
                start2@[0] == 0,
                // Math: start2[i] ≤ |evt2| (block i is being written)
                start2@[i as int] <= evt2@.len(),
                // Math: start2 is monotone
                forall|a: int, b: int| 0 <= a <= b <= i ==> #[trigger] start2@[a] <= #[trigger] start2@[b],
                // Math: |dst2| = |w| = |s2| = |evt2|, |pos| = T
                dst2@.len() == evt2@.len(),
                w.len() == evt2@.len(),
                s2.len() == evt2@.len(),
                pos.len() == g.evt@.len(),
                // Math: ∀ kp: out_pos_ok(kp) (with i the current block)
                forall|kp: int| 0 <= kp < evt2@.len() ==> #[trigger] out_pos_ok(g, dele@, new_of@, old@, start2@, evt2@, dst2@, w, s2, i as int, kp),
                // Positions of the current block are those from start2[i] on.
                forall|kp: int| 0 <= kp < evt2@.len() ==> (#[trigger] s2[kp] == i <==> start2@[i as int] <= kp),
                // Math: w is increasing
                forall|a: int, b: int| 0 <= a < b < evt2@.len() ==> #[trigger] w[a] < #[trigger] w[b],
                // Math: ∀ kp: w[kp] < k
                // Why: so appending source k keeps w increasing.
                forall|kp: int| 0 <= kp < evt2@.len() ==> #[trigger] w[kp] < k,
                // Math: completeness for the kept states done (i' < i)
                forall|ii: int, kk: int|
                    0 <= ii < i && #[trigger] g.in_blk(old@[ii] as int, kk) && !dele@[g.dst@[kk] as int] ==> {
                        let kp = pos[kk];
                        0 <= kp < evt2@.len() && s2[kp] == ii && w[kp] == kk
                    },
                // Math: ∀ k' ∈ [lo, k): ¬dele[dst[k']] → pos[k'] is its output position
                forall|kk: int|
                    lo <= kk < k && !dele@[#[trigger] g.dst@[kk] as int] ==> {
                        let kp = pos[kk];
                        0 <= kp < evt2@.len() && s2[kp] == i && w[kp] == kk
                    },
            decreases hi - k,
        {
            // Math: y = dst[k]
            let y = g.dst[k];
            // Math: y < n (trans_ok)
            assert(g.dst@[k as int] < g.n);
            // Math: target kept? (then the transition is kept)
            if !dele[y] {
                // Math: kp = |evt2|, the new output position
                let ghost kp = evt2@.len() as int;
                // Why: ghost copies of evt2 and dst2 before the push.
                let ghost e0 = evt2@;
                let ghost d0 = dst2@;
                // Math: e = evt[k]
                let e = g.evt[k];
                // Math: evt2 := evt2 · [e]; dst2 := dst2 · [new_of[y]]
                evt2.push(e);
                dst2.push(new_of[y]);
                proof {
                    // Why: ghost copies to show the old positions keep their facts.
                    let w0 = w;
                    let s20 = s2;
                    let pos0 = pos;
                    // Math: w := w · [k]; s2 := s2 · [i]; pos[k] := kp
                    w = w.push(k as int);
                    s2 = s2.push(i as int);
                    pos = pos.update(k as int, kp);
                    // Math: k ∈ block(x)
                    assert(g.in_blk(x as int, k as int));
                    // Math: ∀ q: out_pos_ok(q) after the push
                    assert forall|q: int| 0 <= q < evt2@.len() implies #[trigger] out_pos_ok(g, dele@, new_of@, old@, start2@, evt2@, dst2@, w, s2, i as int, q) by {
                        if q < kp {
                            // Old position: same facts as before the push.
                            // Math: out_pos_ok(q) before the push
                            assert(out_pos_ok(g, dele@, new_of@, old@, start2@, e0, d0, w0, s20, i as int, q));
                            // Math: w[q], s2[q], evt2[q], dst2[q] unchanged
                            assert(w[q] == w0[q] && s2[q] == s20[q]);
                            assert(evt2@[q] == e0[q] && dst2@[q] == d0[q]);
                        } else {
                            // The new position kp: from source position k of x = old[i].
                            // Math: w[kp] = k, s2[kp] = i, evt2[kp] = e, dst2[kp] = new_of[y]
                            assert(w[q] == k && s2[q] == i);
                            assert(evt2@[q] == e && dst2@[q] == new_of@[y as int]);
                        }
                    }
                    // Math: inner completeness for k + 1: ∀ k' ∈ [lo, k], kept target: pos[k'] is right
                    assert forall|kk: int| lo <= kk <= k && !dele@[#[trigger] g.dst@[kk] as int] implies {
                        let q = pos[kk];
                        0 <= q < evt2@.len() && s2[q] == i && w[q] == kk
                    } by {
                        if kk < k {
                            // Math: pos[k'] unchanged (k' ≠ k)
                            assert(pos[kk] == pos0[kk]);
                            // Math: w at that position unchanged
                            assert(w[pos0[kk]] == w0[pos0[kk]]);
                        }
                    }
                    assert forall|ii: int, kk: int|
                        0 <= ii < i && #[trigger] g.in_blk(old@[ii] as int, kk) && !dele@[g.dst@[kk] as int] implies {
                            let q = pos[kk];
                            0 <= q < evt2@.len() && s2[q] == ii && w[q] == kk
                        } by {
                        // kk is in an earlier block, so kk < lo ≤ k: pos[kk] unchanged.
                        // Math: old[i'] < old[i] = x
                        assert(old@[ii] < old@[i as int]);
                        // Math: block(old[i']) ends before lo, so k' < lo ≤ k
                        assert(g.start@[old@[ii] + 1] <= g.start@[x as int]);
                        // Math: pos[k'] unchanged (k' ≠ k)
                        assert(pos[kk] == pos0[kk]);
                        // Math: w at that position unchanged
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
            assert forall|q: int| 0 <= q < evt2@.len() implies #[trigger] out_pos_ok(g, dele@, new_of@, old@, start2@, evt2@, dst2@, w, s2, i + 1, q) && s2[q] < i + 1 by {
                // Math: out_pos_ok(q) with the old start2
                assert(out_pos_ok(g, dele@, new_of@, old@, st0, evt2@, dst2@, w, s2, i as int, q));
                // Math: start2[s2[q]] unchanged (s2[q] ≤ i)
                assert(start2@[s2[q]] == st0[s2[q]]);
                if s2[q] < i {
                    // Math: start2[s2[q]+1] unchanged (s2[q] < i)
                    assert(start2@[s2[q] + 1] == st0[s2[q] + 1]);
                }
            }
            // Why: all output positions so far belong to blocks 0 .. i (the trigger is s2[q]).
            assert forall|q: int| 0 <= q < evt2@.len() implies #[trigger] s2[q] < i + 1 by {
                // Math: out_pos_ok(q) with the old start2
                assert(out_pos_ok(g, dele@, new_of@, old@, st0, evt2@, dst2@, w, s2, i as int, q));
            }
            // Math: start2 still monotone: the new entry |evt2| ≥ start2[i]
            assert forall|a: int, b: int| 0 <= a <= b <= i + 1 implies #[trigger] start2@[a] <= #[trigger] start2@[b] by {
                if b == i + 1 && a <= i {
                    // Math: start2[a] ≤ start2[i] ≤ |evt2| = start2[i+1]
                    assert(start2@[a] <= start2@[i as int]);
                }
            }
            // Math: completeness now also for i' = i
            assert forall|ii: int, kk: int|
                0 <= ii < i + 1 && #[trigger] g.in_blk(old@[ii] as int, kk) && !dele@[g.dst@[kk] as int] implies {
                    let q = pos[kk];
                    0 <= q < evt2@.len() && s2[q] == ii && w[q] == kk
                } by {
                if ii == i {
                    // Math: k' ∈ [lo, hi) = block(x); the inner invariant at k' (k = hi)
                    assert(lo <= kk < hi);
                }
            }
        }
        // Math: i := i + 1
        i += 1;
    }
    (start2, evt2, dst2, Ghost(w), Ghost(s2), Ghost(pos))
}

/// The empty automaton with the same events as `g` (no states).
fn empty_like(g: &Aut) -> (h: Aut)
    requires
        // Why: facts restated in each loop (a loop only knows its invariant).
        g.wf(),
    // Math/Why: see each line below.
    ensures
        h.wf(),
        h.n == 0,
        h@.m == g@.m,
        h@.E == g@.E,
        h@.Euc == g@.Euc,
        h@.Euo == g@.Euo,
{
    // Math: start = [0] (no states, no transitions)
    let mut start: Vec<usize> = Vec::new();
    start.push(0);
    // Math: h = (n = 0, the same m and event flags, no states)
    let h = Aut {
        n: 0,
        m: g.m,
        in_e: copy_flags(&g.in_e),
        in_euc: copy_flags(&g.in_euc),
        in_euo: copy_flags(&g.in_euo),
        init: Vec::new(),
        marked: Vec::new(),
        start,
        evt: Vec::new(),
        dst: Vec::new(),
    };
    // Math: E' = E, Euc' = Euc, Euo' = Euo (same flags; extensionality)
    assert(h@.E =~= g@.E);
    assert(h@.Euc =~= g@.Euc);
    assert(h@.Euo =~= g@.Euo);
    h
}

/// `G` without the states `x` with `dele[x]`, and without the transitions into or out of
/// them. The kept states keep their flags and order and are renumbered `0, 1, ...`; `old[i]`
/// is the state of `g` that state `i` comes from. If no initial state is kept, the result is
/// the empty automaton (an automaton with states but no initial state is not valid, W3).
pub fn delete_states(g: &Aut, dele: &Vec<bool>) -> (r: (Aut, Vec<usize>))
    requires
        // Why: facts restated in each loop (a loop only knows its invariant).
        g.wf(),
        // Math: |dele| = n
        dele@.len() == g.n,
    // Math/Why: see each line below.
    ensures
        // Math: the result is a valid automaton.
        r.0.wf(),
        // Math: (∃ x ∈ X0, ¬dele[x]) → IsDeletion(G, D, G', old)
        (exists|x: int| 0 <= x < g.n && g.init@[x] && !dele@[x]) ==> is_deletion(g@, del_set(dele@, g.n as int), r.0@, r.1@),
        // Math: otherwise the empty automaton, same events.
        !(exists|x: int| 0 <= x < g.n && g.init@[x] && !dele@[x]) ==> r.0.n == 0 && r.1@.len() == 0
            && r.0@.m == g@.m && r.0@.E == g@.E && r.0@.Euc == g@.Euc && r.0@.Euo == g@.Euo,
{
    // Is some initial state kept?
    // Math: x = 0 (x walks the states)
    let mut x: usize = 0;
    // Math: keep_init = false
    // Why: keep_init: some initial state among 0 .. x-1 is kept.
    let mut keep_init = false;
    while x < g.n
        invariant
            // Why: facts restated in each loop (a loop only knows its invariant).
            g.wf(),
            // Math: |dele| = n
            dele@.len() == g.n,
            // Math: 0 ≤ x ≤ n
            x <= g.n,
            // Math: keep_init ↔ ∃ z < x: init[z] ∧ ¬dele[z]
            keep_init == (exists|z: int| 0 <= z < x && #[trigger] g.init@[z] && !dele@[z]),
        // Math: n - x decreases
        decreases g.n - x,
    {
        // Math: x initial and kept?
        if g.init[x] && !dele[x] {
            keep_init = true;
        }
        // Math: x := x + 1
        x += 1;
    }
    // Math: no initial state kept → the empty automaton (W3)
    if !keep_init {
        return (empty_like(g), Vec::new());
    }
    // Math: x0: a kept initial state (ghost)
    // Why: shows the result has an initial state (W3).
    let ghost x0 = choose|z: int| 0 <= z < g.n && #[trigger] g.init@[z] && !dele@[z];
    // Math: number the kept states
    let (new_of, old) = renumber(g, dele);
    // Math: copy the kept transitions
    let (start2, evt2, dst2, Ghost(w), Ghost(s2), Ghost(pos)) = build_blocks(g, dele, &new_of, &old);
    // Flags of the kept states.
    // Math: init2 = marked2 = []
    let mut init2: Vec<bool> = Vec::new();
    let mut marked2: Vec<bool> = Vec::new();
    // Math: i = 0
    let mut i: usize = 0;
    while i < old.len()
        invariant
            // Why: facts restated in each loop (a loop only knows its invariant).
            g.wf(),
            // Math: renum_ok (restated)
            renum_ok(g, dele@, new_of@, old@),
            // Math: 0 ≤ i ≤ n'
            i <= old@.len(),
            // Math: |init2| = |marked2| = i
            init2@.len() == i,
            marked2@.len() == i,
            // Math: ∀ a < i: init2[a] = init[old[a]], marked2[a] = marked[old[a]]
            forall|a: int| 0 <= a < i ==> #[trigger] init2@[a] == g.init@[old@[a] as int],
            forall|a: int| 0 <= a < i ==> #[trigger] marked2@[a] == g.marked@[old@[a] as int],
        // Math: n' - i decreases
        decreases old@.len() - i,
    {
        // Math: x < n (renum_ok)
        assert(old@[i as int] < g.n);
        // Math: init2 := init2 · [init[old[i]]]; marked2 likewise
        init2.push(g.init[old[i]]);
        marked2.push(g.marked[old[i]]);
        i += 1;
    }
    // Math: h = the kept part (same events)
    let h = Aut {
        n: old.len(),
        m: g.m,
        in_e: copy_flags(&g.in_e),
        in_euc: copy_flags(&g.in_euc),
        in_euo: copy_flags(&g.in_euo),
        init: init2,
        marked: marked2,
        start: start2,
        evt: evt2,
        dst: dst2,
    };
    // Math: n' = |old|
    let ghost n2 = old@.len() as int;
    proof {
        // Output position kp lies in the block of output state s2[kp]: the blocks are
        // consecutive, so it is the only block containing kp.
        // Math: kp ∈ block'(a) → s2[kp] = a
        assert forall|a: int, kp: int| 0 <= a < n2 && #[trigger] h.in_blk(a, kp) implies s2[kp] == a by {
            assert(out_pos_ok(g, dele@, new_of@, old@, h.start@, h.evt@, h.dst@, w, s2, n2, kp));
            // Math: b = s2[kp]; kp ∈ block'(b) (out_pos_ok)
            let b = s2[kp];
            if b < a {
                // Math: b < a: kp < start2[b+1] ≤ start2[a] ≤ kp, impossible
                assert(h.start@[b + 1] <= h.start@[a]);
            } else if b > a {
                // Math: b > a: kp ≥ start2[b] ≥ start2[a+1] > kp, impossible
                assert(h.start@[a + 1] <= h.start@[b]);
            }
        }
        // sorted_ok: positions kp ≤ lp of block a come from source positions w[kp] ≤ w[lp] of
        // the sorted block old[a].
        // Math: ∀ a < n': blk_sorted'(a)
        assert forall|a: int| 0 <= a < n2 implies #[trigger] h.blk_sorted(a) by {
            // Math: block(old[a]) is sorted
            assert(g.blk_sorted(old@[a] as int));
            assert forall|kp: int, lp: int| h.start@[a] <= kp <= lp < h.start@[a + 1] implies #[trigger] h.evt@[kp] <= #[trigger] h.evt@[lp] by {
                // Math: kp, lp ∈ block'(a)
                assert(h.in_blk(a, kp) && h.in_blk(a, lp));
                // Math: both come from block(old[a])
                assert(s2[kp] == a && s2[lp] == a);
                assert(out_pos_ok(g, dele@, new_of@, old@, h.start@, h.evt@, h.dst@, w, s2, n2, kp));
                assert(out_pos_ok(g, dele@, new_of@, old@, h.start@, h.evt@, h.dst@, w, s2, n2, lp));
                if kp < lp {
                    // Math: w[kp] < w[lp] (w increasing), so evt[w[kp]] ≤ evt[w[lp]]
                    assert(w[kp] < w[lp]);
                }
            }
        }
        // trans_ok: events in E, targets renumbered kept states.
        // Math: trans_ok': ∀ kp: evt2[kp] < m ∧ in_e[evt2[kp]] ∧ dst2[kp] < n'
        assert forall|kp: int| 0 <= kp < h.num_trans() implies h.evt@[kp] < h.m && h.in_e@[#[trigger] h.evt@[kp] as int] && h.dst@[kp] < h.n by {
            // Math: w[kp] ∈ block(old[a]), evt[w[kp]] = e, new_of[dst[w[kp]]] = b
            assert(out_pos_ok(g, dele@, new_of@, old@, h.start@, h.evt@, h.dst@, w, s2, n2, kp));
            // Math: evt2[kp] = evt[w[kp]] < m, in E (trans_ok of g)
            assert(g.evt@[w[kp]] < g.m);
            // Math: dst[w[kp]] < n and kept, so dst2[kp] = new_of[...] < n'
            assert(g.dst@[w[kp]] < g.n);
        }
        // Why: the same fact, with the other trigger (dst2[kp]).
        assert forall|kp: int| 0 <= kp < h.num_trans() implies h.evt@[kp] < h.m && h.in_e@[h.evt@[kp] as int] && #[trigger] h.dst@[kp] < h.n by {
            // Why: hint: the instance above.
            assert(h.evt@[kp] < h.m);
        }
        // init_ok: the kept initial state x0 is state new_of[x0].
        // Math: init2[new_of[x0]] = init[x0] = true
        // Why: W3: the result has an initial state.
        assert(h.init@[new_of@[x0] as int]);
        // Math: wf(h)
        assert(h.wf());
        // is_deletion, transitions: j ∈ f'(i, e) ↔ old[j] ∈ f(old[i], e).
        // Math: ∀ a, e, b < n': b ∈ f'(a, e) ↔ old[b] ∈ f(old[a], e)
        assert forall|a: int, e: int, b: int| 0 <= a < n2 && 0 <= b < n2 implies (#[trigger] h@.f(a, e, b) <==> g@.f(old@[a] as int, e, old@[b] as int)) by {
            // Math: →
            if h.trans(a, e, b) {
                // Math: kp: the output position of a --e--> b
                let kp = choose|kp: int| #[trigger] h.in_blk(a, kp) && h.evt@[kp] as int == e && h.dst@[kp] as int == b;
                // Math: s2[kp] = a
                assert(s2[kp] == a);
                assert(out_pos_ok(g, dele@, new_of@, old@, h.start@, h.evt@, h.dst@, w, s2, n2, kp));
                // Math: y = dst[w[kp]] (kept)
                let y = g.dst@[w[kp]] as int;
                assert(y < g.n);
                // Math: old[b] = old[new_of[y]] = y; so old[a] --e--> old[b] by position w[kp]
                assert(old@[new_of@[y] as int] == y);
                assert(g.trans(old@[a] as int, e, old@[b] as int));
            }
            // Math: ←
            if g.trans(old@[a] as int, e, old@[b] as int) {
                // Math: k: the source position
                let k = choose|k: int| #[trigger] g.in_blk(old@[a] as int, k) && g.evt@[k] as int == e && g.dst@[k] as int == old@[b] as int;
                // Math: its target old[b] is kept
                assert(!dele@[g.dst@[k] as int]);
                let kp = pos[k];
                assert(out_pos_ok(g, dele@, new_of@, old@, h.start@, h.evt@, h.dst@, w, s2, n2, kp));
                // Math: kp ∈ block'(a), evt2[kp] = e, dst2[kp] = b
                assert(h.in_blk(a, kp));
                assert(h.trans(a, e, b));
            }
        }
        // is_deletion, range: x is kept ↔ x = old[i] for some i.
        // Math: ∀ z < n: z ∉ D ↔ ∃ a: old[a] = z
        assert forall|z: int| 0 <= z < g.n implies (!del_set(dele@, g.n as int).contains(z) <==> exists|a: int| 0 <= a < n2 && #[trigger] old@[a] as int == z) by {
            if !dele@[z] {
                // Math: z kept: a = new_of[z] is a witness
                assert(old@[new_of@[z] as int] as int == z);
            }
        }
        // Math: E' = E, Euc' = Euc, Euo' = Euo (same flags; extensionality)
        assert(h@.E =~= g@.E);
        assert(h@.Euc =~= g@.Euc);
        assert(h@.Euo =~= g@.Euo);
    }
    (h, old)
}


// =============================================================================================
// accessible, coaccessible, trim
// =============================================================================================

/// The states `x` with `flag[x]`, in increasing order.
pub fn states_with(g: &Aut, flag: &Vec<bool>) -> (s: Vec<usize>)
    requires
        // Why: facts restated in each loop (a loop only knows its invariant).
        g.wf(),
        flag@.len() == g.n,
    // Math/Why: see each line below.
    ensures
        states_in(g, s@),
        // Math: set_of(s) = {x ∈ [0, n) | flag[x]}
        set_of(s@) == ISet::new(|x: int| 0 <= x < g.n && flag@[x]),
{
    // Math: s = []
    let mut s: Vec<usize> = Vec::new();
    proof {
        // Math: set_of([]) = ∅
        lemma_set_of_empty();
    }
    let mut x: usize = 0;
    while x < g.n
        invariant
            // Why: facts restated in each loop (a loop only knows its invariant).
            g.wf(),
            flag@.len() == g.n,
            // Math: 0 ≤ x ≤ n
            x <= g.n,
            // Math: ∀ j: s[j] < x
            forall|j: int| 0 <= j < s@.len() ==> #[trigger] s@[j] < x,
            // Math: set_of(s) = {z < x | flag[z]}
            set_of(s@) == ISet::new(|z: int| 0 <= z < x && flag@[z]),
        // Math: n - x decreases
        decreases g.n - x,
    {
        // Math: flag[x]? then s := s · [x]
        if flag[x] {
            proof {
                // Math: set_of(s · [x]) = set_of(s) ∪ {x}
                lemma_set_of_push(s@, x);
            }
            s.push(x);
        }
        // Math: x := x + 1
        x += 1;
        // Math: set_of(s) = {z < x | flag[z]} (for the new x; extensionality)
        assert(set_of(s@) =~= ISet::new(|z: int| 0 <= z < x && flag@[z]));
    }
    s
}

/// `dele[x]` is true exactly for the states `x` not in `out`.
fn not_in(n: usize, out: &Vec<usize>) -> (dele: Vec<bool>)
    requires
        // Math: ∀ i: out[i] < n
        forall|i: int| 0 <= i < out@.len() ==> #[trigger] out@[i] < n,
    // Math/Why: see each line below.
    ensures
        // Math: |dele| = n
        dele@.len() == n,
        forall|x: int| 0 <= x < n ==> #[trigger] dele@[x] == !set_of(out@).contains(x),
{
    // Math: dele = [true] * n, then out's entries are set to false
    let mut dele: Vec<bool> = Vec::new();
    let mut x: usize = 0;
    while x < n
        invariant
            x <= n,
            dele@.len() == x,
            // Math: ∀ a < x: dele[a]
            forall|a: int| 0 <= a < x ==> #[trigger] dele@[a],
        decreases n - x,
    {
        // Math: dele := dele · [true]
        dele.push(true);
        // Math: x := x + 1
        x += 1;
    }
    let mut i: usize = 0;
    while i < out.len()
        invariant
            // Math: ∀ i: out[i] < n
            forall|i: int| 0 <= i < out@.len() ==> #[trigger] out@[i] < n,
            // Math: 0 ≤ i ≤ |out|
            i <= out@.len(),
            dele@.len() == n,
            // Math: dele[x] ↔ x ∉ {out[0], ..., out[i-1]}
            forall|x: int|
                0 <= x < n ==> #[trigger] dele@[x] == !(exists|j: int| 0 <= j < i && #[trigger] out@[j] as int == x),
        // Math: |out| - i decreases
        decreases out@.len() - i,
    {
        // Math: out[i] < n
        assert(out@[i as int] < n);
        // Math: dele[out[i]] := false
        dele.set(out[i], false);
        i += 1;
    }
    dele
}

/// The accessible part of `g` (Python: `accessible`): `g` without the states that are not
/// reachable from an initial state.
pub fn accessible(g: &Aut) -> (r: (Aut, Vec<usize>))
    requires
        // Why: facts restated in each loop (a loop only knows its invariant).
        g.wf(),
    // Math/Why: see each line below.
    ensures
        r.0.wf(),
        // Math: n > 0 → IsDeletion(G, X \ Ac, G', old)
        g.n > 0 ==> is_deletion(g@, g@.Ac().complement(), r.0@, r.1@),
        // Math: n = 0 → G' is the empty automaton
        g.n == 0 ==> r.0.n == 0 && r.1@.len() == 0,
{
    // Math: s lists X0
    let s = states_with(g, &g.init);
    // Math: set_of(s) = X0
    assert(set_of(s@) =~= g@.X0);
    // Math: set_of(out) = reach(X0) = Ac
    let (out, _par) = crate::ops_aut::reach::reachable(g, &s);
    // Math: dele[x] ↔ x ∉ set_of(out)
    let dele = not_in(g.n, &out);
    // Math: r = G without the states with dele
    let r = delete_states(g, &dele);
    proof {
        // Why: with states, some initial state exists (W3) and is kept.
        if g.n > 0 {
            // Some initial state x0 exists (W3); it is reachable, so it is kept.
            // Math: x0 ∈ X0
            let x0 = choose|x: int| 0 <= x < g.n && #[trigger] g.init@[x];
            // Math: x0 ∈ X0
            assert(g@.X0.contains(x0));
            // Math: x0 ∈ reach(X0) = Ac
            lemma_reach_contains(g@, g@.X0, x0);
            // Math: x0 is kept
            assert(!dele@[x0]);
            // The two descriptions of D agree on the states.
            // Math: on the states, D = {x | dele[x]} is Acᶜ
            // Why: is_deletion only looks at D on the states.
            assert forall|x: int| 0 <= x < g.n implies (del_set(dele@, g.n as int).contains(x) == g@.Ac().complement().contains(x)) by {
                // Math: dele[x] ↔ x ∉ set_of(out)
                assert(dele@[x] == !set_of(out@).contains(x));
            }
        }
    }
    r
}

/// The coaccessible part of `g` (Python: `coaccessible`): `g` without the states from which no
/// marked state can be reached. The empty automaton if no initial state is coaccessible.
pub fn coaccessible(g: &Aut) -> (r: (Aut, Vec<usize>))
    requires
        // Why: facts restated in each loop (a loop only knows its invariant).
        g.wf(),
    // Math/Why: see each line below.
    ensures
        r.0.wf(),
        // Math: X0 ∩ CoAc ≠ ∅ → IsDeletion(G, X \ CoAc, G', old)
        (exists|x: int| g@.X0.contains(x) && #[trigger] g@.CoAc().contains(x)) ==> is_deletion(g@, g@.CoAc().complement(), r.0@, r.1@),
        // Math: otherwise the empty automaton, same events
        !(exists|x: int| g@.X0.contains(x) && #[trigger] g@.CoAc().contains(x)) ==> r.0.n == 0 && r.1@.len() == 0
            && r.0@.m == g@.m && r.0@.E == g@.E && r.0@.Euc == g@.Euc && r.0@.Euo == g@.Euo,
{
    // Math: s lists Xm
    let s = states_with(g, &g.marked);
    // Math: set_of(s) = Xm
    assert(set_of(s@) =~= g@.Xm);
    // Math: set_of(out) = coreach(Xm) = CoAc
    let (out, _nxt) = crate::ops_aut::reach::coreachable(g, &s);
    // Math: dele[x] ↔ x ∉ set_of(out)
    let dele = not_in(g.n, &out);
    // Math: r = G without the states with dele
    let r = delete_states(g, &dele);
    proof {
        // dele[x] ↔ x ∉ CoAc, for every state x.
        // Math: ∀ x < n: dele[x] ↔ x ∉ CoAc
        assert forall|x: int| 0 <= x < g.n implies (#[trigger] dele@[x] == !g@.CoAc().contains(x)) by {
            // Math: dele[x] ↔ x ∉ set_of(out)
            assert(dele@[x] == !set_of(out@).contains(x));
        }
        // "Some initial state is kept" ↔ "X0 ∩ CoAc ≠ ∅".
        // Math: X0 ∩ CoAc ≠ ∅ ?
        if exists|x: int| g@.X0.contains(x) && #[trigger] g@.CoAc().contains(x) {
            // Math: x0 ∈ X0 ∩ CoAc
            let x0 = choose|x: int| g@.X0.contains(x) && #[trigger] g@.CoAc().contains(x);
            // Math: x0 is initial and kept
            assert(g.init@[x0] && !dele@[x0]);
            // Math: on the states, D = CoAcᶜ
            assert forall|x: int| 0 <= x < g.n implies (del_set(dele@, g.n as int).contains(x) == g@.CoAc().complement().contains(x)) by {
                // Math: dele[x] ↔ x ∉ CoAc
                assert(dele@[x] == !g@.CoAc().contains(x));
            }
        } else {
            // Math: otherwise every initial state is deleted (then the result is empty)
            assert forall|x: int| 0 <= x < g.n && #[trigger] g.init@[x] implies dele@[x] by {
                // Math: x ∈ X0, so x ∉ CoAc
                assert(g@.X0.contains(x));
                // Math: dele[x] ↔ x ∉ CoAc
                assert(dele@[x] == !g@.CoAc().contains(x));
            }
        }
    }
    r
}

/// The trim part of `g` (Python: `trim`): `g` without the states that are not both accessible
/// and coaccessible. The empty automaton if no initial state is coaccessible.
pub fn trim(g: &Aut) -> (r: (Aut, Vec<usize>))
    requires
        // Why: facts restated in each loop (a loop only knows its invariant).
        g.wf(),
    // Math/Why: see each line below.
    ensures
        r.0.wf(),
        // Math: X0 ∩ CoAc ≠ ∅ → IsDeletion(G, X \ (Ac ∩ CoAc), G', old)
        (exists|x: int| g@.X0.contains(x) && #[trigger] g@.CoAc().contains(x)) ==> is_deletion(g@, g@.Ac().intersect(g@.CoAc()).complement(), r.0@, r.1@),
        !(exists|x: int| g@.X0.contains(x) && #[trigger] g@.CoAc().contains(x)) ==> r.0.n == 0 && r.1@.len() == 0
            && r.0@.m == g@.m && r.0@.E == g@.E && r.0@.Euc == g@.Euc && r.0@.Euo == g@.Euo,
{
    // Math: s0 lists X0
    let s0 = states_with(g, &g.init);
    // Math: set_of(s0) = X0
    assert(set_of(s0@) =~= g@.X0);
    // Math: set_of(ac) = Ac
    let (ac, _par) = crate::ops_aut::reach::reachable(g, &s0);
    // Math: sm lists Xm
    let sm = states_with(g, &g.marked);
    // Math: set_of(sm) = Xm
    assert(set_of(sm@) =~= g@.Xm);
    // Math: set_of(co) = CoAc
    let (co, _nxt) = crate::ops_aut::reach::coreachable(g, &sm);
    // keep[x]: x is coaccessible; then dele[x]: x is not (accessible and coaccessible).
    // Math: not_co[x] ↔ x ∉ CoAc
    let not_co = not_in(g.n, &co);
    // Math: dele[x] ↔ x ∉ Ac (then the states not in CoAc are added)
    let mut dele = not_in(g.n, &ac);
    let mut x: usize = 0;
    while x < g.n
        invariant
            // Why: facts restated in each loop (a loop only knows its invariant).
            g.wf(),
            // Math: 0 ≤ x ≤ n
            x <= g.n,
            // Math: |dele| = n
            dele@.len() == g.n,
            // Math: |dele| = |not_co| = n
            not_co@.len() == g.n,
            // Math: not_co[z] ↔ z ∉ set_of(co)
            forall|z: int| 0 <= z < g.n ==> #[trigger] not_co@[z] == !set_of(co@).contains(z),
            // Math: dele[z] ↔ z ∉ Ac ∨ (z < x ∧ z ∉ CoAc)
            forall|z: int|
                0 <= z < g.n ==> #[trigger] dele@[z] == (!set_of(ac@).contains(z) || (z < x && !set_of(co@).contains(z))),
        // Math: n - x decreases
        decreases g.n - x,
    {
        // Math: x ∉ CoAc → dele[x] := true
        if not_co[x] {
            dele.set(x, true);
        }
        // Math: x := x + 1
        x += 1;
    }
    // Math: r = G without the states with dele
    let r = delete_states(g, &dele);
    proof {
        // Math: D = (Ac ∩ CoAc)ᶜ
        let D = g@.Ac().intersect(g@.CoAc()).complement();
        // Math: ∀ z < n: dele[z] ↔ z ∈ D
        assert forall|z: int| 0 <= z < g.n implies (#[trigger] dele@[z] == D.contains(z)) by {
            // Math: dele[z] ↔ z ∉ Ac ∨ z ∉ CoAc
            assert(dele@[z] == (!set_of(ac@).contains(z) || !set_of(co@).contains(z)));
        }
        // Math: X0 ∩ CoAc ≠ ∅ ?
        if exists|x: int| g@.X0.contains(x) && #[trigger] g@.CoAc().contains(x) {
            // Math: x0 ∈ X0 ∩ CoAc
            let x0 = choose|x: int| g@.X0.contains(x) && #[trigger] g@.CoAc().contains(x);
            // Math: x0 ∈ reach(X0) = Ac
            lemma_reach_contains(g@, g@.X0, x0);
            // Math: x0 is initial and kept
            assert(g.init@[x0] && !dele@[x0]);
            // Math: on the states, del_set(dele) = D
            assert forall|z: int| 0 <= z < g.n implies (del_set(dele@, g.n as int).contains(z) == D.contains(z)) by {
                // Math: dele[z] ↔ z ∈ D
                assert(dele@[z] == D.contains(z));
            }
        } else {
            // Math: otherwise every initial state is deleted (then the result is empty)
            assert forall|z: int| 0 <= z < g.n && #[trigger] g.init@[z] implies dele@[z] by {
                // Math: z ∈ X0, so z ∉ CoAc, so z ∈ D
                assert(g@.X0.contains(z));
                // Math: dele[z] ↔ z ∈ D
                assert(dele@[z] == D.contains(z));
            }
        }
    }
    r
}

} // verus!
