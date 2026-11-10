//! `next_states` and `active_events`. Python: `ops_aut/verified_ops/basic_ops.py`.
//!
//! Glossary (in addition to `aut.rs` and `check.rs`):
//! - `proof { ... }`: proof steps inside running code; erased when compiled.
//! - `lemma_x(...)`: a call to a proved fact (a `proof fn`); it adds its `ensures` here.
//! - `HashSetWithView<usize>`: Rust's hash set, with a view `seen@`, the mathematical set of
//!   its elements.
//! - `let ghost x = ...`: a value that exists only in the proof.
//! - `choose|x| P(x)`: some `x` with `P(x)` (used after showing one exists).
//! - `assert forall|x| P(x) implies Q(x) by { ... }`: proves `∀ x: P(x) → Q(x)`; the block is
//!   the proof for one arbitrary `x`.
//! - `A =~= B`: `A` and `B` have the same members (then they are equal).

use crate::core_aut::aut::*;
use vstd::hash_set::HashSetWithView;
use vstd::prelude::*;

verus! {

/// The first position of state `x`'s block whose event is at least `e` (binary search).
pub fn lower_bound(g: &Aut, x: usize, e: usize) -> (lo: usize)
    // Math: wf(g) ∧ x < n
    // Why: x names a block, and the block is sorted (wf), which binary search needs.
    requires
        g.wf(),
        x < g.n,
    ensures
        // Math: start[x] ≤ lo ≤ start[x+1]
        // Why: lo is a position of the block, or its end.
        g.start@[x as int] <= lo <= g.start@[x + 1],
        // Math: ∀ k ∈ [start[x], lo): evt[k] < e
        // Why: no transition on e before lo.
        forall|k: int| g.start@[x as int] <= k < lo ==> #[trigger] g.evt@[k] < e,
        // Math: ∀ k ∈ [lo, start[x+1]): evt[k] ≥ e
        // Why: so the transitions on e, if any, start at lo.
        forall|k: int| lo <= k < g.start@[x + 1] ==> #[trigger] g.evt@[k] >= e,
{
    // Math: [a, b) = [start[x], start[x+1])
    // Why: the part of the block not yet decided; at first, the whole block.
    let mut a = g.start[x];
    let mut b = g.start[x + 1];
    // Math: blk_sorted(x)
    // Why: hint: opens sorted_ok at x (used in the loop body).
    assert(g.blk_sorted(x as int));
    // Math: start[x] ≤ start[x+1] ≤ start[n] = T
    // Why: hint: the block lies inside evt, so evt[mid] can be read.
    assert(g.start@[x as int] <= g.start@[x + 1] <= g.start@[g.n as int]);
    while a < b
        invariant
            // Why: facts about g, restated (a loop only knows what its invariant says).
            g.wf(),
            x < g.n,
            g.blk_sorted(x as int),
            g.start@[x + 1] <= g.evt@.len(),
            // Math: start[x] ≤ a ≤ b ≤ start[x+1]
            g.start@[x as int] <= a <= b <= g.start@[x + 1],
            // Math: ∀ k ∈ [start[x], a): evt[k] < e
            // Why: left of a is decided: smaller than e.
            forall|k: int| g.start@[x as int] <= k < a ==> #[trigger] g.evt@[k] < e,
            // Math: ∀ k ∈ [b, start[x+1]): evt[k] ≥ e
            // Why: from b on is decided: at least e.
            forall|k: int| b <= k < g.start@[x + 1] ==> #[trigger] g.evt@[k] >= e,
        // Math: b - a decreases (each step halves the undecided part)
        decreases b - a,
    {
        // Math: mid = a + ⌊(b - a) / 2⌋, so a ≤ mid < b
        // Why: written this way, not (a + b) / 2, so it cannot overflow.
        let mid = a + (b - a) / 2;
        // Math: evt[mid] < e ?
        if g.evt[mid] < e {
            // Math: ∀ k ∈ [start[x], mid]: evt[k] ≤ evt[mid]  (< e)
            // Why: sorted block; so everything up to mid is decided: smaller than e.
            assert(forall|k: int| g.start@[x as int] <= k <= mid ==> #[trigger] g.evt@[k] <= g.evt@[mid as int]);
            // Math: a := mid + 1
            a = mid + 1;
        } else {
            // Math: ∀ k ∈ [mid, start[x+1]): evt[mid] ≤ evt[k]  (and e ≤ evt[mid])
            // Why: sorted block; so everything from mid on is decided: at least e.
            assert(forall|k: int| mid <= k < g.start@[x + 1] ==> g.evt@[mid as int] <= #[trigger] g.evt@[k]);
            // Math: b := mid
            b = mid;
        }
    }
    // Math: a = b, so both parts of the invariant meet at a: the postcondition with lo = a.
    a
}

/// The states reached from `s` by `e`, each once (Lean: `step f S e`), and for each one the
/// index in `s` of a state it is reached from.
pub fn next_states(g: &Aut, s: &Vec<usize>, e: usize) -> (r: (Vec<usize>, Vec<usize>))
    // Math: wf(g) ∧ ∀ j: s[j] < n
    // Why: a valid automaton, and s lists states of it (the binding checks the second part).
    requires
        g.wf(),
        states_in(g, s@),
    ensures
        // Math: set_of(out) = f(set_of(s), e)
        // Why: the result: exactly the states reached by one e (Lean: step f S e).
        set_of(r.0@) == g@.step(set_of(s@), e as int),
        // Math: out has no repeats
        // Why: "each once".
        r.0@.no_duplicates(),
        // Math: |src| = |out|
        r.1@.len() == r.0@.len(),
        // Math: ∀ i: src[i] < |s| ∧ out[i] ∈ f(s[src[i]], e)
        // Why: witnesses: each output state with a state of s it is reached from.
        forall|i: int|
            0 <= i < r.0@.len() ==> #[trigger] r.1@[i] < s@.len() && g@.f(
                s@[r.1@[i] as int] as int,
                e as int,
                r.0@[i] as int,
            ),
{
    // Math: out = [], src = []
    // Why: out: the states found so far; src: their witnesses.
    let mut out: Vec<usize> = Vec::new();
    let mut src: Vec<usize> = Vec::new();
    // Why: usize keys hash as the math says (vstd axiom), required by HashSetWithView::new.
    broadcast use vstd::std_specs::hash::group_hash_axioms;
    // Math: seen = ∅
    // Why: the same states as out, as a hash set, to skip repeats in O(1).
    let mut seen: HashSetWithView<usize> = HashSetWithView::new();
    proof {
        // Math: set_of([]) = ∅
        // Why: so the invariant `seen = set_of(out)` holds at the start.
        lemma_set_of_empty();
    }
    // Math: j = 0
    // Why: j: the states s[0 .. j-1] are done.
    let mut j: usize = 0;
    while j < s.len()
        invariant
            // Why: facts about g and s, restated.
            g.wf(),
            states_in(g, s@),
            // Math: 0 ≤ j ≤ |s|
            j <= s@.len(),
            // Math: ∀ y: y ∈ seen ↔ y ∈ set_of(out)
            // Why: the hash set and the list hold the same states.
            forall|y: usize| seen@.contains(y) == set_of(out@).contains(y as int),
            // Math: out has no repeats
            out@.no_duplicates(),
            // Math: |src| = |out|
            src@.len() == out@.len(),
            // Math: ∀ i: src[i] < j ∧ trans(s[src[i]], e, out[i])
            // Why: soundness so far: every state in out is reached from a done state of s.
            forall|i: int|
                0 <= i < out@.len() ==> #[trigger] src@[i] < j && g.trans(
                    s@[src@[i] as int] as int,
                    e as int,
                    out@[i] as int,
                ),
            // Math: ∀ j' < j, ∀ y: trans(s[j'], e, y) → y ∈ set_of(out)
            // Why: completeness for the states done. Trigger: the transition.
            forall|jj: int, y: int|
                0 <= jj < j && #[trigger] g.trans(s@[jj] as int, e as int, y) ==> set_of(
                    out@,
                ).contains(y),
        // Math: |s| - j decreases
        decreases s@.len() - j,
    {
        // Math: x = s[j]
        let x = s[j];
        // Math: x < n
        // Why: hint: states_in at j; x names a block.
        assert(s@[j as int] < g.n);
        // Math: hi = start[x+1], the end of x's block
        let hi = g.start[x + 1];
        // Math: lo = first position of x's block with event ≥ e
        let lo = lower_bound(g, x, e);
        // Math: start[x+1] ≤ start[n]
        // Why: hint: the block lies inside evt.
        assert(g.start@[x + 1] <= g.start@[g.n as int]);
        // Math: blk_sorted(x)
        // Why: hint: opens sorted_ok at x (used after the inner loop).
        assert(g.blk_sorted(x as int));
        // Math: k = lo
        // Why: k walks the transitions on e: positions lo, lo+1, ... while evt[k] = e.
        let mut k = lo;
        while k < hi && g.evt[k] == e
            invariant
                // Why: facts restated from outside the inner loop.
                g.wf(),
                states_in(g, s@),
                j < s@.len(),
                x == s@[j as int],
                x < g.n,
                g.blk_sorted(x as int),
                hi == g.start@[x + 1],
                hi <= g.evt@.len(),
                // Math: start[x] ≤ lo ≤ k ≤ hi
                g.start@[x as int] <= lo <= k <= hi,
                // Math: ∀ k' ∈ [start[x], lo): evt[k'] < e; ∀ k' ∈ [lo, hi): evt[k'] ≥ e
                // Why: lower_bound's result, restated.
                forall|kk: int| g.start@[x as int] <= kk < lo ==> #[trigger] g.evt@[kk] < e,
                forall|kk: int| lo <= kk < hi ==> #[trigger] g.evt@[kk] >= e,
                // Math: ∀ k' ∈ [lo, k): evt[k'] = e ∧ dst[k'] ∈ set_of(out)
                // Why: the positions walked so far are on e, and their targets are recorded.
                forall|kk: int|
                    lo <= kk < k ==> #[trigger] g.evt@[kk] == e && set_of(out@).contains(
                        g.dst@[kk] as int,
                    ),
                // Why: the outer invariant, with "src[i] ≤ j" (state j is being done).
                forall|y: usize| seen@.contains(y) == set_of(out@).contains(y as int),
                out@.no_duplicates(),
                src@.len() == out@.len(),
                forall|i: int|
                    0 <= i < out@.len() ==> #[trigger] src@[i] <= j && g.trans(
                        s@[src@[i] as int] as int,
                        e as int,
                        out@[i] as int,
                    ),
                forall|jj: int, y: int|
                    0 <= jj < j && #[trigger] g.trans(s@[jj] as int, e as int, y) ==> set_of(
                        out@,
                    ).contains(y),
            // Math: hi - k decreases
            decreases hi - k,
        {
            // Math: y = dst[k]
            let y = g.dst[k];
            // Math: start[x] ≤ k < start[x+1]
            // Why: hint: names position k as the witness of the transition below.
            assert(g.in_blk(x as int, k as int));
            // Math: x --e--> y
            // Why: hint: needed for the soundness invariant of the new entry.
            assert(g.trans(x as int, e as int, y as int));
            // Math: seen := seen ∪ {y}; the call returns true ↔ y ∉ seen before
            if seen.insert(y) {
                proof {
                    // Math: y ∉ set_of(out), so out · [y] has no repeats
                    lemma_no_dup_push(out@, y);
                    // Math: set_of(out · [y]) = set_of(out) ∪ {y}
                    // Why: keeps `seen = set_of(out)` after both grow by y.
                    lemma_set_of_push(out@, y);
                }
                // Math: out := out · [y]; src := src · [j]
                out.push(y);
                src.push(j);
            }
            // Math: k := k + 1
            k += 1;
        }
        // Math: ∀ y: trans(x, e, y) → y ∈ set_of(out)
        // Why: completeness for j. The positions with event e are exactly [lo, k): before lo
        //      the event is smaller; from k on it is larger (k = hi, or evt[k] ≠ e and
        //      evt[k] ≥ e, then sorted).
        assert forall|y: int| #[trigger] g.trans(x as int, e as int, y) implies set_of(out@).contains(y) by {
            // Math: kk: a position of x's block with evt[kk] = e, dst[kk] = y
            let kk = choose|kk: int| #[trigger] g.in_blk(x as int, kk) && g.evt@[kk] as int == e
                && g.dst@[kk] as int == y;
            if kk >= k {
                // Math: evt[k] ≤ evt[kk] = e
                // Why: sorted; with evt[k] ≥ e this gives evt[k] = e, but the loop stopped at
                //      k, so kk ≥ k is impossible and kk ∈ [lo, k).
                assert(g.evt@[k as int] <= g.evt@[kk]);
            }
        }
        // Math: j := j + 1
        j += 1;
    }
    // Math: ∀ y: y ∈ set_of(out) ↔ y ∈ f(set_of(s), e)
    // Why: the two inclusions; then equality by extensionality below.
    assert forall|y: int| set_of(out@).contains(y) == g@.step(set_of(s@), e as int).contains(y) by {
        // →: out[i] is reached from s[src[i]].
        if set_of(out@).contains(y) {
            // Math: i with out[i] = y
            let i = choose|i: int| 0 <= i < out@.len() && #[trigger] out@[i] as int == y;
            // Math: jj = src[i]
            let jj = src@[i] as int;
            // Math: s[jj] ∈ set_of(s)
            // Why: hint: the witness x = s[jj] of step's ∃.
            assert(set_of(s@).contains(s@[jj] as int));
            // Math: y ∈ f(s[jj], e)
            assert(g@.f(s@[jj] as int, e as int, y));
        }
        // ←: y is reached from some x = s[jj]; completeness for jj.
        if g@.step(set_of(s@), e as int).contains(y) {
            // Math: x ∈ set_of(s) with y ∈ f(x, e)
            let x = choose|x: int| #[trigger] set_of(s@).contains(x) && g@.f(x, e as int, y);
            // Math: jj with s[jj] = x
            let jj = choose|jj: int| 0 <= jj < s@.len() && #[trigger] s@[jj] as int == x;
            // Math: trans(s[jj], e, y)
            // Why: hint: the trigger of the completeness invariant.
            assert(g.trans(s@[jj] as int, e as int, y));
        }
    }
    // Math: set_of(out) = f(set_of(s), e)
    // Why: same members, so equal (extensionality).
    assert(set_of(out@) =~= g@.step(set_of(s@), e as int));
    // Math: ∀ i: src[i] < |s| ∧ out[i] ∈ f(s[src[i]], e)
    // Why: hint: the witness facts in view form (f is trans through the view's delta).
    assert forall|i: int| 0 <= i < out@.len() implies #[trigger] src@[i] < s@.len() && g@.f(
        s@[src@[i] as int] as int,
        e as int,
        out@[i] as int,
    ) by {}
    (out, src)
}

/// The events enabled at some state of `s`, each once (Lean: `active f S`), and for each one
/// the index in `s` of a state where it is enabled. For one state, in increasing event number.
pub fn active_events(g: &Aut, s: &Vec<usize>) -> (r: (Vec<usize>, Vec<usize>))
    // Math: wf(g) ∧ ∀ j: s[j] < n
    requires
        g.wf(),
        states_in(g, s@),
    ensures
        // Math: set_of(out) = active(set_of(s))
        // Why: the result (Lean: active f S).
        set_of(r.0@) == g@.active(set_of(s@)),
        // Math: out has no repeats
        r.0@.no_duplicates(),
        // Math: |src| = |out|
        r.1@.len() == r.0@.len(),
        // Math: ∀ i: src[i] < |s| ∧ ∃ y: y ∈ f(s[src[i]], out[i])
        // Why: witnesses: each event with a state of s where it is enabled.
        forall|i: int|
            0 <= i < r.0@.len() ==> #[trigger] r.1@[i] < s@.len() && exists|y: int|
                g@.f(s@[r.1@[i] as int] as int, r.0@[i] as int, y),
{
    // Math: out = [], src = []
    let mut out: Vec<usize> = Vec::new();
    let mut src: Vec<usize> = Vec::new();
    // Math: mark = [false] * m
    // Why: mark[e]: event e is already in out. One flag per event number (m: alphabet size).
    let mut mark: Vec<bool> = Vec::new();
    // Math: i = 0
    let mut i: usize = 0;
    while i < g.m
        invariant
            // Math: 0 ≤ i ≤ m ∧ |mark| = i ∧ ∀ a < i: ¬mark[a]
            i <= g.m,
            mark@.len() == i,
            forall|a: int| 0 <= a < i ==> !#[trigger] mark@[a],
        // Math: m - i decreases
        decreases g.m - i,
    {
        // Math: mark := mark · [false]; i := i + 1
        mark.push(false);
        i += 1;
    }
    proof {
        // Math: set_of([]) = ∅
        // Why: so `mark[a] ↔ a ∈ set_of(out)` holds at the start.
        lemma_set_of_empty();
    }
    // Math: j = 0
    // Why: j: the states s[0 .. j-1] are done.
    let mut j: usize = 0;
    while j < s.len()
        invariant
            // Why: facts about g and s, restated.
            g.wf(),
            states_in(g, s@),
            j <= s@.len(),
            mark@.len() == g.m,
            // Math: ∀ a ∈ [0, m): mark[a] ↔ a ∈ set_of(out)
            forall|a: int| 0 <= a < g.m ==> #[trigger] mark@[a] == set_of(out@).contains(a),
            // Math: ∀ i: out[i] < m
            // Why: so mark[out[i]] can be read.
            forall|i: int| 0 <= i < out@.len() ==> #[trigger] out@[i] < g.m,
            // Math: out has no repeats; |src| = |out|
            out@.no_duplicates(),
            src@.len() == out@.len(),
            // Math: ∀ i: src[i] < j ∧ ∃ y: trans(s[src[i]], out[i], y)
            // Why: soundness so far.
            forall|i: int|
                0 <= i < out@.len() ==> #[trigger] src@[i] < j && exists|y: int|
                    g.trans(s@[src@[i] as int] as int, out@[i] as int, y),
            // Math: ∀ j' < j, a, y: trans(s[j'], a, y) → a ∈ set_of(out)
            // Why: completeness for the states done.
            forall|jj: int, a: int, y: int|
                0 <= jj < j && #[trigger] g.trans(s@[jj] as int, a, y) ==> set_of(out@).contains(a),
        // Math: |s| - j decreases
        decreases s@.len() - j,
    {
        // Math: x = s[j]
        let x = s[j];
        // Math: x < n
        // Why: hint: states_in at j.
        assert(s@[j as int] < g.n);
        // Math: [lo, hi) = x's block
        let lo = g.start[x];
        let hi = g.start[x + 1];
        // Math: start[x] ≤ start[x+1] ≤ start[n]
        // Why: hint: the block lies inside evt.
        assert(g.start@[x as int] <= g.start@[x + 1] <= g.start@[g.n as int]);
        // Math: k = lo
        // Why: k walks x's whole block.
        let mut k = lo;
        while k < hi
            invariant
                // Why: facts restated from outside the inner loop.
                g.wf(),
                states_in(g, s@),
                j < s@.len(),
                x == s@[j as int],
                x < g.n,
                lo == g.start@[x as int],
                hi == g.start@[x + 1],
                hi <= g.evt@.len(),
                // Math: lo ≤ k ≤ hi
                lo <= k <= hi,
                mark@.len() == g.m,
                // Math: ∀ k' ∈ [lo, k): evt[k'] ∈ set_of(out)
                // Why: the events of the positions walked are recorded.
                forall|kk: int| lo <= kk < k ==> set_of(out@).contains(#[trigger] g.evt@[kk] as int),
                // Why: the outer invariant, with "src[i] ≤ j".
                forall|a: int| 0 <= a < g.m ==> #[trigger] mark@[a] == set_of(out@).contains(a),
                forall|i: int| 0 <= i < out@.len() ==> #[trigger] out@[i] < g.m,
                out@.no_duplicates(),
                src@.len() == out@.len(),
                forall|i: int|
                    0 <= i < out@.len() ==> #[trigger] src@[i] <= j && exists|y: int|
                        g.trans(s@[src@[i] as int] as int, out@[i] as int, y),
                forall|jj: int, a: int, y: int|
                    0 <= jj < j && #[trigger] g.trans(s@[jj] as int, a, y) ==> set_of(out@).contains(a),
            // Math: hi - k decreases
            decreases hi - k,
        {
            // Math: a = evt[k]
            let a = g.evt[k];
            // Math: a < m
            // Why: hint: trans_ok at k; so mark[a] can be read.
            assert(g.evt@[k as int] < g.m);
            // Math: a ∉ set_of(out) ?
            if !mark[a] {
                // Math: start[x] ≤ k < start[x+1]
                // Why: hint: names position k as the witness.
                assert(g.in_blk(x as int, k as int));
                // Math: x --a--> dst[k]
                // Why: hint: a is enabled at x.
                assert(g.trans(x as int, a as int, g.dst@[k as int] as int));
                proof {
                    // Math: out · [a] has no repeats; set_of(out · [a]) = set_of(out) ∪ {a}
                    lemma_no_dup_push(out@, a);
                    lemma_set_of_push(out@, a);
                }
                // Why: ghost copies of out and src before the push, to name the old entries.
                let ghost out0 = out@;
                let ghost src0 = src@;
                // Math: mark[a] := true; out := out · [a]; src := src · [j]
                mark.set(a, true);
                out.push(a);
                src.push(j);
                // Math: ∀ i: src[i] ≤ j ∧ ∃ y: trans(s[src[i]], out[i], y)
                // Why: hint: each witness carries over (old entries unchanged; the new one is
                //      a at x, with target dst[k]).
                assert forall|i: int| 0 <= i < out@.len() implies #[trigger] src@[i] <= j
                    && exists|y: int| g.trans(s@[src@[i] as int] as int, out@[i] as int, y) by {
                    if i < out0.len() {
                        // Math: out[i] = out0[i], src[i] = src0[i]
                        assert(out@[i] == out0[i] && src@[i] == src0[i]);
                    } else {
                        // Math: the new entry: y = dst[k]
                        assert(g.trans(s@[src@[i] as int] as int, out@[i] as int, g.dst@[k as int] as int));
                    }
                }
            }
            // Math: k := k + 1
            k += 1;
        }
        // Math: ∀ a, y: trans(x, a, y) → a ∈ set_of(out)
        // Why: completeness for j: every position of x's block was walked.
        assert forall|a: int, y: int| #[trigger] g.trans(x as int, a, y) implies set_of(out@).contains(a) by {
            // Math: kk: a position of x's block with evt[kk] = a
            let kk = choose|kk: int| #[trigger] g.in_blk(x as int, kk) && g.evt@[kk] as int == a
                && g.dst@[kk] as int == y;
            // Math: lo ≤ kk < k (= hi)
            assert(lo <= kk < k);
            // Math: evt[kk] ∈ set_of(out)
            // Why: hint: the inner invariant at kk.
            assert(set_of(out@).contains(g.evt@[kk] as int));
        }
        // Math: j := j + 1
        j += 1;
    }
    // Math: ∀ a: a ∈ set_of(out) ↔ a ∈ active(set_of(s))
    // Why: the two inclusions; then equality by extensionality below.
    assert forall|a: int| set_of(out@).contains(a) == g@.active(set_of(s@)).contains(a) by {
        // →: out[i] is enabled at s[src[i]].
        if set_of(out@).contains(a) {
            // Math: i with out[i] = a; jj = src[i]; y: a target of a from s[jj]
            let i = choose|i: int| 0 <= i < out@.len() && #[trigger] out@[i] as int == a;
            let jj = src@[i] as int;
            let y = choose|y: int| g.trans(s@[jj] as int, out@[i] as int, y);
            // Why: hints: the witnesses x = s[jj] and y of active's ∃.
            assert(set_of(s@).contains(s@[jj] as int));
            assert(g@.f(s@[jj] as int, a, y));
        }
        // ←: a is enabled at some x = s[jj]; completeness for jj.
        if g@.active(set_of(s@)).contains(a) {
            // Math: x ∈ set_of(s), y ∈ f(x, a); jj with s[jj] = x
            let (x, y) = choose|x: int, y: int| #[trigger] set_of(s@).contains(x) && #[trigger] g@.f(x, a, y);
            let jj = choose|jj: int| 0 <= jj < s@.len() && #[trigger] s@[jj] as int == x;
            // Why: hint: the trigger of the completeness invariant.
            assert(g.trans(s@[jj] as int, a, y));
        }
    }
    // Math: set_of(out) = active(set_of(s))
    assert(set_of(out@) =~= g@.active(set_of(s@)));
    // Math: ∀ i: src[i] < |s| ∧ ∃ y: y ∈ f(s[src[i]], out[i])
    // Why: the witness facts in view form.
    assert forall|i: int| 0 <= i < out@.len() implies #[trigger] src@[i] < s@.len() && exists|y: int|
        g@.f(s@[src@[i] as int] as int, out@[i] as int, y) by {
        // Math: y: a target (from the invariant); then y ∈ f(...) in the view
        let y = choose|y: int| g.trans(s@[src@[i] as int] as int, out@[i] as int, y);
        assert(g@.f(s@[src@[i] as int] as int, out@[i] as int, y));
    }
    (out, src)
}

} // verus!
