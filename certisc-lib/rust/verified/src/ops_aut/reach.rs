//! `reachable` and `coreachable`. Python: `ops_aut/verified_ops/reach.py`, `coreach.py`.
//!
//! Unlike Nagini, the contracts state the Lean result itself (`set_of(out) = reach(S)`), not
//! only a certificate: the certificate lemmas of Automaton.lean (R1, R2, C1, C2) are proved
//! here too, by induction (recursive `proof fn`s with `decreases`).
//!
//! Glossary (in addition to `aut.rs`, `check.rs`, `basic_ops.rs`):
//! - `Option<(usize, usize)>`: `None`, or `Some((p, e))`, a pair of numbers.
//! - `seq![a]`: the one-element sequence `[a]`; `s.push(a)`: `s · [a]`; `s + t`: concatenation.
//! - `choose|x| P(x)`: some `x` with `P(x)` (used after showing one exists).
//! - `s.last()`: `s[|s| - 1]`.

use crate::core_aut::aut::*;
use vstd::prelude::*;
// Why: used only by proofs (erased in a plain build).
#[allow(unused_imports)]
use vstd::set_lib::*;

verus! {

// =============================================================================================
// Certificates (Automaton.lean: reach_eq_of_certificate, coreach_eq_of_certificate)
// =============================================================================================

/// `R` is closed under the transitions (Lean: `Closed f R`).
pub open spec fn closed(v: AutView, R: ISet<int>) -> bool {
    // Math: ∀ x ∈ R, ∀ e, y: y ∈ f(x, e) → y ∈ R
    forall|x: int, e: int, y: int| R.contains(x) && #[trigger] v.f(x, e, y) ==> R.contains(y)
}

/// `R` is closed backwards (Lean: `BackClosed f R`).
pub open spec fn back_closed(v: AutView, R: ISet<int>) -> bool {
    // Math: ∀ y ∈ R, ∀ x, e: y ∈ f(x, e) → x ∈ R
    forall|x: int, e: int, y: int| R.contains(y) && #[trigger] v.f(x, e, y) ==> R.contains(x)
}

/// A run that starts in a closed set stays in it, up to step `i`.
proof fn lemma_run_stays(v: AutView, R: ISet<int>, xs: Seq<int>, w: Seq<int>, i: int)
    // Math: is_run(xs, w) ∧ closed(R) ∧ xs[0] ∈ R ∧ 0 ≤ i ≤ |w|
    requires
        v.is_run(xs, w),
        closed(v, R),
        R.contains(xs[0]),
        0 <= i <= w.len(),
    // Math: xs[i] ∈ R
    ensures
        R.contains(xs[i]),
    // Why: induction on i.
    decreases i,
{
    if i > 0 {
        // Induction hypothesis: xs[i-1] ∈ R.
        lemma_run_stays(v, R, xs, w, i - 1);
        // Math: xs[i] ∈ f(xs[i-1], w[i-1]); closed gives xs[i] ∈ R.
        assert(v.f(xs[i - 1], w[i - 1], xs[i]));
    }
}

/// A run that ends in a backward-closed set was in it from step `i` on.
proof fn lemma_run_back(v: AutView, R: ISet<int>, xs: Seq<int>, w: Seq<int>, i: int)
    // Math: is_run(xs, w) ∧ back_closed(R) ∧ xs[|w|] ∈ R ∧ 0 ≤ i ≤ |w|
    requires
        v.is_run(xs, w),
        back_closed(v, R),
        R.contains(xs[w.len() as int]),
        0 <= i <= w.len(),
    // Math: xs[i] ∈ R
    ensures
        R.contains(xs[i]),
    // Why: induction on |w| - i (from the end backwards).
    decreases w.len() - i,
{
    if i < w.len() {
        // Induction hypothesis: xs[i+1] ∈ R.
        lemma_run_back(v, R, xs, w, i + 1);
        // Math: xs[i+1] ∈ f(xs[i], w[i]); back_closed gives xs[i] ∈ R.
        assert(v.f(xs[i], w[i], xs[i + 1]));
    }
}

/// R1: a closed set that contains `S` contains every state reachable from `S`
/// (Lean: `reach_subset_of_closed`).
pub proof fn lemma_reach_subset(v: AutView, S: ISet<int>, R: ISet<int>)
    // Math: S ⊆ R ∧ closed(R)
    requires
        forall|x: int| S.contains(x) ==> R.contains(x),
        closed(v, R),
    // Math: reach(S) ⊆ R
    ensures
        forall|y: int| v.reach(S).contains(y) ==> R.contains(y),
{
    assert forall|y: int| v.reach(S).contains(y) implies R.contains(y) by {
        // A run from S to y.
        let (xs, w) = choose|xs: Seq<int>, w: Seq<int>|
            #[trigger] v.is_run(xs, w) && S.contains(xs[0]) && xs.last() == y;
        // Its last state, xs[|w|] = y, is in R.
        lemma_run_stays(v, R, xs, w, w.len() as int);
    }
}

/// C1: a backward-closed set that contains `S` contains every state that reaches `S`
/// (Lean: `coreach_subset_of_closed`).
pub proof fn lemma_coreach_subset(v: AutView, S: ISet<int>, R: ISet<int>)
    // Math: S ⊆ R ∧ back_closed(R)
    requires
        forall|x: int| S.contains(x) ==> R.contains(x),
        back_closed(v, R),
    // Math: coreach(S) ⊆ R
    ensures
        forall|x: int| v.coreach(S).contains(x) ==> R.contains(x),
{
    assert forall|x: int| v.coreach(S).contains(x) implies R.contains(x) by {
        // A run from x to S.
        let (xs, w) = choose|xs: Seq<int>, w: Seq<int>|
            #[trigger] v.is_run(xs, w) && xs[0] == x && S.contains(xs.last());
        // Its first state, xs[0] = x, is in R.
        lemma_run_back(v, R, xs, w, 0);
    }
}

/// The witness of entry `i` of a `reachable` result: a start state, or reached from an
/// earlier entry.
pub open spec fn reach_wit(
    v: AutView,
    S: ISet<int>,
    out: Seq<usize>,
    par: Seq<Option<(usize, usize)>>,
    i: int,
) -> bool {
    match par[i] {
        // Math: par[i] = None → out[i] ∈ S
        Option::None => S.contains(out[i] as int),
        // Math: par[i] = (p, e) → p < i ∧ out[i] ∈ f(out[p], e)
        Option::Some((p, e)) => p < i && v.f(out[p as int] as int, e as int, out[i] as int),
    }
}

/// The witness of entry `i` of a `coreachable` result: a target state, or leads to an
/// earlier entry.
pub open spec fn coreach_wit(
    v: AutView,
    S: ISet<int>,
    out: Seq<usize>,
    nxt: Seq<Option<(usize, usize)>>,
    i: int,
) -> bool {
    match nxt[i] {
        // Math: nxt[i] = None → out[i] ∈ S
        Option::None => S.contains(out[i] as int),
        // Math: nxt[i] = (p, e) → p < i ∧ out[p] ∈ f(out[i], e)
        Option::Some((p, e)) => p < i && v.f(out[i] as int, e as int, out[p as int] as int),
    }
}

/// R2: every entry with witnesses is reachable (Lean: `mem_reach_of_witness`).
pub proof fn lemma_wit_reach(
    v: AutView,
    S: ISet<int>,
    out: Seq<usize>,
    par: Seq<Option<(usize, usize)>>,
    i: int,
)
    // Math: ∀ j < |out|: reach_wit(j) ∧ 0 ≤ i < |out|
    requires
        par.len() == out.len(),
        forall|j: int| 0 <= j < out.len() ==> #[trigger] reach_wit(v, S, out, par, j),
        0 <= i < out.len(),
    // Math: out[i] ∈ reach(S)
    ensures
        v.reach(S).contains(out[i] as int),
    // Why: strong induction on i (the parent p is smaller).
    decreases i,
{
    // Why: open the witness of i.
    assert(reach_wit(v, S, out, par, i));
    match par[i] {
        Option::None => {
            // The run [out[i]] of the empty word.
            let xs = seq![out[i] as int];
            let w = Seq::<int>::empty();
            // Why: hint: the witness (xs, w) of reach's ∃.
            assert(v.is_run(xs, w));
            assert(xs.last() == out[i] as int);
        },
        Option::Some((p, e)) => {
            // Induction hypothesis: a run from S to out[p].
            lemma_wit_reach(v, S, out, par, p as int);
            let (xs, w) = choose|xs: Seq<int>, w: Seq<int>|
                #[trigger] v.is_run(xs, w) && S.contains(xs[0]) && xs.last() == out[p as int] as int;
            // Extend it by out[p] --e--> out[i].
            let xs2 = xs.push(out[i] as int);
            let w2 = w.push(e as int);
            assert forall|k: int| 0 <= k < w2.len() implies v.f(xs2[k], #[trigger] w2[k], xs2[k + 1]) by {
                if k < w.len() {
                    // Old steps: unchanged.
                    assert(xs2[k] == xs[k] && xs2[k + 1] == xs[k + 1] && w2[k] == w[k]);
                } else {
                    // The new step: from the old last state.
                    assert(xs2[k] == xs.last());
                }
            }
            assert(v.is_run(xs2, w2));
            assert(xs2[0] == xs[0]);
            assert(xs2.last() == out[i] as int);
        },
    }
}

/// C2: every entry with witnesses reaches `S` (Lean: `mem_coreach_of_witness`).
pub proof fn lemma_wit_coreach(
    v: AutView,
    S: ISet<int>,
    out: Seq<usize>,
    nxt: Seq<Option<(usize, usize)>>,
    i: int,
)
    requires
        nxt.len() == out.len(),
        forall|j: int| 0 <= j < out.len() ==> #[trigger] coreach_wit(v, S, out, nxt, j),
        0 <= i < out.len(),
    // Math: out[i] ∈ coreach(S)
    ensures
        v.coreach(S).contains(out[i] as int),
    decreases i,
{
    assert(coreach_wit(v, S, out, nxt, i));
    match nxt[i] {
        Option::None => {
            let xs = seq![out[i] as int];
            let w = Seq::<int>::empty();
            assert(v.is_run(xs, w));
            assert(xs.last() == out[i] as int);
        },
        Option::Some((p, e)) => {
            // Induction hypothesis: a run from out[p] to S.
            lemma_wit_coreach(v, S, out, nxt, p as int);
            let (xs, w) = choose|xs: Seq<int>, w: Seq<int>|
                #[trigger] v.is_run(xs, w) && xs[0] == out[p as int] as int && S.contains(xs.last());
            // Put out[i] --e--> out[p] in front.
            let xs2 = seq![out[i] as int] + xs;
            let w2 = seq![e as int] + w;
            assert forall|k: int| 0 <= k < w2.len() implies v.f(xs2[k], #[trigger] w2[k], xs2[k + 1]) by {
                if k > 0 {
                    // Old steps, shifted by one.
                    assert(xs2[k] == xs[k - 1] && xs2[k + 1] == xs[k] && w2[k] == w[k - 1]);
                } else {
                    assert(xs2[0] == out[i] as int && xs2[1] == xs[0] && w2[0] == e as int);
                }
            }
            assert(v.is_run(xs2, w2));
            assert(xs2.last() == xs.last());
        },
    }
}

/// A list without repeats of numbers below `n` has at most `n` entries.
pub proof fn lemma_len_bound(s: Seq<usize>, n: int)
    // Math: s has no repeats ∧ ∀ i: s[i] < n ∧ n ≥ 0
    requires
        s.no_duplicates(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] < n,
        n >= 0,
    // Math: |s| ≤ n
    ensures
        s.len() <= n,
{
    // t: the same list as mathematical integers.
    // Math: t = [s[0], ..., s[|s|-1]] as integers
    // Why: the vstd set lemmas below are about Set<int>.
    let t = s.map_values(|v: usize| v as int);
    // Math: ∀ i ≠ j: t[i] ≠ t[j]
    // Why: t has no repeats because s has none.
    assert forall|i: int, j: int| 0 <= i < t.len() && 0 <= j < t.len() && i != j implies t[i]
        != t[j] by {
        // Math: s[i] ≠ s[j] (no repeats in s)
        assert(s[i] != s[j]);
    }
    // Math: t has no repeats
    assert(t.no_duplicates());
    // Math: |t| = |set(t)| (no repeats) and set(t) ⊆ [0, n), which has n elements.
    // Math: |t| = |set(t)| (vstd: a list without repeats has as many elements as its set)
    t.unique_seq_to_set();
    // Math: |[0, n)| = n (vstd)
    lemma_int_range(0, n);
    // Math: set(t) ⊆ [0, n)
    assert forall|x: int| t.to_set().contains(x) implies set_int_range(0, n).contains(x) by {
        // Math: i with t[i] = x
        let i = choose|i: int| 0 <= i < t.len() && t[i] == x;
        // Math: x = s[i] < n
        assert(s[i] < n);
    }
    // Math: |set(t)| ≤ |[0, n)| = n, so |s| = |t| ≤ n
    lemma_len_subset(t.to_set(), set_int_range(0, n));
}

/// A state of `S` is reachable from `S` (by the empty word; Lean: `mem_reach_of_mem`).
pub proof fn lemma_reach_contains(v: AutView, S: ISet<int>, x: int)
    requires
        S.contains(x),
    ensures
        v.reach(S).contains(x),
{
    // The run [x] of the empty word.
    // Math: xs = [x], w = []: the run of the empty word from x
    let xs = seq![x];
    let w = Seq::<int>::empty();
    assert(v.is_run(xs, w));
    // Math: last(xs) = x
    assert(xs.last() == x);
}

/// After appending an entry with its witness, all witnesses still hold (reach).
proof fn lemma_reach_wit_push(
    v: AutView,
    S: ISet<int>,
    out: Seq<usize>,
    par: Seq<Option<(usize, usize)>>,
    y: usize,
    q: Option<(usize, usize)>,
)
    requires
        par.len() == out.len(),
        forall|j: int| 0 <= j < out.len() ==> #[trigger] reach_wit(v, S, out, par, j),
        reach_wit(v, S, out.push(y), par.push(q), out.len() as int),
    ensures
        forall|j: int|
            0 <= j < out.len() + 1 ==> #[trigger] reach_wit(v, S, out.push(y), par.push(q), j),
{
    assert forall|j: int| 0 <= j < out.len() + 1 implies #[trigger] reach_wit(
        v,
        S,
        out.push(y),
        par.push(q),
        j,
    ) by {
        // Math: j < |out|: an old entry
        // Why: entries before the new one keep their witness.
        if j < out.len() {
            // Old entries and their parents (p < j) are unchanged.
            // Math: the old witness of j
            assert(reach_wit(v, S, out, par, j));
            // Math: (out · [y])[j] = out[j], (par · [q])[j] = par[j]
            assert(out.push(y)[j] == out[j] && par.push(q)[j] == par[j]);
            if let Option::Some((p, e)) = par[j] {
                // Math: (out · [y])[p] = out[p] (p < j < |out|)
                // Why: the parent/next entry is old too.
                assert(out.push(y)[p as int] == out[p as int]);
            }
        }
    }
}

/// After appending an entry with its witness, all witnesses still hold (coreach).
proof fn lemma_coreach_wit_push(
    v: AutView,
    S: ISet<int>,
    out: Seq<usize>,
    nxt: Seq<Option<(usize, usize)>>,
    y: usize,
    q: Option<(usize, usize)>,
)
    requires
        nxt.len() == out.len(),
        forall|j: int| 0 <= j < out.len() ==> #[trigger] coreach_wit(v, S, out, nxt, j),
        coreach_wit(v, S, out.push(y), nxt.push(q), out.len() as int),
    ensures
        forall|j: int|
            0 <= j < out.len() + 1 ==> #[trigger] coreach_wit(v, S, out.push(y), nxt.push(q), j),
{
    assert forall|j: int| 0 <= j < out.len() + 1 implies #[trigger] coreach_wit(
        v,
        S,
        out.push(y),
        nxt.push(q),
        j,
    ) by {
        // Math: j < |out|: an old entry
        // Why: entries before the new one keep their witness.
        if j < out.len() {
            // Math: the old witness of j
            assert(coreach_wit(v, S, out, nxt, j));
            // Math: (out · [y])[j] = out[j], (nxt · [q])[j] = nxt[j]
            assert(out.push(y)[j] == out[j] && nxt.push(q)[j] == nxt[j]);
            if let Option::Some((p, e)) = nxt[j] {
                // Math: (out · [y])[p] = out[p] (p < j < |out|)
                // Why: the parent/next entry is old too.
                assert(out.push(y)[p as int] == out[p as int]);
            }
        }
    }
}

// =============================================================================================
// reachable
// =============================================================================================

/// `n` flags, all false.
pub fn falses(n: usize) -> (v: Vec<bool>)
    ensures
        v@.len() == n,
        forall|i: int| 0 <= i < n ==> !#[trigger] v@[i],
{
    // Math: v = []
    let mut v: Vec<bool> = Vec::new();
    // Math: i = 0
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            v@.len() == i,
            forall|a: int| 0 <= a < i ==> !#[trigger] v@[a],
        decreases n - i,
    {
        // Math: v := v · [false]
        v.push(false);
        // Math: i := i + 1
        i += 1;
    }
    v
}

/// The states reachable from `s`, each once, in breadth-first order (Lean: `reach f S`), with
/// a parent for each: `None` for a state of `s`, else `Some((p, e))`: reached from `out[p]`
/// (`p < i`) by `e`.
pub fn reachable(g: &Aut, s: &Vec<usize>) -> (r: (Vec<usize>, Vec<Option<(usize, usize)>>))
    requires
        // Why: facts restated in each loop (a loop only knows its invariant).
        g.wf(),
        // Math: ∀ j: s[j] < n
        states_in(g, s@),
    ensures
        // Math: set_of(out) = reach(set_of(s))
        set_of(r.0@) == g@.reach(set_of(s@)),
        // Math: ∀ i: out[i] < n
        // Why: callers index per-state lists with the entries.
        forall|i: int| 0 <= i < r.0@.len() ==> #[trigger] r.0@[i] < g.n,
        // Math: out has no repeats
        r.0@.no_duplicates(),
        // Math: ∀ i: reach_wit(i)
        r.1@.len() == r.0@.len(),
        forall|i: int| 0 <= i < r.0@.len() ==> #[trigger] reach_wit(g@, set_of(s@), r.0@, r.1@, i),
{
    // Math: S = set_of(s)
    // Why: a ghost name for the start set, used by the contracts below.
    let ghost S = set_of(s@);
    // mark[y]: y is in out.
    // Math: mark = [false] * n
    // Why: mark[y]: y is in out.
    let mut mark = falses(g.n);
    // Math: out = []
    let mut out: Vec<usize> = Vec::new();
    // Math: par = []  (par[i]: the parent of out[i])
    let mut par: Vec<Option<(usize, usize)>> = Vec::new();
    proof {
        // Math: set_of([]) = ∅
        // Why: the invariants hold at the start.
        lemma_set_of_empty();
    }
    // Seed: the states of s, each once.
    // Math: j = 0
    // Why: seed: put the states of s in out, each once; s[0 .. j-1] are done.
    let mut j: usize = 0;
    while j < s.len()
        invariant
            // Why: facts restated in each loop (a loop only knows its invariant).
            g.wf(),
            // Math: ∀ j: s[j] < n
            states_in(g, s@),
            // Math: S = set_of(s) (ghost name for the start set)
            S == set_of(s@),
            // Math: 0 ≤ j ≤ |s|
            j <= s@.len(),
            // Math: |mark| = n
            mark@.len() == g.n,
            // Math: ∀ y ∈ [0, n): mark[y] ↔ y ∈ set_of(out)
            // Why: mark answers "already found?" in O(1).
            forall|y: int| 0 <= y < g.n ==> #[trigger] mark@[y] == set_of(out@).contains(y),
            // Math: ∀ i: out[i] < n
            forall|i: int| 0 <= i < out@.len() ==> #[trigger] out@[i] < g.n,
            // Math: out has no repeats
            out@.no_duplicates(),
            // Math: |par| = |out|
            par@.len() == out@.len(),
            // Math: ∀ i: reach_wit(i)  (start state, or reached from an earlier entry)
            // Why: R2 turns this into out ⊆ reach(S) at the end.
            forall|i: int| 0 <= i < out@.len() ==> #[trigger] reach_wit(g@, S, out@, par@, i),
            // Math: s[0 .. j-1] ⊆ set_of(out)
            forall|jj: int| 0 <= jj < j ==> set_of(out@).contains(#[trigger] s@[jj] as int),
        // Math: |s| - j decreases
        decreases s@.len() - j,
    {
        // Math: x = s[j]
        let x = s[j];
        // Math: x < n (states_in at j)
        // Why: so mark[x] can be read.
        assert(s@[j as int] < g.n);
        // Math: x ∉ set_of(out) ?
        if !mark[x] {
            // Why: hint: x ∈ S (it is s[j]).
            // Math: x ∈ S (x = s[j])
            // Why: hint: the witness of the new entry (None: a start state).
            assert(S.contains(x as int));
            proof {
                // Math: out · [x] has no repeats
                lemma_no_dup_push(out@, x);
                // Math: set_of(out · [x]) = set_of(out) ∪ {x}
                lemma_set_of_push(out@, x);
                // Math: the witnesses still hold after appending (x, None)
                lemma_reach_wit_push(g@, S, out@, par@, x, Option::None);
            }
            // Math: mark[x] := true; out := out · [x]
            mark.set(x, true);
            out.push(x);
            // Math: par := par · [None]  (a start state)
            par.push(None);
        }
        // Math: j := j + 1
        j += 1;
    }
    // Breadth-first search: out[0 .. h-1] are expanded.
    // Math: h = 0
    // Why: breadth-first search: out[0 .. h-1] are expanded; out works as the queue.
    let mut h: usize = 0;
    // Math: while some entry is not expanded
    while h < out.len()
        invariant
            // Why: facts restated in each loop (a loop only knows its invariant).
            g.wf(),
            // Math: S = set_of(s) (ghost name for the start set)
            S == set_of(s@),
            // Math: |mark| = n
            mark@.len() == g.n,
            // Math: ∀ y ∈ [0, n): mark[y] ↔ y ∈ set_of(out)
            // Why: mark answers "already found?" in O(1).
            forall|y: int| 0 <= y < g.n ==> #[trigger] mark@[y] == set_of(out@).contains(y),
            // Math: ∀ i: out[i] < n
            forall|i: int| 0 <= i < out@.len() ==> #[trigger] out@[i] < g.n,
            // Math: out has no repeats
            out@.no_duplicates(),
            // Math: |par| = |out|
            par@.len() == out@.len(),
            // Math: ∀ i: reach_wit(i)  (start state, or reached from an earlier entry)
            // Why: R2 turns this into out ⊆ reach(S) at the end.
            forall|i: int| 0 <= i < out@.len() ==> #[trigger] reach_wit(g@, S, out@, par@, i),
            // Math: S ⊆ set_of(out)
            forall|x: int| S.contains(x) ==> set_of(out@).contains(x),
            // Math: h ≤ |out|
            h <= out@.len(),
            // Math: ∀ h' < h, e, y: trans(out[h'], e, y) → y ∈ set_of(out)
            // Why: closed so far (the expanded part).
            // Math: ∀ h' < h, e, y: trans(out[h'], e, y) → y ∈ set_of(out)
            // Why: closed so far (the expanded part); at the end h = |out|: closed.
            forall|hh: int, e: int, y: int|
                0 <= hh < h && #[trigger] g.trans(out@[hh] as int, e, y) ==> set_of(out@).contains(y),
        // Why: out has at most n entries (no repeats, all below n), so h < n while looping.
        // Math: n - h decreases (h < |out| ≤ n inside the loop, lemma_len_bound)
        decreases g.n - h,
    {
        proof {
            // Math: |out| ≤ n (no repeats, all below n)
            // Why: so n - h > 0 while h < |out|: the search ends.
            lemma_len_bound(out@, g.n as int);
        }
        // Math: x = out[h], the state to expand
        let x = out[h];
        // Math: [lo, hi) = x's block
        let lo = g.start[x];
        let hi = g.start[x + 1];
        // Math: start[x] ≤ start[x+1] ≤ start[n]
        // Why: hint: the block lies inside evt and dst.
        assert(g.start@[x as int] <= g.start@[x + 1] <= g.start@[g.n as int]);
        // Math: k = lo  (k walks x's block)
        let mut k = lo;
        while k < hi
            invariant
                // Why: facts restated in each loop (a loop only knows its invariant).
                g.wf(),
                // Math: S = set_of(s) (ghost name for the start set)
                S == set_of(s@),
                // Math: h < |out|
                h < out@.len(),
                // Math: x = out[h]
                x == out@[h as int],
                // Math: x < n
                x < g.n,
                // Math: lo = start[x], hi = start[x+1] ≤ |evt|, lo ≤ k ≤ hi
                lo == g.start@[x as int],
                hi == g.start@[x + 1],
                hi <= g.evt@.len(),
                lo <= k <= hi,
                // Math: |mark| = n
                mark@.len() == g.n,
                // Math: ∀ y ∈ [0, n): mark[y] ↔ y ∈ set_of(out)
                // Why: mark answers "already found?" in O(1).
                forall|y: int| 0 <= y < g.n ==> #[trigger] mark@[y] == set_of(out@).contains(y),
                // Math: ∀ i: out[i] < n
                forall|i: int| 0 <= i < out@.len() ==> #[trigger] out@[i] < g.n,
                // Math: out has no repeats
                out@.no_duplicates(),
                // Math: |par| = |out|
                par@.len() == out@.len(),
                // Math: ∀ i: reach_wit(i)  (start state, or reached from an earlier entry)
                // Why: R2 turns this into out ⊆ reach(S) at the end.
                forall|i: int| 0 <= i < out@.len() ==> #[trigger] reach_wit(g@, S, out@, par@, i),
                // Math: S ⊆ set_of(out)
                // Why: R1/C1 need it.
                forall|x: int| S.contains(x) ==> set_of(out@).contains(x),
                // Math: ∀ h' < h, e, y: trans(out[h'], e, y) → y ∈ set_of(out)
                // Why: closed so far (the expanded part); at the end h = |out|: closed.
                forall|hh: int, e: int, y: int|
                    0 <= hh < h && #[trigger] g.trans(out@[hh] as int, e, y) ==> set_of(out@).contains(y),
                // Math: ∀ k' ∈ [lo, k): dst[k'] ∈ set_of(out)
                forall|kk: int| lo <= kk < k ==> set_of(out@).contains(#[trigger] g.dst@[kk] as int),
            // Math: hi - k decreases
            decreases hi - k,
        {
            // Math: y = dst[k]
            let y = g.dst[k];
            // Math: dst[k] < n (trans_ok)
            // Why: so mark[y] can be read.
            assert(g.dst@[k as int] < g.n);
            // Math: y ∉ set_of(out) ?
            if !mark[y] {
                // Math: e = evt[k]
                let e = g.evt[k];
                // Why: hint: position k shows out[h] --e--> y.
                // Math: start[x] ≤ k < start[x+1]
                // Why: hint: names position k as the witness of the transition.
                assert(g.in_blk(x as int, k as int));
                // Math: x --e--> y
                assert(g.trans(x as int, e as int, y as int));
                // Math: y ∈ f(x, e) (the view)
                // Why: the witness of the new entry is stated over the view.
                assert(g@.f(x as int, e as int, y as int));
                proof {
                    // Math: out · [y] has no repeats
                    lemma_no_dup_push(out@, y);
                    // Math: set_of(out · [y]) = set_of(out) ∪ {y}
                    lemma_set_of_push(out@, y);
                    // Math: (out · [y])[h] = x
                    // Why: the parent of the new entry is still out[h] after the push.
                    assert(out@.push(y)[h as int] == x);
                    // Math: the witnesses still hold after appending (y, Some((h, e)))
                    lemma_reach_wit_push(g@, S, out@, par@, y, Option::Some((h, e)));
                }
                // Why: ghost copy, to carry the closure facts over the push.
                // Why: ghost copy of out before the push, to carry the closure facts over it.
                let ghost out0 = out@;
                // Math: mark[y] := true; out := out · [y]; par := par · [(h, e)]
                mark.set(y, true);
                out.push(y);
                par.push(Some((h, e)));
                assert forall|hh: int, e: int, z: int|
                    0 <= hh < h && #[trigger] g.trans(out@[hh] as int, e, z) implies set_of(out@).contains(z) by {
                    // Math: out[h'] = out0[h'] (old entry)
                    assert(out@[hh] == out0[hh]);
                }
            }
            // Math: k := k + 1
            k += 1;
        }
        // Math: ∀ e, y: trans(out[h], e, y) → y ∈ set_of(out)
        assert forall|e: int, y: int| #[trigger] g.trans(x as int, e, y) implies set_of(out@).contains(y) by {
            // Math: kk: the position of the transition
            let kk = choose|kk: int| #[trigger] g.in_blk(x as int, kk) && g.evt@[kk] as int == e
                && g.dst@[kk] as int == y;
            // Math: lo ≤ kk < hi (= k)
            assert(lo <= kk < hi);
            // Math: dst[kk] ∈ set_of(out) (inner invariant at kk)
            assert(set_of(out@).contains(g.dst@[kk] as int));
        }
        // Math: h := h + 1
        h += 1;
    }
    // Math: closed(set_of(out)): every entry is expanded (h = |out|).
    // Math: closed(set_of(out)): x ∈ out ∧ y ∈ f(x, e) → y ∈ out
    // Why: every entry is expanded (h = |out|); this is the hypothesis of R1.
    assert forall|x: int, e: int, y: int| set_of(out@).contains(x) && #[trigger] g@.f(x, e, y) implies set_of(out@).contains(y) by {
        // Math: i with out[i] = x
        let i = choose|i: int| 0 <= i < out@.len() && #[trigger] out@[i] as int == x;
        // Why: hint: the trigger of the closure invariant at i.
        assert(g.trans(out@[i] as int, e, y));
    }
    // Math: reach(S) ⊆ set_of(out) (R1) and set_of(out) ⊆ reach(S) (R2).
    proof {
        // Math: R1: reach(S) ⊆ set_of(out)
        lemma_reach_subset(g@, S, set_of(out@));
        // Math: R2: set_of(out) ⊆ reach(S)
        assert forall|y: int| set_of(out@).contains(y) implies g@.reach(S).contains(y) by {
            // Math: i with out[i] = y
            let i = choose|i: int| 0 <= i < out@.len() && #[trigger] out@[i] as int == y;
            // Math: out[i] ∈ reach(S) (by the witnesses)
            lemma_wit_reach(g@, S, out@, par@, i);
        }
    }
    // Math: set_of(out) = reach(S) (both inclusions)
    assert(set_of(out@) =~= g@.reach(S));
    (out, par)
}

// =============================================================================================
// Reverse index and coreachable
// =============================================================================================

/// `rev` is the reverse index of `g`: `rev[y]` lists exactly the pairs `(x, e)` with
/// `y ∈ f(x, e)`.
pub open spec fn rev_ok(g: &Aut, rev: Seq<Vec<(usize, usize)>>) -> bool {
    // Math: |rev| = n
    &&& rev.len() == g.n
    // Math: sound: ∀ y, i: rev[y][i] = (x, e) → x < n ∧ trans(x, e, y)
    &&& forall|y: int, i: int|
        0 <= y < g.n && 0 <= i < rev[y]@.len() ==> (#[trigger] rev[y]@[i]).0 < g.n && g.trans(
            rev[y]@[i].0 as int,
            rev[y]@[i].1 as int,
            y,
        )
    // Math: complete: trans(x, e, y) → (x, e) ∈ rev[y]
    &&& forall|x: int, e: int, y: int|
        #[trigger] g.trans(x, e, y) ==> rev[y]@.contains((x as usize, e as usize))
}

/// For each state `y`, the transitions into it: `rev[y]` lists the pairs `(x, e)` with
/// `y ∈ f(x, e)`. Python: `trusted/reverse_index.py` (built there, checked by a verified
/// checker); here the builder itself is verified.
pub fn reverse_index(g: &Aut) -> (rev: Vec<Vec<(usize, usize)>>)
    requires
        // Why: facts restated in each loop (a loop only knows its invariant).
        g.wf(),
    ensures
        // Math: rev is the reverse index of g
        // Math: rev_ok(g, rev)
        // Why: rev lists exactly the transitions into each state.
        rev_ok(g, rev@),
        // Math: |rev| = n
        rev@.len() == g.n,
        // Math: sound: ∀ y, i: rev[y][i] = (x, e) → x < n ∧ trans(x, e, y)
        // Math: sound: ∀ y, i: rev[y][i] = (x', e) → x' < n ∧ trans(x', e, y)
        forall|y: int, i: int|
            0 <= y < g.n && 0 <= i < rev@[y]@.len() ==> (#[trigger] rev@[y]@[i]).0 < g.n && g.trans(
                rev@[y]@[i].0 as int,
                rev@[y]@[i].1 as int,
                y,
            ),
        // Math: complete: trans(x, e, y) → (x, e) ∈ rev[y]
        forall|x: int, e: int, y: int|
            #[trigger] g.trans(x, e, y) ==> rev@[y]@.contains((x as usize, e as usize)),
{
    // Math: rev = [[], ..., []] (n empty lists), built below
    let mut rev: Vec<Vec<(usize, usize)>> = Vec::new();
    // Math: i = 0 (i counts the empty lists made)
    let mut i: usize = 0;
    while i < g.n
        invariant
            i <= g.n,
            rev@.len() == i,
            forall|a: int| 0 <= a < i ==> (#[trigger] rev@[a])@.len() == 0,
        decreases g.n - i,
    {
        // Math: rev := rev · [[]]
        rev.push(Vec::new());
        // Math: i := i + 1
        i += 1;
    }
    // Math: x = 0
    // Why: x walks the source states; their blocks are added to rev.
    let mut x: usize = 0;
    while x < g.n
        invariant
            // Why: facts restated in each loop (a loop only knows its invariant).
            g.wf(),
            // Math: 0 ≤ x ≤ n
            x <= g.n,
            // Math: |rev| = n
            rev@.len() == g.n,
            // Math: sound: ∀ y, i: rev[y][i] = (x', e) → x' < n ∧ trans(x', e, y)
            forall|y: int, i: int|
                0 <= y < g.n && 0 <= i < rev@[y]@.len() ==> (#[trigger] rev@[y]@[i]).0 < g.n && g.trans(
                    rev@[y]@[i].0 as int,
                    rev@[y]@[i].1 as int,
                    y,
                ),
            // Math: complete for the sources done: x' < x
            // Math: complete for the sources done: x' < x ∧ trans(x', e, y) → (x', e) ∈ rev[y]
            forall|xx: int, e: int, y: int|
                0 <= xx < x && #[trigger] g.trans(xx, e, y) ==> rev@[y]@.contains((xx as usize, e as usize)),
        // Math: n - x decreases
        decreases g.n - x,
    {
        // Math: [lo, hi) = x's block
        let lo = g.start[x];
        let hi = g.start[x + 1];
        // Math: start[x] ≤ start[x+1] ≤ start[n]
        // Why: hint: the block lies inside evt and dst.
        assert(g.start@[x as int] <= g.start@[x + 1] <= g.start@[g.n as int]);
        // Math: k = lo  (k walks x's block)
        let mut k = lo;
        while k < hi
            invariant
                // Why: facts restated in each loop (a loop only knows its invariant).
                g.wf(),
                // Math: x < n
                x < g.n,
                // Math: lo = start[x], hi = start[x+1] ≤ |evt|, lo ≤ k ≤ hi
                lo == g.start@[x as int],
                hi == g.start@[x + 1],
                hi <= g.evt@.len(),
                lo <= k <= hi,
                // Math: |rev| = n
                rev@.len() == g.n,
                // Math: sound: ∀ y, i: rev[y][i] = (x', e) → x' < n ∧ trans(x', e, y)
                forall|y: int, i: int|
                    0 <= y < g.n && 0 <= i < rev@[y]@.len() ==> (#[trigger] rev@[y]@[i]).0 < g.n && g.trans(
                        rev@[y]@[i].0 as int,
                        rev@[y]@[i].1 as int,
                        y,
                    ),
                // Math: complete for the sources done: x' < x ∧ trans(x', e, y) → (x', e) ∈ rev[y]
                forall|xx: int, e: int, y: int|
                    0 <= xx < x && #[trigger] g.trans(xx, e, y) ==> rev@[y]@.contains((xx as usize, e as usize)),
                // Math: ∀ k' ∈ [lo, k): (x, evt[k']) ∈ rev[dst[k']]
                forall|kk: int|
                    lo <= kk < k ==> rev@[#[trigger] g.dst@[kk] as int]@.contains((x, g.evt@[kk])),
            // Math: hi - k decreases
            decreases hi - k,
        {
            // Math: y = dst[k], e = evt[k]
            let y = g.dst[k];
            let e = g.evt[k];
            // Math: dst[k] < n (trans_ok)
            // Why: so mark[y] can be read.
            assert(g.dst@[k as int] < g.n);
            // Math: start[x] ≤ k < start[x+1]
            // Why: hint: names position k as the witness of the transition.
            assert(g.in_blk(x as int, k as int));
            // Math: x --e--> y
            assert(g.trans(x as int, e as int, y as int));
            // Why: ghost copy of rev, to say what the push changes.
            let ghost rev0 = rev@;
            // Math: rev[y] := rev[y] · [(x, e)]
            rev[y].push((x, e));
            // Math: rev[y] gains (x, e) at its end; other lists are unchanged.
            // Math: rev[y] = rev0[y] · [(x, e)]
            assert(rev@[y as int]@ == rev0[y as int]@.push((x, e)));
            // Math: ∀ z ≠ y: rev[z] = rev0[z]
            assert(forall|z: int| 0 <= z < g.n && z != y ==> rev@[z] == rev0[z]);
            // Why: hints: membership in the lists only grows.
            // Math: soundness carries over: old entries unchanged; the new one is (x, e) with x --e--> y
            assert forall|z: int, i: int|
                0 <= z < g.n && 0 <= i < rev@[z]@.len() implies (#[trigger] rev@[z]@[i]).0 < g.n
                    && g.trans(rev@[z]@[i].0 as int, rev@[z]@[i].1 as int, z) by {
                if z == y as int && i == rev0[z]@.len() {
                } else {
                    // Math: rev[z][i] = rev0[z][i] (old entry)
                    assert(rev@[z]@[i] == rev0[z]@[i]);
                }
            }
            // Math: ∀ z, p: p ∈ rev0[z] → p ∈ rev[z]
            // Why: membership only grows, so completeness carries over.
            assert forall|p: (usize, usize), z: int| 0 <= z < g.n && rev0[z]@.contains(p) implies #[trigger] rev@[z]@.contains(p) by {
                // Math: i with rev0[z][i] = p; the same index still holds p
                let i = choose|i: int| 0 <= i < rev0[z]@.len() && rev0[z]@[i] == p;
                assert(rev@[z]@[i] == p);
            }
            // Math: the last entry of rev[y] is (x, e)
            // Why: the inner invariant at k.
            assert(rev@[y as int]@[rev0[y as int]@.len() as int] == (x, e));
            // Math: k := k + 1
            k += 1;
        }
        // Math: ∀ e, y: trans(x, e, y) → (x, e) ∈ rev[y]
        assert forall|e: int, y: int| #[trigger] g.trans(x as int, e, y) implies rev@[y]@.contains((x, e as usize)) by {
            // Math: kk: the position of the transition
            let kk = choose|kk: int| #[trigger] g.in_blk(x as int, kk) && g.evt@[kk] as int == e
                && g.dst@[kk] as int == y;
            // Math: lo ≤ kk < hi (= k)
            assert(lo <= kk < hi);
            // Math: (x, evt[kk]) ∈ rev[dst[kk]] (inner invariant at kk)
            assert(rev@[g.dst@[kk] as int]@.contains((x, g.evt@[kk])));
        }
        // Math: x := x + 1
        x += 1;
    }
    rev
}

/// The states from which some state of `s` can be reached, each once, in breadth-first order
/// from `s` (Lean: `coreach f S`), with a next step for each: `None` for a state of `s`, else
/// `Some((p, e))`: `e` leads to `out[p]` (`p < i`).
pub fn coreachable(g: &Aut, s: &Vec<usize>) -> (r: (Vec<usize>, Vec<Option<(usize, usize)>>))
    requires
        // Why: facts restated in each loop (a loop only knows its invariant).
        g.wf(),
        // Math: ∀ j: s[j] < n
        states_in(g, s@),
    ensures
        set_of(r.0@) == g@.coreach(set_of(s@)),
        forall|i: int| 0 <= i < r.0@.len() ==> #[trigger] r.0@[i] < g.n,
        r.0@.no_duplicates(),
        r.1@.len() == r.0@.len(),
        forall|i: int| 0 <= i < r.0@.len() ==> #[trigger] coreach_wit(g@, set_of(s@), r.0@, r.1@, i),
{
    // Math: rev = the reverse index of g (rev_ok)
    let rev = reverse_index(g);
    // Math: the search over rev
    coreachable_with(g, &rev, s)
}

/// `coreachable` over a reverse index built before (so a caller can keep it and reuse it).
pub fn coreachable_with(g: &Aut, rev: &Vec<Vec<(usize, usize)>>, s: &Vec<usize>) -> (r: (Vec<usize>, Vec<Option<(usize, usize)>>))
    requires
        // Why: facts restated in each loop (a loop only knows its invariant).
        g.wf(),
        rev_ok(g, rev@),
        // Math: ∀ j: s[j] < n
        states_in(g, s@),
    ensures
        // Math: set_of(out) = coreach(set_of(s))
        set_of(r.0@) == g@.coreach(set_of(s@)),
        // Math: ∀ i: out[i] < n
        // Why: callers index per-state lists with the entries.
        forall|i: int| 0 <= i < r.0@.len() ==> #[trigger] r.0@[i] < g.n,
        r.0@.no_duplicates(),
        r.1@.len() == r.0@.len(),
        forall|i: int| 0 <= i < r.0@.len() ==> #[trigger] coreach_wit(g@, set_of(s@), r.0@, r.1@, i),
{
    // Math: S = set_of(s)
    // Why: a ghost name for the start set, used by the contracts below.
    let ghost S = set_of(s@);
    // Math: mark = [false] * n
    // Why: mark[y]: y is in out.
    let mut mark = falses(g.n);
    // Math: out = []
    let mut out: Vec<usize> = Vec::new();
    // Math: nxt = []  (nxt[i]: the next step of out[i] towards S)
    let mut nxt: Vec<Option<(usize, usize)>> = Vec::new();
    proof {
        // Math: set_of([]) = ∅
        // Why: the invariants hold at the start.
        lemma_set_of_empty();
    }
    // Math: j = 0
    // Why: seed: put the states of s in out, each once; s[0 .. j-1] are done.
    let mut j: usize = 0;
    while j < s.len()
        invariant
            // Why: facts restated in each loop (a loop only knows its invariant).
            g.wf(),
            // Math: ∀ j: s[j] < n
            states_in(g, s@),
            // Math: S = set_of(s) (ghost name for the start set)
            S == set_of(s@),
            // Math: 0 ≤ j ≤ |s|
            j <= s@.len(),
            // Math: |mark| = n
            mark@.len() == g.n,
            // Math: ∀ y ∈ [0, n): mark[y] ↔ y ∈ set_of(out)
            // Why: mark answers "already found?" in O(1).
            forall|y: int| 0 <= y < g.n ==> #[trigger] mark@[y] == set_of(out@).contains(y),
            // Math: ∀ i: out[i] < n
            forall|i: int| 0 <= i < out@.len() ==> #[trigger] out@[i] < g.n,
            // Math: out has no repeats
            out@.no_duplicates(),
            // Math: |nxt| = |out|
            nxt@.len() == out@.len(),
            // Math: ∀ i: coreach_wit(i)  (target state, or leads to an earlier entry)
            // Why: C2 turns this into out ⊆ coreach(S) at the end.
            forall|i: int| 0 <= i < out@.len() ==> #[trigger] coreach_wit(g@, S, out@, nxt@, i),
            // Math: s[0 .. j-1] ⊆ set_of(out)
            forall|jj: int| 0 <= jj < j ==> set_of(out@).contains(#[trigger] s@[jj] as int),
        // Math: |s| - j decreases
        decreases s@.len() - j,
    {
        // Math: x = s[j]
        let x = s[j];
        // Math: x < n (states_in at j)
        // Why: so mark[x] can be read.
        assert(s@[j as int] < g.n);
        // Math: x ∉ set_of(out) ?
        if !mark[x] {
            // Math: x ∈ S (x = s[j])
            // Why: hint: the witness of the new entry (None: a start state).
            assert(S.contains(x as int));
            proof {
                // Math: out · [x] has no repeats
                lemma_no_dup_push(out@, x);
                // Math: set_of(out · [x]) = set_of(out) ∪ {x}
                lemma_set_of_push(out@, x);
                // Math: the witnesses still hold after appending (x, None)
                lemma_coreach_wit_push(g@, S, out@, nxt@, x, Option::None);
            }
            // Math: mark[x] := true; out := out · [x]
            mark.set(x, true);
            out.push(x);
            // Math: nxt := nxt · [None]  (a target state)
            nxt.push(None);
        }
        // Math: j := j + 1
        j += 1;
    }
    // Math: h = 0
    // Why: breadth-first search: out[0 .. h-1] are expanded; out works as the queue.
    let mut h: usize = 0;
    // Math: while some entry is not expanded
    while h < out.len()
        invariant
            // Why: facts restated in each loop (a loop only knows its invariant).
            g.wf(),
            // Math: S = set_of(s) (ghost name for the start set)
            S == set_of(s@),
            // Math: |rev| = n
            rev@.len() == g.n,
            // Math: sound: ∀ y, i: rev[y][i] = (x', e) → x' < n ∧ trans(x', e, y)
            forall|y: int, i: int|
                0 <= y < g.n && 0 <= i < rev@[y]@.len() ==> (#[trigger] rev@[y]@[i]).0 < g.n && g.trans(
                    rev@[y]@[i].0 as int,
                    rev@[y]@[i].1 as int,
                    y,
                ),
            // Math: complete: trans(x, e, y) → (x, e) ∈ rev[y]
            forall|x: int, e: int, y: int|
                #[trigger] g.trans(x, e, y) ==> rev@[y]@.contains((x as usize, e as usize)),
            // Math: |mark| = n
            mark@.len() == g.n,
            // Math: ∀ y ∈ [0, n): mark[y] ↔ y ∈ set_of(out)
            // Why: mark answers "already found?" in O(1).
            forall|y: int| 0 <= y < g.n ==> #[trigger] mark@[y] == set_of(out@).contains(y),
            // Math: ∀ i: out[i] < n
            forall|i: int| 0 <= i < out@.len() ==> #[trigger] out@[i] < g.n,
            // Math: out has no repeats
            out@.no_duplicates(),
            // Math: |nxt| = |out|
            nxt@.len() == out@.len(),
            // Math: ∀ i: coreach_wit(i)  (target state, or leads to an earlier entry)
            // Why: C2 turns this into out ⊆ coreach(S) at the end.
            forall|i: int| 0 <= i < out@.len() ==> #[trigger] coreach_wit(g@, S, out@, nxt@, i),
            // Math: S ⊆ set_of(out)
            // Why: R1/C1 need it.
            forall|x: int| S.contains(x) ==> set_of(out@).contains(x),
            // Math: h ≤ |out|
            h <= out@.len(),
            // Math: ∀ h' < h, x, e: trans(x, e, out[h']) → x ∈ set_of(out)
            forall|hh: int, x: int, e: int|
                0 <= hh < h && #[trigger] g.trans(x, e, out@[hh] as int) ==> set_of(out@).contains(x),
        // Math: n - h decreases (h < |out| ≤ n inside the loop, lemma_len_bound)
        decreases g.n - h,
    {
        proof {
            // Math: |out| ≤ n (no repeats, all below n)
            // Why: so n - h > 0 while h < |out|: the search ends.
            lemma_len_bound(out@, g.n as int);
        }
        // Math: y = out[h], the state to expand (backwards)
        let y = out[h];
        // Math: preds = rev[y], the transitions into y
        let preds = &rev[y];
        // Math: i = 0 (i walks preds)
        let mut i: usize = 0;
        while i < preds.len()
            invariant
                // Why: facts restated in each loop (a loop only knows its invariant).
                g.wf(),
                // Math: S = set_of(s) (ghost name for the start set)
                S == set_of(s@),
                // Math: h < |out|
                h < out@.len(),
                // Math: y = out[h] < n
                y == out@[h as int],
                y < g.n,
                // Math: |rev| = n
                rev@.len() == g.n,
                // Math: preds = rev[y]
                preds@ == rev@[y as int]@,
                // Math: sound: ∀ y, i: rev[y][i] = (x', e) → x' < n ∧ trans(x', e, y)
                forall|y: int, i: int|
                    0 <= y < g.n && 0 <= i < rev@[y]@.len() ==> (#[trigger] rev@[y]@[i]).0 < g.n && g.trans(
                        rev@[y]@[i].0 as int,
                        rev@[y]@[i].1 as int,
                        y,
                    ),
                // Math: 0 ≤ i ≤ |preds|
                i <= preds@.len(),
                // Math: |mark| = n
                mark@.len() == g.n,
                forall|z: int| 0 <= z < g.n ==> #[trigger] mark@[z] == set_of(out@).contains(z),
                // Math: ∀ i: out[i] < n
                forall|i: int| 0 <= i < out@.len() ==> #[trigger] out@[i] < g.n,
                // Math: out has no repeats
                out@.no_duplicates(),
                // Math: |nxt| = |out|
                nxt@.len() == out@.len(),
                // Math: ∀ i: coreach_wit(i)  (target state, or leads to an earlier entry)
                // Why: C2 turns this into out ⊆ coreach(S) at the end.
                forall|i: int| 0 <= i < out@.len() ==> #[trigger] coreach_wit(g@, S, out@, nxt@, i),
                // Math: S ⊆ set_of(out)
                // Why: R1/C1 need it.
                forall|x: int| S.contains(x) ==> set_of(out@).contains(x),
                // Math: ∀ h' < h, x, e: trans(x, e, out[h']) → x ∈ set_of(out)
                // Why: backward closed so far.
                forall|hh: int, x: int, e: int|
                    0 <= hh < h && #[trigger] g.trans(x, e, out@[hh] as int) ==> set_of(out@).contains(x),
                // Math: ∀ i' < i: preds[i'].0 ∈ set_of(out)
                forall|ii: int| 0 <= ii < i ==> set_of(out@).contains((#[trigger] preds@[ii]).0 as int),
            // Math: |preds| - i decreases
            decreases preds@.len() - i,
        {
            // Math: (x, e) = preds[i]
            let (x, e) = preds[i];
            // Why: hint: soundness of rev at (y, i).
            // Math: rev[y][i] = (x, e)
            // Why: hint: soundness of rev at (y, i).
            assert(rev@[y as int]@[i as int] == (x, e));
            // Math: x --e--> y
            assert(g.trans(x as int, e as int, y as int));
            // Math: x ∉ set_of(out) ?
            if !mark[x] {
                // Math: y ∈ f(x, e) (the view)
                // Why: the witness of the new entry is stated over the view.
                assert(g@.f(x as int, e as int, y as int));
                proof {
                    // Math: out · [x] has no repeats
                    lemma_no_dup_push(out@, x);
                    // Math: set_of(out · [x]) = set_of(out) ∪ {x}
                    lemma_set_of_push(out@, x);
                    // Math: (out · [x])[h] = y
                    // Why: the next entry is still out[h] after the push.
                    assert(out@.push(x)[h as int] == y);
                    // Math: the witnesses still hold after appending (x, Some((h, e)))
                    lemma_coreach_wit_push(g@, S, out@, nxt@, x, Option::Some((h, e)));
                }
                // Why: ghost copy of out before the push, to carry the closure facts over it.
                let ghost out0 = out@;
                // Math: mark[x] := true; out := out · [x]
                mark.set(x, true);
                out.push(x);
                // Math: nxt := nxt · [(h, e)]
                nxt.push(Some((h, e)));
                assert forall|hh: int, z: int, e: int|
                    0 <= hh < h && #[trigger] g.trans(z, e, out@[hh] as int) implies set_of(out@).contains(z) by {
                    // Math: out[h'] = out0[h'] (old entry)
                    assert(out@[hh] == out0[hh]);
                }
            }
            i += 1;
        }
        // Math: ∀ x, e: trans(x, e, y) → x ∈ set_of(out)
        assert forall|x: int, e: int| #[trigger] g.trans(x, e, y as int) implies set_of(out@).contains(x) by {
            // Math: (x, e) ∈ rev[y] (completeness of rev)
            assert(rev@[y as int]@.contains((x as usize, e as usize)));
            // Math: ii with preds[ii] = (x, e)
            let ii = choose|ii: int| 0 <= ii < preds@.len() && preds@[ii] == (x as usize, e as usize);
            // Math: preds[ii].0 ∈ set_of(out) (inner invariant at ii)
            assert(set_of(out@).contains(preds@[ii].0 as int));
            // Why: x is a state (trans), so x as usize as int = x.
            assert(0 <= x < g.n);
        }
        // Math: h := h + 1
        h += 1;
    }
    // Math: back_closed(set_of(out)).
    // Math: back_closed(set_of(out)): y ∈ out ∧ y ∈ f(x, e) → x ∈ out
    // Why: every entry is expanded; the hypothesis of C1.
    assert forall|x: int, e: int, y: int| set_of(out@).contains(y) && #[trigger] g@.f(x, e, y) implies set_of(out@).contains(x) by {
        // Math: i with out[i] = y
        let i = choose|i: int| 0 <= i < out@.len() && #[trigger] out@[i] as int == y;
        // Why: hint: the trigger of the backward closure invariant at i.
        assert(g.trans(x, e, out@[i] as int));
    }
    proof {
        // Math: C1: coreach(S) ⊆ set_of(out)
        lemma_coreach_subset(g@, S, set_of(out@));
        // Math: C2: set_of(out) ⊆ coreach(S)
        assert forall|x: int| set_of(out@).contains(x) implies g@.coreach(S).contains(x) by {
            // Math: i with out[i] = x
            let i = choose|i: int| 0 <= i < out@.len() && #[trigger] out@[i] as int == x;
            // Math: out[i] ∈ coreach(S) (by the witnesses)
            lemma_wit_coreach(g@, S, out@, nxt@, i);
        }
    }
    // Math: set_of(out) = coreach(S) (both inclusions)
    assert(set_of(out@) =~= g@.coreach(S));
    (out, nxt)
}

} // verus!
