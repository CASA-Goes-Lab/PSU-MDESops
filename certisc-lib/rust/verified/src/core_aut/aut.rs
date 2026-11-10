//! The automaton: flat storage (`Aut`) and its mathematical view (`AutView`).
//!
//! Glossary of the notation used in this file:
//! - `spec fn`: a mathematical function, used only in contracts and proofs; it never runs.
//! - `open spec fn`: its body is visible to callers' proofs; `closed`: only its name is.
//! - `v@`: the view of `v`. For a `Vec<T>` it is the sequence `Seq<T>` of its elements; for an
//!   `Aut` it is the `AutView` defined below.
//! - `s[i]`: element `i` of sequence `s`; `s.len()`: its length `|s|`.
//! - `ISet<A>`: a mathematical set of `A`s; `ISet::new(|a| P(a))` is `{a | P(a)}`;
//!   `S.contains(a)` is `a ∈ S`.
//! - `forall|x: int| P(x) ==> Q(x)`: `∀ x ∈ ℤ, P(x) → Q(x)`; `exists|x: int| P(x)`: `∃ x ∈ ℤ, P(x)`.
//! - `#[trigger] t`: the term `t` tells the SMT solver when to use a `forall` (each time a term of
//!   that shape appears in the proof) or which witness to try for an `exists`.
//! - `&&&`: a list of conjuncts, one per line (same as `&&`).
//! - `int`: a mathematical integer (no overflow); `x as int` converts a machine integer.

use vstd::prelude::*;

verus! {

/// An automaton in the grouped encoding (as `Encoded` in Python, `wrapper.md` section 4).
///
/// States are `0 .. n-1`, events are `0 .. m-1`. State `x` owns transition positions
/// `start[x] .. start[x+1]-1`; position `k` is the transition `x --evt[k]--> dst[k]`.
pub struct Aut {
    /// Number of states.
    pub n: usize,
    /// Number of event numbers (the size of the event table).
    pub m: usize,
    /// `in_e[e]`: event `e` is in the alphabet `E`.
    pub in_e: Vec<bool>,
    /// `in_euc[e]`: event `e` is uncontrollable (`e ∈ Euc`).
    pub in_euc: Vec<bool>,
    /// `in_euo[e]`: event `e` is unobservable (`e ∈ Euo`).
    pub in_euo: Vec<bool>,
    /// `init[x]`: state `x` is initial (`x ∈ X0`).
    pub init: Vec<bool>,
    /// `marked[x]`: state `x` is marked (`x ∈ Xm`).
    pub marked: Vec<bool>,
    /// Block boundaries: `n + 1` entries.
    pub start: Vec<usize>,
    /// Event of each transition position.
    pub evt: Vec<usize>,
    /// Target of each transition position.
    pub dst: Vec<usize>,
}

/// The mathematical automaton that an `Aut` stands for (Lean: `Automaton`, Automaton.lean).
#[allow(non_snake_case)]
pub struct AutView {
    /// Number of states; the states are `0 .. n-1` (Lean: `Fin n`).
    pub n: int,
    /// Number of event numbers.
    pub m: int,
    /// The alphabet `E`.
    pub E: ISet<int>,
    /// The uncontrollable events `Euc`.
    pub Euc: ISet<int>,
    /// The unobservable events `Euo`.
    pub Euo: ISet<int>,
    /// The initial states `X0`.
    pub X0: ISet<int>,
    /// The marked states `Xm`.
    pub Xm: ISet<int>,
    /// The transitions: `(x, e, y) ∈ delta` means `y ∈ f(x, e)` (Lean: `f x e`).
    pub delta: ISet<(int, int, int)>,
}

/// The set of the elements of a sequence of machine integers: `{s[i] | 0 ≤ i < |s|}`.
pub open spec fn set_of(s: Seq<usize>) -> ISet<int> {
    // Math: {x ∈ ℤ | ∃ i ∈ [0, |s|): s[i] = x}
    // Why: contracts compare the lists a function returns with sets defined in the view.
    ISet::new(|x: int| exists|i: int| 0 <= i < s.len() && #[trigger] s[i] as int == x)
}

/// All states of `s` are states of `g`.
pub open spec fn states_in(g: &Aut, s: Seq<usize>) -> bool {
    // Math: ∀ j ∈ [0, |s|): s[j] < n
    forall|j: int| 0 <= j < s.len() ==> #[trigger] s[j] < g.n
}

impl Aut {
    /// Number of transitions `T = |evt|`.
    pub open spec fn num_trans(&self) -> int {
        // Math: T = |evt|
        self.evt@.len() as int
    }

    /// Position `k` belongs to state `x`'s block.
    pub open spec fn in_blk(&self, x: int, k: int) -> bool {
        // Math: x ∈ [0, n) ∧ start[x] ≤ k < start[x+1]
        // Why: names "transition k leaves state x"; used by `trans` and by every proof that
        //      walks a block.
        0 <= x < self.n && self.start@[x] <= k < self.start@[x + 1]
    }

    /// `x --e--> y` is a transition: some position of `x`'s block carries `e` and `y`.
    pub open spec fn trans(&self, x: int, e: int, y: int) -> bool {
        // Math: ∃ k: in_blk(x, k) ∧ evt[k] = e ∧ dst[k] = y
        // Why: the link between the flat storage and the view's `delta`.
        //      Trigger `in_blk(x, k)`: a proof shows a transition by naming its position k.
        exists|k: int| #[trigger] self.in_blk(x, k) && self.evt@[k] as int == e
            && self.dst@[k] as int == y
    }

    // --- validity (what `check.rs` checks; Python: `valid_automaton` in check.py) -----------

    /// One flag per event and per state; `n + 1` block boundaries; one target per event entry.
    pub open spec fn sizes_ok(&self) -> bool {
        // Math: |in_e| = |in_euc| = |in_euo| = m
        &&& self.in_e@.len() == self.m
        &&& self.in_euc@.len() == self.m
        &&& self.in_euo@.len() == self.m
        // Math: |init| = |marked| = n
        &&& self.init@.len() == self.n
        &&& self.marked@.len() == self.n
        // Math: |start| = n + 1
        &&& self.start@.len() == self.n + 1
        // Math: |dst| = |evt|
        &&& self.dst@.len() == self.evt@.len()
    }

    /// `start` cuts the positions `0 .. T-1` into `n` consecutive blocks.
    pub open spec fn blocks_ok(&self) -> bool {
        // Math: start[0] = 0
        // Why: the first block starts at the first position.
        &&& self.start@[0] == 0
        // Math: start[n] = T
        // Why: the last block ends at the last position.
        &&& self.start@[self.n as int] == self.num_trans()
        // Math: ∀ x, y: 0 ≤ x ≤ y ≤ n → start[x] ≤ start[y]
        // Why: blocks do not run backwards. Stated for every pair, not only neighbours, so the
        //      solver never has to chain neighbour facts (that would need induction).
        //      Trigger: both terms, so the rule fires only for two boundaries already in view.
        &&& forall|x: int, y: int|
            0 <= x <= y <= self.n ==> #[trigger] self.start@[x] <= #[trigger] self.start@[y]
    }

    /// The events of state `x`'s block are in increasing order.
    pub open spec fn blk_sorted(&self, x: int) -> bool {
        // Math: ∀ k, l: start[x] ≤ k ≤ l < start[x+1] → evt[k] ≤ evt[l]
        // Why: binary search inside a block (next_states) and the determinism check need it.
        forall|k: int, l: int|
            self.start@[x] <= k <= l < self.start@[x + 1] ==> #[trigger] self.evt@[k]
                <= #[trigger] self.evt@[l]
    }

    /// Every block is sorted by event (layout B, 2026-10-21).
    pub open spec fn sorted_ok(&self) -> bool {
        // Math: ∀ x ∈ [0, n): blk_sorted(x)
        // Why: trigger is the whole `blk_sorted(x)` term, so a proof opens it only for the
        //      blocks it talks about.
        forall|x: int| 0 <= x < self.n ==> #[trigger] self.blk_sorted(x)
    }

    /// (W1) and ranges: every transition uses an event of `E`, and its target is a state.
    pub open spec fn trans_ok(&self) -> bool {
        // Math: ∀ k ∈ [0, T): evt[k] < m ∧ in_e[evt[k]] ∧ dst[k] < n
        // Why: two triggers, so either `evt[k]` or `dst[k]` in a proof brings in the fact.
        forall|k: int|
            #![trigger self.evt@[k]]
            #![trigger self.dst@[k]]
            0 <= k < self.num_trans() ==> self.evt@[k] < self.m && self.in_e@[self.evt@[k] as int]
                && self.dst@[k] < self.n
    }

    /// (W2): `Euc ⊆ E` and `Euo ⊆ E`.
    pub open spec fn events_ok(&self) -> bool {
        // Math: ∀ e ∈ [0, m): (in_euc[e] → in_e[e]) ∧ (in_euo[e] → in_e[e])
        forall|e: int|
            #![trigger self.in_euc@[e]]
            #![trigger self.in_euo@[e]]
            0 <= e < self.m ==> (self.in_euc@[e] ==> self.in_e@[e]) && (self.in_euo@[e]
                ==> self.in_e@[e])
    }

    /// (W3): there is an initial state exactly when there are states.
    pub open spec fn init_ok(&self) -> bool {
        // Math: n > 0 ↔ ∃ x ∈ [0, n): init[x]
        // Why: Lean `wf_X0`. An automaton with states but no initial state is not valid.
        (self.n > 0) == (exists|x: int| 0 <= x < self.n && #[trigger] self.init@[x])
    }

    /// The storage is a valid automaton (Python: `valid_automaton(..., deterministic=False)`).
    pub open spec fn wf(&self) -> bool {
        // Math: each part above holds.
        // Why: the precondition of every operation; `check` decides it at run time.
        &&& self.sizes_ok()
        &&& self.blocks_ok()
        &&& self.sorted_ok()
        &&& self.trans_ok()
        &&& self.events_ok()
        &&& self.init_ok()
    }

    /// No event occurs twice in state `x`'s block.
    pub open spec fn blk_det(&self, x: int) -> bool {
        // Math: ∀ k, l: start[x] ≤ k < l < start[x+1] → evt[k] ≠ evt[l]
        forall|k: int, l: int|
            self.start@[x] <= k < l < self.start@[x + 1] ==> #[trigger] self.evt@[k]
                != #[trigger] self.evt@[l]
    }

    /// Deterministic: at most one initial state, and no state has two transitions on one event.
    pub open spec fn is_det(&self) -> bool {
        // Math: ∀ x, y ∈ [0, n): init[x] ∧ init[y] → x = y
        // Why: Lean `IsDeterministic`, first part: |X0| ≤ 1.
        &&& forall|x: int, y: int|
            0 <= x < self.n && 0 <= y < self.n && #[trigger] self.init@[x] && #[trigger] self.init@[y]
                ==> x == y
        // Math: ∀ x ∈ [0, n): blk_det(x)
        // Why: Lean `IsDeterministic`, second part: |f(x, e)| ≤ 1 (on a valid encoding).
        &&& forall|x: int| 0 <= x < self.n ==> #[trigger] self.blk_det(x)
    }
}

impl View for Aut {
    type V = AutView;

    /// The automaton the storage stands for.
    open spec fn view(&self) -> AutView {
        AutView {
            // Math: n, m as integers.
            n: self.n as int,
            m: self.m as int,
            // Math: E = {e ∈ [0, m) | in_e[e]}; likewise Euc, Euo.
            E: ISet::new(|e: int| 0 <= e < self.m && self.in_e@[e]),
            Euc: ISet::new(|e: int| 0 <= e < self.m && self.in_euc@[e]),
            Euo: ISet::new(|e: int| 0 <= e < self.m && self.in_euo@[e]),
            // Math: X0 = {x ∈ [0, n) | init[x]}; Xm = {x ∈ [0, n) | marked[x]}.
            X0: ISet::new(|x: int| 0 <= x < self.n && self.init@[x]),
            Xm: ISet::new(|x: int| 0 <= x < self.n && self.marked@[x]),
            // Math: delta = {(x, e, y) | trans(x, e, y)}.
            delta: ISet::new(|t: (int, int, int)| self.trans(t.0, t.1, t.2)),
        }
    }
}

impl AutView {
    /// `y ∈ f(x, e)` (Lean: `y ∈ f x e`).
    pub open spec fn f(self, x: int, e: int, y: int) -> bool {
        // Math: (x, e, y) ∈ delta
        self.delta.contains((x, e, y))
    }

    /// `xs` is a run of the word `w`: `xs[0] --w[0]--> xs[1] --w[1]--> ... --> xs[|w|]`.
    pub open spec fn is_run(self, xs: Seq<int>, w: Seq<int>) -> bool {
        // Math: |xs| = |w| + 1
        // Why: one state before each event, plus the last state.
        &&& xs.len() == w.len() + 1
        // Math: ∀ i ∈ [0, |w|): xs[i+1] ∈ f(xs[i], w[i])
        // Why: each step is a transition. Trigger `w[i]`, not `xs[i]`: the body mentions
        //      xs[i+1], and a trigger on xs[i] would fire again on it without end.
        &&& forall|i: int| 0 <= i < w.len() ==> self.f(xs[i], #[trigger] w[i], xs[i + 1])
    }

    /// `f(S, e)`: the states reached from `S` by one `e` (Lean: `step f S e`).
    pub open spec fn step(self, S: ISet<int>, e: int) -> ISet<int> {
        // Math: {y | ∃ x ∈ S: y ∈ f(x, e)}
        ISet::new(|y: int| exists|x: int| #[trigger] S.contains(x) && self.f(x, e, y))
    }

    /// The events enabled at some state of `S` (Lean: `active f S`).
    pub open spec fn active(self, S: ISet<int>) -> ISet<int> {
        // Math: {e | ∃ x ∈ S, ∃ y: y ∈ f(x, e)}
        ISet::new(|e: int| exists|x: int, y: int| #[trigger] S.contains(x) && #[trigger] self.f(x, e, y))
    }

    /// The states reachable from `S` (Lean: `reach f X0`).
    pub open spec fn reach(self, S: ISet<int>) -> ISet<int> {
        // Math: {y | ∃ xs, w: is_run(xs, w) ∧ xs[0] ∈ S ∧ xs[|w|] = y}
        ISet::new(|y: int| exists|xs: Seq<int>, w: Seq<int>| #[trigger] self.is_run(xs, w)
            && S.contains(xs[0]) && xs.last() == y)
    }

    /// The accessible states (Lean: `Ac`): reachable from an initial state.
    pub open spec fn Ac(self) -> ISet<int> {
        // Math: Ac = reach(X0)
        self.reach(self.X0)
    }

    /// The coaccessible states (Lean: `CoAc`): a marked state is reachable from them.
    pub open spec fn CoAc(self) -> ISet<int> {
        // Math: CoAc = coreach(Xm)
        self.coreach(self.Xm)
    }

    /// The states from which some state of `S` is reachable (Lean: `coreach f Xm`).
    pub open spec fn coreach(self, S: ISet<int>) -> ISet<int> {
        // Math: {x | ∃ xs, w: is_run(xs, w) ∧ xs[0] = x ∧ xs[|w|] ∈ S}
        ISet::new(|x: int| exists|xs: Seq<int>, w: Seq<int>| #[trigger] self.is_run(xs, w)
            && xs[0] == x && S.contains(xs.last()))
    }
}


// --- facts about `set_of` -------------------------------------------------------------------

/// Appending `v` to a list adds `v` to its set.
pub proof fn lemma_set_of_push(s: Seq<usize>, v: usize)
    // Math: set_of(s · [v]) = set_of(s) ∪ {v}
    ensures
        set_of(s.push(v)) == set_of(s).insert(v as int),
{
    // t = s · [v]
    let t = s.push(v);
    // Math: ∀ x: x ∈ set_of(t) ↔ x ∈ set_of(s) ∪ {v}
    assert forall|x: int| set_of(t).contains(x) == set_of(s).insert(v as int).contains(x) by {
        // ← for x ∈ set_of(s): the same index i of s is an index of t.
        if set_of(s).contains(x) {
            let i = choose|i: int| 0 <= i < s.len() && s[i] as int == x;
            // Why: hint: t[i] = s[i] (push keeps the old elements).
            assert(t[i] == s[i]);
        }
        // ← for x = v: v is the last element of t.
        if x == v as int {
            assert(t[s.len() as int] == v);
        }
        // → for x ∈ set_of(t): its index is in s, or it is the last one (= v).
        if set_of(t).contains(x) {
            let i = choose|i: int| 0 <= i < t.len() && t[i] as int == x;
            if i < s.len() {
                assert(s[i] == t[i]);
            }
        }
    }
    // Why: two ISets with the same members are equal (extensionality, `=~=`).
    assert(set_of(t) =~= set_of(s).insert(v as int));
}

/// The empty list has the empty set.
pub proof fn lemma_set_of_empty()
    // Math: set_of([]) = ∅
    ensures
        set_of(Seq::<usize>::empty()) == ISet::<int>::empty(),
{
    // Why: extensionality; no index of the empty list exists.
    assert(set_of(Seq::<usize>::empty()) =~= ISet::<int>::empty());
}

/// Appending a value not yet in the list keeps it free of repeats.
pub proof fn lemma_no_dup_push(s: Seq<usize>, v: usize)
    // Math: s has no repeats ∧ v ∉ set_of(s)
    requires
        s.no_duplicates(),
        !set_of(s).contains(v as int),
    // Math: s · [v] has no repeats
    ensures
        s.push(v).no_duplicates(),
{
    let t = s.push(v);
    // Math: ∀ i ≠ j: t[i] ≠ t[j]
    assert forall|i: int, j: int| 0 <= i < t.len() && 0 <= j < t.len() && i != j implies t[i]
        != t[j] by {
        // Both old: s has no repeats. One of them last (= v): the other is in s, and v ∉ s.
        if i < s.len() && j < s.len() {
            assert(t[i] == s[i] && t[j] == s[j]);
        } else if i < s.len() {
            assert(t[i] == s[i]);
        } else if j < s.len() {
            assert(t[j] == s[j]);
        }
    }
}

} // verus!
