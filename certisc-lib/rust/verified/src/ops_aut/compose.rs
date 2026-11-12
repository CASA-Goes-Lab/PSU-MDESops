//! Parallel composition and product with a Lean-level contract (Parallel.lean: `syncF`,
//! `parMode`, `prodMode`, `IsComposition`).
//!
//! `compose_aut` computes the event modes and the output event flags (verified), runs the
//! verified search `parallel::compose`, and proves that the result is a valid automaton and is
//! the composition, stated over the views. The only trusted input is `map2`, the numbering of
//! G2's events in the output (built from event labels in Python).
//!
//! Glossary: as in `aut.rs`, `check.rs`, `reach.rs`; `S.union(T)` is `S ∪ T`.

use crate::core_aut::aut::*;
use crate::ops_aut::parallel::*;
use vstd::prelude::*;

verus! {

/// `d ∈ f2'(b, o)`: G2's transitions with events renamed by `map2` (G2 event `e2` is output
/// event `map2[e2]`).
pub open spec fn f2(g2: AutView, map2: Seq<usize>, b: int, o: int, d: int) -> bool {
    // Math: ∃ e2 ∈ [0, |map2|): map2[e2] = o ∧ d ∈ f2(b, e2)
    exists|e2: int| 0 <= e2 < map2.len() && map2[e2] as int == o && #[trigger] g2.f(b, e2, d)
}

/// The image of a set of G2 events in the output numbering: `map2(S)`.
pub open spec fn img(S: ISet<int>, map2: Seq<usize>) -> ISet<int> {
    // Math: {o | ∃ e2 ∈ S: map2[e2] = o}
    ISet::new(|o: int| exists|e2: int| 0 <= e2 < map2.len() && #[trigger] S.contains(e2) && map2[e2] as int == o)
}

/// The mode of event `o` (Lean: `parMode E1 E2` if `par`, else `prodMode E1 E2`).
pub open spec fn mode_of(par: bool, E1: ISet<int>, E2: ISet<int>, o: int) -> u8 {
    // Math: both if o ∈ E1 ∩ E2; left/right if only in one (parallel); none otherwise
    if E1.contains(o) && E2.contains(o) {
        BOTH
    } else if par && E1.contains(o) {
        LEFT
    } else if par && E2.contains(o) {
        RIGHT
    } else {
        NONE
    }
}

/// `(c, d) ∈ f_mode((a, b), o)` (Lean: `syncF mode f1 f2`).
pub open spec fn sync(g1: AutView, g2: AutView, map2: Seq<usize>, md: u8, a: int, b: int, o: int, c: int, d: int) -> bool {
    // Math: G2 moves on inv2[o]: d ∈ f2(b, inv2[o]), and map2[inv2[o]] = o
    if md == BOTH {
        // Math: c ∈ f1(a, o) ∧ d ∈ f2'(b, o)
        g1.f(a, o, c) && f2(g2, map2, b, o, d)
    } else if md == LEFT {
        // Math: c ∈ f1(a, o) ∧ d = b
        g1.f(a, o, c) && d == b
    } else if md == RIGHT {
        // Math: c = a ∧ d ∈ f2'(b, o)
        c == a && f2(g2, map2, b, o, d)
    } else {
        false
    }
}

/// The composition's move from the pair of output state `i` (labels `p1`, `p2`).
pub open spec fn sync_at(par: bool, g1: AutView, g2: AutView, map2: Seq<usize>, p1: Seq<usize>, p2: Seq<usize>, i: int, o: int, c: int, d: int) -> bool {
    sync(g1, g2, map2, mode_of(par, g1.E, img(g2.E, map2), o), p1[i] as int, p2[i] as int, o, c, d)
}

/// `h` is the composition of `g1` and `g2` with state labels `(p1[i], p2[i])`
/// (Lean: `IsComposition mode G1 G2 H φ`, with `mode` = `parMode`/`prodMode`).
pub open spec fn is_composition(par: bool, g1: AutView, g2: AutView, map2: Seq<usize>, h: AutView, p1: Seq<usize>, p2: Seq<usize>) -> bool {
    // Labels: one pair of states per output state.
    &&& p1.len() == h.n
    &&& p2.len() == h.n
    &&& forall|i: int| 0 <= i < h.n ==> #[trigger] p1[i] < g1.n && p2[i] < g2.n
    // Math: step_sound: j ∈ f_H(i, o) → φ(j) ∈ f_mode(φ(i), o)
    &&& forall|i: int, o: int, j: int| #[trigger] h.f(i, o, j) ==> 0 <= i < h.n && 0 <= j < h.n
        && sync_at(par, g1, g2, map2, p1, p2, i, o, p1[j] as int, p2[j] as int)
    // Math: step_complete: (c, d) ∈ f_mode(φ(i), o) → ∃ j ∈ f_H(i, o): φ(j) = (c, d)
    &&& forall|i: int, o: int, c: int, d: int| 0 <= i < h.n && #[trigger] sync_at(par, g1, g2, map2, p1, p2, i, o, c, d)
        ==> exists|j: int| #[trigger] h.f(i, o, j) && p1[j] as int == c && p2[j] as int == d
    // Math: init_sound: i ∈ X0_H → φ(i) ∈ X01 × X02
    &&& forall|i: int| #[trigger] h.X0.contains(i) ==> g1.X0.contains(p1[i] as int) && g2.X0.contains(p2[i] as int)
    // Math: init_complete: (a, b) ∈ X01 × X02 → ∃ i ∈ X0_H: φ(i) = (a, b)
    &&& forall|a: int, b: int| #[trigger] g1.X0.contains(a) && #[trigger] g2.X0.contains(b)
        ==> exists|i: int| #[trigger] h.X0.contains(i) && p1[i] as int == a && p2[i] as int == b
    // Math: marked: i ∈ Xm_H ↔ p1[i] ∈ Xm1 ∧ p2[i] ∈ Xm2
    &&& forall|i: int| 0 <= i < h.n ==> (#[trigger] h.Xm.contains(i) <==> g1.Xm.contains(p1[i] as int) && g2.Xm.contains(p2[i] as int))
    // Math: E_H = E1 ∪ E2, Euc_H = Euc1 ∪ Euc2, Euo_H = Euo1 ∪ Euo2 (G2's renamed)
    &&& h.E == g1.E.union(img(g2.E, map2))
    &&& h.Euc == g1.Euc.union(img(g2.Euc, map2))
    &&& h.Euo == g1.Euo.union(img(g2.Euo, map2))
}

/// What the trusted event numbering must satisfy (Python `_events`).
pub open spec fn map_ok(g1: &Aut, g2: &Aut, map2: Seq<usize>, m: int) -> bool {
    // Math: one output number per G2 event; m1 ≤ m; every output number below m
    &&& map2.len() == g2.m
    &&& g1.m <= m
    &&& forall|e2: int| 0 <= e2 < map2.len() ==> #[trigger] map2[e2] < m
    // Math: injective: different G2 events, different output events (different labels)
    &&& forall|a: int, b: int| 0 <= a < map2.len() && 0 <= b < map2.len() && a != b ==> #[trigger] map2[a] != #[trigger] map2[b]
    // Math: G2-only events are numbered in G2's order (so blocks come out sorted)
    &&& forall|a: int, b: int| 0 <= a <= b < map2.len() && map2[a] >= g1.m && map2[b] >= g1.m ==> #[trigger] map2[a] <= #[trigger] map2[b]
    // Math: every event of G1's table is in E1 (true for a table built from G1 alone)
    &&& forall|o: int| 0 <= o < g1.m ==> #[trigger] g1.in_e@[o]
}

/// Decides `map_ok` (so the binding only passes what it gets from Python).
pub fn check_map(g1: &Aut, g2: &Aut, map2: &Vec<usize>, m: usize) -> (r: bool)
    requires
        g1.wf(),
        g2.wf(),
    ensures
        r == map_ok(g1, g2, map2@, m as int),
{
    // Math: |map2| ≠ m2 ∨ m1 > m → ¬map_ok
    if map2.len() != g2.m || g1.m > m {
        return false;
    }
    // Every G1 event number is in E1.
    // Math: o = 0 (o walks G1's event numbers)
    let mut o: usize = 0;
    while o < g1.m
        invariant
            g1.wf(),
            o <= g1.m,
            // Math: ∀ a < o: a ∈ E1
            forall|a: int| 0 <= a < o ==> #[trigger] g1.in_e@[a],
        // Math: m1 - o decreases
        decreases g1.m - o,
    {
        // Math: o ∉ E1 → ¬map_ok
        if !g1.in_e[o] {
            return false;
        }
        o += 1;
    }
    // seen[o]: some earlier G2 event maps to o. last: the largest earlier value ≥ m1 (if any).
    // Math: seen = [false] * m
    // Why: seen[o]: some earlier G2 event maps to o (injectivity check).
    let mut seen = crate::ops_aut::reach::falses(m);
    // Math: has_last = false, last = 0
    // Why: the largest earlier value ≥ m1 (order check).
    let mut has_last = false;
    let mut last: usize = 0;
    // Math: e2 = 0 (e2 walks G2's events)
    let mut e2: usize = 0;
    while e2 < map2.len()
        invariant
            g1.wf(),
            g2.wf(),
            map2@.len() == g2.m,
            g1.m <= m,
            forall|a: int| 0 <= a < g1.m ==> #[trigger] g1.in_e@[a],
            e2 <= map2@.len(),
            seen@.len() == m,
            // Math: ∀ a < e2: map2[a] < m
            forall|a: int| 0 <= a < e2 ==> #[trigger] map2@[a] < m,
            // Math: seen[o] ↔ ∃ a < e2: map2[a] = o
            forall|o: int| 0 <= o < m ==> (#[trigger] seen@[o] <==> exists|a: int| 0 <= a < e2 && #[trigger] map2@[a] as int == o),
            // Math: map2 injective on [0, e2)
            forall|a: int, b: int| 0 <= a < e2 && 0 <= b < e2 && a != b ==> #[trigger] map2@[a] != #[trigger] map2@[b],
            // Math: map2 increasing on the new events in [0, e2)
            forall|a: int, b: int| 0 <= a <= b < e2 && map2@[a] >= g1.m && map2@[b] >= g1.m ==> #[trigger] map2@[a] <= #[trigger] map2@[b],
            // Math: has_last ↔ some earlier value is ≥ m1; then last is the largest of them.
            has_last <==> exists|a: int| 0 <= a < e2 && #[trigger] map2@[a] >= g1.m,
            has_last ==> forall|a: int| 0 <= a < e2 && #[trigger] map2@[a] >= g1.m ==> map2@[a] <= last,
            has_last ==> exists|a: int| 0 <= a < e2 && #[trigger] map2@[a] == last && last >= g1.m,
        // Math: |map2| - e2 decreases
        decreases map2@.len() - e2,
    {
        // Math: o = map2[e2]
        let o = map2[e2];
        // Math: o ≥ m → ¬map_ok
        if o >= m {
            return false;
        }
        // Math: o already used → not injective
        if seen[o] {
            // Two G2 events with the same output number.
            // Math: a < e2 with map2[a] = o
            let ghost a = choose|a: int| 0 <= a < e2 && #[trigger] map2@[a] as int == o;
            // Math: map2[a] = map2[e2], a ≠ e2
            assert(map2@[a] == map2@[e2 as int]);
            return false;
        }
        // Math: o is a G2-only event
        if o >= g1.m {
            // Math: an earlier G2-only event has a larger number → not increasing
            if has_last && o < last {
                // An earlier G2-only event has a larger number.
                // Math: a < e2 with map2[a] = last > o
                let ghost a = choose|a: int| 0 <= a < e2 && #[trigger] map2@[a] == last && last >= g1.m;
                // Math: map2[a] > map2[e2] with a < e2
                assert(map2@[a] > map2@[e2 as int]);
                return false;
            }
            // Math: last := o
            has_last = true;
            last = o;
        }
        // Math: seen[o] := true
        seen.set(o, true);
        // Math: e2 := e2 + 1
        e2 += 1;
    }
    true
}

// --- agreement on shared events (spec/parallel.md §9 Q1, §11 Q-B) ----------------------------

/// G2's event `e2` is shared: it is in `E2`, and its output number `map2[e2]` is in `E1`.
pub open spec fn shared(g1: AutView, g2: AutView, map2: Seq<usize>, e2: int) -> bool {
    // Math: e2 ∈ [0, |map2|) ∧ e2 ∈ E2 ∧ map2[e2] ∈ E1
    // Why: only shared events can disagree; a private event has one attribute only.
    &&& 0 <= e2 < map2.len()
    &&& g2.E.contains(e2)
    &&& g1.E.contains(map2[e2] as int)
}

/// The inputs agree on G2's event `e2`: if it is shared, it is uncontrollable in both or in
/// neither, and unobservable in both or in neither.
pub open spec fn agree_at(g1: AutView, g2: AutView, map2: Seq<usize>, e2: int) -> bool {
    // Math: shared(e2) → (map2[e2] ∈ Euc1 ↔ e2 ∈ Euc2) ∧ (map2[e2] ∈ Euo1 ↔ e2 ∈ Euo2)
    // Why: the per-event condition; a named function, so it can be a trigger below.
    shared(g1, g2, map2, e2) ==> {
        &&& g1.Euc.contains(map2[e2] as int) == g2.Euc.contains(e2)
        &&& g1.Euo.contains(map2[e2] as int) == g2.Euo.contains(e2)
    }
}

/// The inputs agree on every shared event (the condition for composing them, §9 Q1).
pub open spec fn agree(g1: AutView, g2: AutView, map2: Seq<usize>) -> bool {
    // Math: ∀ e2 ∈ [0, |map2|): agree_at(e2)
    // Why: the whole condition; trigger `agree_at(e2)`, so a proof opens it per event.
    forall|e2: int| 0 <= e2 < map2.len() ==> #[trigger] agree_at(g1, g2, map2, e2)
}

/// Decides `agree`: `(0, _)` exactly when the inputs agree; else `(1, e2)` (controllability)
/// or `(2, e2)` (observability), with `e2` a shared G2 event on which they disagree.
// Why: `m` is used only in the contract (unused once it is erased).
#[allow(unused_variables)]
pub fn check_agree(g1: &Aut, g2: &Aut, map2: &Vec<usize>, m: usize) -> (r: (u8, usize))
    requires
        // Math: valid inputs and a valid numbering
        // Why: map_ok gives |map2| = m2 (so e2 indexes G2's flags) and map2[e2] < m.
        g1.wf(),
        g2.wf(),
        map_ok(g1, g2, map2@, m as int),
    ensures
        // Math: r.0 ∈ {0, 1, 2}
        r.0 <= 2,
        // Math: r.0 = 0 ↔ agree(G1, G2, map2)
        // Why: the exact answer: 0 is never wrong, and nonzero is never wrong.
        (r.0 == 0) == agree(g1@, g2@, map2@),
        // Math: r.0 = 1 → shared(r.1) ∧ (map2[r.1] ∈ Euc1 ↔ r.1 ∉ Euc2)
        // Why: the event reported for an error really disagrees on controllability.
        r.0 == 1 ==> shared(g1@, g2@, map2@, r.1 as int)
            && g1@.Euc.contains(map2@[r.1 as int] as int) != g2@.Euc.contains(r.1 as int),
        // Math: r.0 = 2 → shared(r.1) ∧ (map2[r.1] ∈ Euo1 ↔ r.1 ∉ Euo2)
        // Why: the same for observability.
        r.0 == 2 ==> shared(g1@, g2@, map2@, r.1 as int)
            && g1@.Euo.contains(map2@[r.1 as int] as int) != g2@.Euo.contains(r.1 as int),
{
    // Math: e2 = 0 (e2 walks G2's events)
    let mut e2: usize = 0;
    while e2 < map2.len()
        invariant
            // Math: the preconditions, restated
            // Why: Verus forgets facts about unchanged values across a loop unless restated.
            g1.wf(),
            g2.wf(),
            map_ok(g1, g2, map2@, m as int),
            // Math: e2 ≤ |map2|
            e2 <= map2@.len(),
            // Math: ∀ a < e2: agree_at(a)
            // Why: the events already walked agree (else the loop returned).
            forall|a: int| 0 <= a < e2 ==> #[trigger] agree_at(g1@, g2@, map2@, a),
        // Math: |map2| - e2 decreases
        decreases map2@.len() - e2,
    {
        // Math: o = map2[e2], the output number of e2
        let o = map2[e2];
        // Math: o < m1 ↔ o ∈ E1 (every G1 number is in E1, map_ok); e2 ∈ E2 ↔ in_e2[e2]
        // Why: the run-time form of shared(e2).
        if o < g1.m && g2.in_e[e2] {
            proof {
                // Math: o ∈ E1
                // Why: hint: map_ok's last line at o, so the view's E1 contains o.
                assert(g1.in_e@[o as int]);
                // Math: shared(e2)
                assert(shared(g1@, g2@, map2@, e2 as int));
            }
            // Math: (o ∈ Euc1) ≠ (e2 ∈ Euc2) → report (1, e2)
            if g1.in_euc[o] != g2.in_euc[e2] {
                // Math: ¬agree_at(e2), so ¬agree
                // Why: hint: names the failing instance of agree's ∀ (its trigger).
                assert(!agree_at(g1@, g2@, map2@, e2 as int));
                return (1, e2);
            }
            // Math: (o ∈ Euo1) ≠ (e2 ∈ Euo2) → report (2, e2)
            if g1.in_euo[o] != g2.in_euo[e2] {
                // Math: ¬agree_at(e2), so ¬agree
                // Why: hint: names the failing instance of agree's ∀ (its trigger).
                assert(!agree_at(g1@, g2@, map2@, e2 as int));
                return (2, e2);
            }
        } else {
            proof {
                // Math: ¬shared(e2): o ∉ E1 (o ≥ m1, outside the view's range) or e2 ∉ E2
                // Why: then agree_at(e2) holds trivially; the solver needs the case named.
                assert(!shared(g1@, g2@, map2@, e2 as int));
            }
        }
        // Math: agree_at(e2)
        // Why: hint: the new instance of the invariant.
        assert(agree_at(g1@, g2@, map2@, e2 as int));
        // Math: e2 := e2 + 1
        e2 += 1;
    }
    // Math: agree (the invariant at e2 = |map2|)
    (0, 0)
}

/// What agreement buys: the composition's `Euc` and `Euo` are each input's own sets on that
/// input's events. So a shared event keeps the controllability (and observability) it has in
/// both inputs, and a private event keeps the one it has in its own input.
pub proof fn lemma_agree_keeps_flags(par: bool, g1: &Aut, g2: &Aut, map2: Seq<usize>, m: int, h: AutView, p1: Seq<usize>, p2: Seq<usize>)
    requires
        // Math: valid inputs, a valid numbering, agreement, and h is their composition
        g1.wf(),
        g2.wf(),
        map_ok(g1, g2, map2, m),
        agree(g1@, g2@, map2),
        is_composition(par, g1@, g2@, map2, h, p1, p2),
    ensures
        // Math: ∀ o ∈ E1: o ∈ Euc_H ↔ o ∈ Euc1, and o ∈ Euo_H ↔ o ∈ Euo1
        // Why: G1's events keep G1's attributes in the output.
        forall|o: int| #[trigger] g1@.E.contains(o) ==> (h.Euc.contains(o) == g1@.Euc.contains(o)
            && h.Euo.contains(o) == g1@.Euo.contains(o)),
        // Math: ∀ e2 ∈ E2: map2[e2] ∈ Euc_H ↔ e2 ∈ Euc2, and map2[e2] ∈ Euo_H ↔ e2 ∈ Euo2
        // Why: G2's events keep G2's attributes in the output (under their output numbers).
        forall|e2: int| 0 <= e2 < map2.len() && #[trigger] g2@.E.contains(e2) ==> (
            h.Euc.contains(map2[e2] as int) == g2@.Euc.contains(e2)
            && h.Euo.contains(map2[e2] as int) == g2@.Euo.contains(e2)),
{
    // --- G1's events ---
    assert forall|o: int| #[trigger] g1@.E.contains(o) implies (h.Euc.contains(o) == g1@.Euc.contains(o)
        && h.Euo.contains(o) == g1@.Euo.contains(o)) by {
        // Math: o ∈ map2(Euc2) → o ∈ Euc1
        // Why: Euc_H = Euc1 ∪ map2(Euc2) (is_composition); the second part adds nothing new.
        if img(g2@.Euc, map2).contains(o) {
            // Math: e with map2[e] = o and e ∈ Euc2
            let e = choose|e: int| 0 <= e < map2.len() && #[trigger] g2@.Euc.contains(e) && map2[e] as int == o;
            // Math: e ∈ E2 (W2 of G2: Euc2 ⊆ E2)
            assert(g2.in_euc@[e]);
            assert(g2@.E.contains(e));
            // Math: shared(e) and agree_at(e) give o ∈ Euc1
            assert(agree_at(g1@, g2@, map2, e));
        }
        // Math: o ∈ map2(Euo2) → o ∈ Euo1 (same argument with Euo)
        if img(g2@.Euo, map2).contains(o) {
            let e = choose|e: int| 0 <= e < map2.len() && #[trigger] g2@.Euo.contains(e) && map2[e] as int == o;
            // Math: e ∈ E2 (W2 of G2: Euo2 ⊆ E2)
            assert(g2.in_euo@[e]);
            assert(g2@.E.contains(e));
            // Math: agree_at(e) gives o ∈ Euo1
            assert(agree_at(g1@, g2@, map2, e));
        }
    }
    // --- G2's events ---
    assert forall|e2: int| 0 <= e2 < map2.len() && #[trigger] g2@.E.contains(e2) implies (
        h.Euc.contains(map2[e2] as int) == g2@.Euc.contains(e2)
        && h.Euo.contains(map2[e2] as int) == g2@.Euo.contains(e2)) by {
        // Math: o = map2[e2]
        let o = map2[e2] as int;
        // Math: e2 ∈ Euc2 → o ∈ map2(Euc2) ⊆ Euc_H
        // Why: the witness of the image is e2 itself.
        if g2@.Euc.contains(e2) {
            assert(img(g2@.Euc, map2).contains(o));
        }
        // Math: e2 ∈ Euo2 → o ∈ map2(Euo2) ⊆ Euo_H
        if g2@.Euo.contains(e2) {
            assert(img(g2@.Euo, map2).contains(o));
        }
        // Math: o ∈ Euc1 → e2 ∈ Euc2
        // Why: o ∈ Euc1 ⊆ E1 (W2 of G1), so e2 is shared and agree_at(e2) applies.
        if g1@.Euc.contains(o) {
            assert(g1.in_euc@[o]);
            assert(g1@.E.contains(o));
            assert(agree_at(g1@, g2@, map2, e2));
        }
        // Math: o ∈ Euo1 → e2 ∈ Euo2 (same argument with Euo)
        if g1@.Euo.contains(o) {
            assert(g1.in_euo@[o]);
            assert(g1@.E.contains(o));
            assert(agree_at(g1@, g2@, map2, e2));
        }
        // Math: o ∈ map2(Euc2) → e2 ∈ Euc2
        // Why: the image's witness e has map2[e] = o = map2[e2], so e = e2 (map2 injective).
        if img(g2@.Euc, map2).contains(o) {
            let e = choose|e: int| 0 <= e < map2.len() && #[trigger] g2@.Euc.contains(e) && map2[e] as int == o;
            // Math: e = e2 (map_ok: injective)
            assert(e == e2);
        }
        // Math: o ∈ map2(Euo2) → e2 ∈ Euo2 (same argument with Euo)
        if img(g2@.Euo, map2).contains(o) {
            let e = choose|e: int| 0 <= e < map2.len() && #[trigger] g2@.Euo.contains(e) && map2[e] as int == o;
            // Math: e = e2 (map_ok: injective)
            assert(e == e2);
        }
    }
}

/// Spike's input condition from the shared validity.
proof fn lemma_aut_ok(g: &Aut)
    requires
        g.wf(),
    ensures
        aut_ok(g, g.m as int),
{
    // Why: adj_le (the spike's neighbour form) is opaque; open it here.
    reveal(adj_le);
    // Math: ∀ x: sorted_blk(g, x) (neighbour form) from blk_sorted(x) (pair form)
    assert forall|x: int| 0 <= x < g.n implies #[trigger] sorted_blk(g, x) by {
        reveal(adj_le);
        // Math: blk_sorted(x)
        assert(g.blk_sorted(x));
    }
}

/// `n` zeros.
fn zeros(n: usize) -> (v: Vec<usize>)
    ensures
        v@.len() == n,
        forall|i: int| 0 <= i < n ==> #[trigger] v@[i] == 0,
{
    let mut v: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            v@.len() == i,
            forall|a: int| 0 <= a < i ==> #[trigger] v@[a] == 0,
        decreases n - i,
    {
        // Math: v := v · [0]
        v.push(0);
        i += 1;
    }
    v
}

/// A copy of a list of numbers.
fn copy_nums(v: &Vec<usize>) -> (w: Vec<usize>)
    ensures
        w@ == v@,
{
    let mut w: Vec<usize> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v@.len(),
            w@ == v@.subrange(0, i as int),
        decreases v@.len() - i,
    {
        // Math: w := w · [v[i]]
        w.push(v[i]);
        i += 1;
        // Math: w = v[0 .. i-1]
        assert(w@ =~= v@.subrange(0, i as int));
    }
    // Math: w = v
    assert(w@ =~= v@);
    w
}

/// G2's event flags in the output numbering: `in2[o]` (with `inv2[o]` the G2 event), `euc2[o]`,
/// `euo2[o]`.
fn renamed_flags(g2: &Aut, map2: &Vec<usize>, m: usize) -> (r: (Vec<bool>, Vec<usize>, Vec<bool>, Vec<bool>))
    requires
        g2.wf(),
        map2@.len() == g2.m,
        forall|e2: int| 0 <= e2 < map2@.len() ==> #[trigger] map2@[e2] < m,
    ensures
        ({
            // Why: names for the parts of the result.
            let (in2, inv2, euc2, euo2) = r;
            // Math: one entry per output event
            &&& in2@.len() == m && inv2@.len() == m && euc2@.len() == m && euo2@.len() == m
            // Math: in2[o] ↔ o ∈ map2(E2), and then inv2[o] is the G2 event of o
            &&& forall|o: int| 0 <= o < m ==> (#[trigger] in2@[o] <==> img(g2@.E, map2@).contains(o))
            &&& forall|o: int| 0 <= o < m && #[trigger] in2@[o] ==> inv2@[o] < g2.m && map2@[inv2@[o] as int] == o && g2.in_e@[inv2@[o] as int]
            &&& forall|o: int| 0 <= o < m ==> (#[trigger] euc2@[o] <==> img(g2@.Euc, map2@).contains(o))
            &&& forall|o: int| 0 <= o < m ==> (#[trigger] euo2@[o] <==> img(g2@.Euo, map2@).contains(o))
        }),
{
    // Math: in2 = euc2 = euo2 = [false] * m, inv2 = [0] * m
    let mut in2 = crate::ops_aut::reach::falses(m);
    let mut inv2 = zeros(m);
    let mut euc2 = crate::ops_aut::reach::falses(m);
    let mut euo2 = crate::ops_aut::reach::falses(m);
    let mut e2: usize = 0;
    while e2 < g2.m
        invariant
            g2.wf(),
            map2@.len() == g2.m,
            forall|e: int| 0 <= e < map2@.len() ==> #[trigger] map2@[e] < m,
            e2 <= g2.m,
            // Math: lengths
            in2@.len() == m && inv2@.len() == m && euc2@.len() == m && euo2@.len() == m,
            // Math: in2[o] ↔ ∃ e < e2: map2[e] = o ∧ e ∈ E2
            forall|o: int| 0 <= o < m ==> (#[trigger] in2@[o] <==> exists|e: int| 0 <= e < e2 && #[trigger] map2@[e] as int == o && g2.in_e@[e]),
            // Math: in2[o] → inv2[o] is a G2 event in E2 with map2[inv2[o]] = o
            forall|o: int| 0 <= o < m && #[trigger] in2@[o] ==> inv2@[o] < g2.m && map2@[inv2@[o] as int] == o && g2.in_e@[inv2@[o] as int],
            // Math: euc2[o] ↔ ∃ e < e2: map2[e] = o ∧ e ∈ Euc2
            forall|o: int| 0 <= o < m ==> (#[trigger] euc2@[o] <==> exists|e: int| 0 <= e < e2 && #[trigger] map2@[e] as int == o && g2.in_euc@[e]),
            // Math: euo2[o] ↔ ∃ e < e2: map2[e] = o ∧ e ∈ Euo2
            forall|o: int| 0 <= o < m ==> (#[trigger] euo2@[o] <==> exists|e: int| 0 <= e < e2 && #[trigger] map2@[e] as int == o && g2.in_euo@[e]),
        // Math: m2 - e2 decreases
        decreases g2.m - e2,
    {
        let o = map2[e2];
        // Math: o < m
        assert(map2@[e2 as int] < m);
        // Math: e2 ∈ E2 → in2[o] := true, inv2[o] := e2
        if g2.in_e[e2] {
            in2.set(o, true);
            inv2.set(o, e2);
        }
        // Math: e2 ∈ Euc2 → euc2[o] := true
        if g2.in_euc[e2] {
            euc2.set(o, true);
        }
        // Math: e2 ∈ Euo2 → euo2[o] := true
        if g2.in_euo[e2] {
            euo2.set(o, true);
        }
        // Math: e2 := e2 + 1
        e2 += 1;
    }
    // The flags are the images: the view's sets are the flags on [0, m2).
    // Math: in2[o] ↔ o ∈ map2(E2)
    assert forall|o: int| 0 <= o < m implies (#[trigger] in2@[o] <==> img(g2@.E, map2@).contains(o)) by {
        if in2@[o] {
            let e = choose|e: int| 0 <= e < g2.m && #[trigger] map2@[e] as int == o && g2.in_e@[e];
            // Math: e ∈ E2: the witness of the image
            assert(g2@.E.contains(e));
        }
    }
    // Math: euc2[o] ↔ o ∈ map2(Euc2)
    assert forall|o: int| 0 <= o < m implies (#[trigger] euc2@[o] <==> img(g2@.Euc, map2@).contains(o)) by {
        if euc2@[o] {
            let e = choose|e: int| 0 <= e < g2.m && #[trigger] map2@[e] as int == o && g2.in_euc@[e];
            // Math: e ∈ Euc2: the witness of the image
            assert(g2@.Euc.contains(e));
        }
    }
    // Math: euo2[o] ↔ o ∈ map2(Euo2)
    assert forall|o: int| 0 <= o < m implies (#[trigger] euo2@[o] <==> img(g2@.Euo, map2@).contains(o)) by {
        if euo2@[o] {
            let e = choose|e: int| 0 <= e < g2.m && #[trigger] map2@[e] as int == o && g2.in_euo@[e];
            // Math: e ∈ Euo2: the witness of the image
            assert(g2@.Euo.contains(e));
        }
    }
    (in2, inv2, euc2, euo2)
}

/// The parallel composition (`par`) or product (`!par`) of `g1` and `g2`: the reachable part,
/// with output state `i` labelled by the pair `(p1[i], p2[i])`. Output events: G1's numbers,
/// and G2's event `e2` is `map2[e2]`.
pub fn compose_aut(g1: &Aut, g2: &Aut, map2: &Vec<usize>, m: usize, par: bool) -> (r: (Aut, Vec<usize>, Vec<usize>))
    requires
        g1.wf(),
        g2.wf(),
        map_ok(g1, g2, map2@, m as int),
        g1.n * g2.n <= u64::MAX,
    ensures
        // Math: the result is a valid automaton
        r.0.wf(),
        // Math: IsComposition(mode, G1, G2, H, φ), φ(i) = (p1[i], p2[i])
        is_composition(par, g1@, g2@, map2@, r.0@, r.1@, r.2@),
{
    // Math: G2's flags in output numbers
    let (in2, inv2, euc2, euo2) = renamed_flags(g2, map2, m);
    // Modes and output flags, event by event.
    // Math: mode = in_e = in_euc = in_euo = []
    let mut mode: Vec<u8> = Vec::new();
    let mut in_e: Vec<bool> = Vec::new();
    let mut in_euc: Vec<bool> = Vec::new();
    let mut in_euo: Vec<bool> = Vec::new();
    // Math: E2' = map2(E2) (ghost name)
    let ghost E2 = img(g2@.E, map2@);
    // Math: o = 0 (o walks the output events)
    let mut o: usize = 0;
    while o < m
        invariant
            g1.wf(),
            g2.wf(),
            map_ok(g1, g2, map2@, m as int),
            // Math: E2' = map2(E2)
            E2 == img(g2@.E, map2@),
            // Math: lengths
            in2@.len() == m && euc2@.len() == m && euo2@.len() == m,
            // Math: in2[o] ↔ o ∈ E2'
            forall|o: int| 0 <= o < m ==> (#[trigger] in2@[o] <==> E2.contains(o)),
            // Math: euc2 = map2(Euc2), euo2 = map2(Euo2)
            forall|o: int| 0 <= o < m ==> (#[trigger] euc2@[o] <==> img(g2@.Euc, map2@).contains(o)),
            forall|o: int| 0 <= o < m ==> (#[trigger] euo2@[o] <==> img(g2@.Euo, map2@).contains(o)),
            o <= m,
            // Math: o entries written
            mode@.len() == o && in_e@.len() == o && in_euc@.len() == o && in_euo@.len() == o,
            // Math: ∀ a < o: mode[a] = parMode/prodMode(E1, E2')(a)
            forall|a: int| 0 <= a < o ==> #[trigger] mode@[a] == mode_of(par, g1@.E, E2, a),
            // Math: ∀ a < o: in_e[a] ↔ a ∈ E1 ∪ E2'
            forall|a: int| 0 <= a < o ==> #[trigger] in_e@[a] == (g1@.E.contains(a) || E2.contains(a)),
            // Math: ∀ a < o: in_euc[a] ↔ a ∈ Euc1 ∪ map2(Euc2)
            forall|a: int| 0 <= a < o ==> #[trigger] in_euc@[a] == (g1@.Euc.contains(a) || img(g2@.Euc, map2@).contains(a)),
            // Math: ∀ a < o: in_euo[a] ↔ a ∈ Euo1 ∪ map2(Euo2)
            forall|a: int| 0 <= a < o ==> #[trigger] in_euo@[a] == (g1@.Euo.contains(a) || img(g2@.Euo, map2@).contains(a)),
        // Math: m - o decreases
        decreases m - o,
    {
        // e1: o is a G1 event (every number of G1's table is in E1, map_ok).
        // Math: e1 ↔ o ∈ E1 (every G1 number is in E1, map_ok)
        let e1 = o < g1.m;
        proof {
            if e1 {
                // Math: o ∈ E1
                assert(g1.in_e@[o as int]);
            }
        }
        // Math: md = both if o ∈ E1 ∩ E2'; left/right if in one (parallel); none otherwise
        let md = if e1 && in2[o] {
            BOTH
        } else if par && e1 {
            LEFT
        } else if par && in2[o] {
            RIGHT
        } else {
            NONE
        };
        // Math: append mode[o], in_e[o] = (o ∈ E1 ∨ o ∈ E2'), and the Euc/Euo unions
        mode.push(md);
        in_e.push(e1 || in2[o]);
        in_euc.push((e1 && g1.in_euc[o]) || euc2[o]);
        in_euo.push((e1 && g1.in_euo[o]) || euo2[o]);
        // Math: o := o + 1
        o += 1;
    }
    // Math: the spike's event description: m1, mode, inv2, map2
    let ev = Events { m1: g1.m, mode, inv2, map2: copy_nums(map2) };
    proof {
        // Math: aut_ok(g1), aut_ok(g2) (the spike's input conditions)
        lemma_aut_ok(g1);
        lemma_aut_ok(g2);
        // ev_ok: modes agree with the number ranges; inv2 in range for shared events.
        // Math: ev_ok: left → e < m1; both → e < m1 ∧ inv2[e] < m2; right → e ≥ m1
        assert forall|e: int| 0 <= e < m implies {
            &&& #[trigger] ev.mode@[e] == LEFT ==> e < ev.m1
            &&& ev.mode@[e] == BOTH ==> e < ev.m1 && ev.inv2@[e] < g2.m
            &&& ev.mode@[e] == RIGHT ==> e >= ev.m1
        } by {
            // The mode computed in the loop is the Lean mode.
            // Math: mode[e] = mode_of(e) (loop invariant)
            assert(ev.mode@[e] == mode_of(par, g1@.E, E2, e));
            // Math: e < m1 → e ∈ E1
            if e < g1.m {
                assert(g1@.E.contains(e));
            }
            // Math: e ∈ E2' → in2[e] (then inv2[e] < m2)
            if E2.contains(e) {
                // Math: in2[e]
                assert(in2@[e]);
            }
        }
        // Math: ev_ok
        assert(ev_ok(&ev, ev.map2@.len() as int));
    }
    // Math: the verified search: composition_ok(g1, g2, ev, st, tr)
    let (st, tr) = compose(g1, g2, &ev, false);
    // Why: ghost copies of the search's output, named by the bridge lemma below.
    let ghost tr0 = tr;
    let ghost st0 = st;
    proof {
        // Math: o ∈ E2' → inv2[o] is the G2 event of o (from in2)
        assert forall|o: int| 0 <= o < m && #[trigger] img(g2@.E, map2@).contains(o) implies ev.inv2@[o] < g2.m
            && ev.map2@[ev.inv2@[o] as int] == o && g2.in_e@[ev.inv2@[o] as int] by {
            // Math: in2[o]
            assert(in2@[o]);
        }
    }
    // Math: h = the output automaton: n = |p1|, flags, init/marked, blocks
    let h = Aut {
        n: st.p1.len(),
        m,
        in_e,
        in_euc,
        in_euo,
        init: st.init,
        marked: st.marked,
        start: tr.start,
        evt: tr.evt,
        dst: tr.dst,
    };
    proof {
        // Math: wf(h) ∧ is_composition(...)
        lemma_compose_view(par, g1, g2, &ev, &st0, &tr0, &h, m as int);
    }
    // Math: (H, p1, p2)
    (h, st.p1, st.p2)
}

/// From the search's postcondition (positions, witnesses) to the view-level statement.
proof fn lemma_compose_view(par: bool, g1: &Aut, g2: &Aut, ev: &Events, st: &Pairs, tr: &Trans, h: &Aut, m: int)
    requires
        g1.wf(),
        g2.wf(),
        map_ok(g1, g2, ev.map2@, m),
        ev.m1 == g1.m,
        ev.mode@.len() == m,
        forall|o: int| 0 <= o < m ==> #[trigger] ev.mode@[o] == mode_of(par, g1@.E, img(g2@.E, ev.map2@), o),
        forall|o: int| 0 <= o < m && #[trigger] img(g2@.E, ev.map2@).contains(o) ==> ev.inv2@[o] < g2.m
            && ev.map2@[ev.inv2@[o] as int] == o && g2.in_e@[ev.inv2@[o] as int],
        composition_ok(g1, g2, ev, st, tr),
        h.n == st.p1@.len(),
        h.m == m,
        h.in_e@.len() == m && h.in_euc@.len() == m && h.in_euo@.len() == m,
        forall|a: int| 0 <= a < m ==> #[trigger] h.in_e@[a] == (g1@.E.contains(a) || img(g2@.E, ev.map2@).contains(a)),
        forall|a: int| 0 <= a < m ==> #[trigger] h.in_euc@[a] == (g1@.Euc.contains(a) || img(g2@.Euc, ev.map2@).contains(a)),
        forall|a: int| 0 <= a < m ==> #[trigger] h.in_euo@[a] == (g1@.Euo.contains(a) || img(g2@.Euo, ev.map2@).contains(a)),
        h.init@ == st.init@,
        h.marked@ == st.marked@,
        h.start@ == tr.start@,
        h.evt@ == tr.evt@,
        h.dst@ == tr.dst@,
    ensures
        h.wf(),
        is_composition(par, g1@, g2@, ev.map2@, h@, st.p1@, st.p2@),
{
    // Why: blk_ok (sound + sorted per block) is opaque in the spike; open it here.
    reveal(blk_ok);
    // Why: short names for the proof.
    let map2 = ev.map2@;
    let E2 = img(g2@.E, map2);
    let n = h.n as int;
    let p1 = st.p1@;
    let p2 = st.p2@;
    // --- h.wf() ---
    // Math: start is monotone (pair form, from the neighbour form)
    lemma_all_le(tr.start@, 0, n + 1);
    // Math: blocks_ok(h)
    assert(h.blocks_ok());
    // Math: ∀ i: blk_sorted(h, i)
    assert forall|i: int| 0 <= i < n implies #[trigger] h.blk_sorted(i) by {
        // Math: blk_done(i): block i is sound, sorted and complete
        assert(blk_done(tr, st, g1, g2, ev, i));
        // Math: block i sorted (pair form)
        lemma_all_le(tr.evt@, tr.start@[i] as int, tr.start@[i + 1] as int);
    }
    // Math: trans_ok(h): evt[k] < m, evt[k] ∈ E (mode ≠ none), dst[k] < n
    assert forall|k: int| 0 <= k < h.num_trans() implies h.evt@[k] < h.m && h.in_e@[#[trigger] h.evt@[k] as int] && h.dst@[k] < h.n by {
        // Math: evt[k] < m
        assert(tr.evt@[k] < ev.mode@.len());
    }
    // Why: the same fact, with the other trigger (dst[k]).
    assert forall|k: int| 0 <= k < h.num_trans() implies h.evt@[k] < h.m && h.in_e@[h.evt@[k] as int] && #[trigger] h.dst@[k] < h.n by {
        // Math: evt[k] < m
        assert(tr.evt@[k] < ev.mode@.len());
    }
    // Math: events_ok(h): Euc ⊆ E, Euo ⊆ E (W2 of g1 and g2)
    assert forall|o: int| 0 <= o < m implies (#[trigger] h.in_euc@[o] ==> h.in_e@[o]) && (h.in_euo@[o] ==> h.in_e@[o]) by {
        // Math: o = map2[e], e ∈ Euc2
        if img(g2@.Euc, map2).contains(o) {
            let e = choose|e: int| 0 <= e < map2.len() && #[trigger] g2@.Euc.contains(e) && map2[e] as int == o;
            // W2 of G2: Euc2 ⊆ E2, so e ∈ E2 and o = map2[e] ∈ map2(E2).
            assert(g2.in_euc@[e]);
            assert(g2@.E.contains(e));
            // Math: o ∈ E2'
            assert(E2.contains(o));
        }
        // Math: o = map2[e], e ∈ Euo2
        if img(g2@.Euo, map2).contains(o) {
            let e = choose|e: int| 0 <= e < map2.len() && #[trigger] g2@.Euo.contains(e) && map2[e] as int == o;
            // W2 of G2: Euo2 ⊆ E2, so e ∈ E2 and o = map2[e] ∈ map2(E2).
            assert(g2.in_euo@[e]);
            assert(g2@.E.contains(e));
            // Math: o ∈ E2'
            assert(E2.contains(o));
        }
    }
    // Why: the same fact, with the other trigger.
    assert forall|o: int| 0 <= o < m implies (h.in_euc@[o] ==> h.in_e@[o]) && (#[trigger] h.in_euo@[o] ==> h.in_e@[o]) by {
        // Why: hint: the instance above.
        assert(h.in_euc@[o] ==> h.in_e@[o]);
    }
    // Math: init_ok(h): with states, an initial one (composition_ok)
    if n > 0 {
        // Math: i with init[i]
        let i = choose|i: int| 0 <= i < n && #[trigger] st.init@[i];
        // Math: init[i]
        assert(h.init@[i]);
    }
    // Math: wf(h)
    assert(h.wf());
    // --- step_sound ---
    // Math: step_sound: j ∈ f_H(i, o) → (p1[j], p2[j]) ∈ f_mode((p1[i], p2[i]), o)
    assert forall|i: int, o: int, j: int| #[trigger] h@.f(i, o, j) implies 0 <= i < n && 0 <= j < n
        && sync_at(par, g1@, g2@, map2, p1, p2, i, o, p1[j] as int, p2[j] as int) by {
        // Math: k: the output position of i --o--> j
        let k = choose|k: int| #[trigger] h.in_blk(i, k) && h.evt@[k] as int == o && h.dst@[k] as int == j;
        // Math: blk_done(i): block i is sound, sorted and complete
        assert(blk_done(tr, st, g1, g2, ev, i));
        // Math: k ∈ block(i)
        assert(tr.start@[i] <= k < tr.start@[i + 1]);
        // Math: sound_at(i, k): move_by with witnesses w1[k], w2[k]
        assert(sound_at(tr, st, g1, g2, ev, i, k));
        // Math: evt[k] < m
        assert(tr.evt@[k] < ev.mode@.len());
        // Math: (a, b) = φ(i), (c, d) = φ(j)
        let (a, b, c, d) = (p1[i] as int, p2[i] as int, p1[j] as int, p2[j] as int);
        // Math: k1, k2: the G1 and G2 positions used
        let (k1, k2) = (tr.w1@[k], tr.w2@[k]);
        // Math: md = mode[o]
        let md = ev.mode@[o];
        // Math: G1 moves: c ∈ f1(a, o) by position k1
        if md == LEFT || md == BOTH {
            // Math: k1 ∈ block1(a)
            assert(g1.in_blk(a, k1));
            // Math: a --o--> c in G1
            assert(g1.trans(a, o, c));
        }
        if md == BOTH {
            assert(g2.in_blk(b, k2));
            // Math: b --inv2[o]--> d in G2
            assert(g2.trans(b, ev.inv2@[o] as int, d));
            // Math: the witness e2 = inv2[o] of f2'
            assert(g2@.f(b, ev.inv2@[o] as int, d));
        }
        // Math: G2 moves on evt2[k2], and map2[evt2[k2]] = o
        if md == RIGHT {
            assert(g2.in_blk(b, k2));
            // Math: b --evt2[k2]--> d in G2
            assert(g2.trans(b, g2.evt@[k2] as int, d));
            // Math: the witness e2 = evt2[k2] of f2'
            assert(g2@.f(b, g2.evt@[k2] as int, d));
            // Math: evt2[k2] < m2 = |map2|
            assert(g2.evt@[k2] < g2.m);
        }
    }
    // --- step_complete ---
    // Math: step_complete: (c, d) ∈ f_mode(φ(i), o) → ∃ j ∈ f_H(i, o): φ(j) = (c, d)
    assert forall|i: int, o: int, c: int, d: int| 0 <= i < n && #[trigger] sync_at(par, g1@, g2@, map2, p1, p2, i, o, c, d)
        implies exists|j: int| #[trigger] h@.f(i, o, j) && p1[j] as int == c && p2[j] as int == d by {
        // Math: (a, b) = φ(i)
        let (a, b) = (p1[i] as int, p2[i] as int);
        // Math: md = mode_of(o)
        let md = mode_of(par, g1@.E, E2, o);
        // 0 ≤ o < m: some side moves on o, so o is an event of G1 or of G2 (renamed).
        // Math: md ≠ none (sync is false for none)
        assert(md != NONE);
        // Math: o ∈ E1 or o ∈ E2' (else md = none), so 0 ≤ o < m
        if g1@.E.contains(o) {
        } else {
            // Math: o = map2[e] < m
            let e = choose|e: int| 0 <= e < map2.len() && #[trigger] g2@.E.contains(e) && map2[e] as int == o;
        }
        // Math: 0 ≤ o < m
        assert(0 <= o < m);
        // Math: mode[o] = md
        assert(ev.mode@[o] == md);
        // The witnesses k1 (G1 position) and k2 (G2 position) of the move.
        // k1: the G1 position (-1 if G1 stays); e2, k2: the G2 event and position (-1 if G2 stays).
        let k1: int = if md == LEFT || md == BOTH {
            choose|k: int| #[trigger] g1.in_blk(a, k) && g1.evt@[k] as int == o && g1.dst@[k] as int == c
        } else {
            -1
        };
        let e2: int = if md == RIGHT || md == BOTH {
            choose|e2: int| 0 <= e2 < map2.len() && map2[e2] as int == o && #[trigger] g2@.f(b, e2, d)
        } else {
            0
        };
        let k2: int = if md == RIGHT || md == BOTH {
            choose|k: int| #[trigger] g2.in_blk(b, k) && g2.evt@[k] as int == e2 && g2.dst@[k] as int == d
        } else {
            -1
        };
        if md == BOTH {
            // map2 is injective: the G2 event of o is inv2[o].
            // Math: o ∈ E2'
            assert(E2.contains(o));
            // Math: map2[inv2[o]] = o
            assert(map2[ev.inv2@[o] as int] == o);
            // Math: e2 = inv2[o] (map2 injective)
            assert(e2 == ev.inv2@[o]);
        }
        // Math: move_by(a, b, o, c, d, k1, k2): the spike's form of the move
        assert(move_by(g1, g2, ev, a, b, o, c, d, k1, k2));
        // Math: blk_done(i): block i is sound, sorted and complete
        assert(blk_done(tr, st, g1, g2, ev, i));
        // Math: complete(i): the move is emitted in block i
        assert(found_in(tr, st, tr.start@[i] as int, tr.start@[i + 1] as int, o, c, d));
        // Math: k ∈ block(i): evt[k] = o, φ(dst[k]) = (c, d)
        let k = choose|k: int| tr.start@[i] <= k < tr.start@[i + 1] && #[trigger] tr.evt@[k] as int == o
            && st.p1@[tr.dst@[k] as int] as int == c && st.p2@[tr.dst@[k] as int] as int == d;
        // j: the output state reached; it is labelled (c, d).
        let j = tr.dst@[k] as int;
        // Math: k ∈ block_H(i)
        assert(h.in_blk(i, k));
        // Math: i --o--> j in H
        assert(h.trans(i, o, j));
        // Math: j ∈ f_H(i, o): the witness
        assert(h@.f(i, o, j));
        // Math: φ(j) = (c, d)
        assert(p1[j] as int == c && p2[j] as int == d);
    }
    // --- init, marked ---
    // Math: init_complete: (a, b) ∈ X01 × X02 → ∃ i ∈ X0_H: φ(i) = (a, b)
    assert forall|a: int, b: int| #[trigger] g1@.X0.contains(a) && #[trigger] g2@.X0.contains(b)
        implies exists|i: int| #[trigger] h@.X0.contains(i) && p1[i] as int == a && p2[i] as int == b by {
        // Math: init1[a] ∧ init2[b]
        assert(g1.init@[a] && g2.init@[b]);
        // Math: i with φ(i) = (a, b) (composition_ok)
        let i = choose|i: int| 0 <= i < n && #[trigger] st.p1@[i] == a && st.p2@[i] == b;
        // Math: i ∈ X0_H (init[i] = init1[a] ∧ init2[b])
        assert(h@.X0.contains(i));
    }
    // Math: init_sound: i ∈ X0_H → φ(i) ∈ X01 × X02
    assert forall|i: int| #[trigger] h@.X0.contains(i) implies g1@.X0.contains(p1[i] as int) && g2@.X0.contains(p2[i] as int) by {
        // Math: p1[i] < n1 (composition_ok)
        assert(st.p1@[i] < g1.n);
    }
    // Math: marked: i ∈ Xm_H ↔ p1[i] ∈ Xm1 ∧ p2[i] ∈ Xm2
    assert forall|i: int| 0 <= i < n implies (#[trigger] h@.Xm.contains(i) <==> g1@.Xm.contains(p1[i] as int) && g2@.Xm.contains(p2[i] as int)) by {
        // Math: p1[i] < n1 (composition_ok)
        assert(st.p1@[i] < g1.n);
    }
    // Math: labels in range
    assert forall|i: int| 0 <= i < n implies #[trigger] p1[i] < g1.n && p2[i] < g2.n by {
        // Math: p1[i] < n1 (composition_ok)
        assert(st.p1@[i] < g1.n);
    }
    // --- events ---
    // Math: E_H = E1 ∪ E2'
    assert(h@.E =~= g1@.E.union(E2));
    // Math: Euc_H = Euc1 ∪ map2(Euc2)
    assert(h@.Euc =~= g1@.Euc.union(img(g2@.Euc, map2)));
    // Math: Euo_H = Euo1 ∪ map2(Euo2)
    assert(h@.Euo =~= g1@.Euo.union(img(g2@.Euo, map2)));
}

} // verus!
