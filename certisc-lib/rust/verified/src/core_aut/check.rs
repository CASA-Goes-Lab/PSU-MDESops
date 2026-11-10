//! The validity checker: decides `g.wf()` (and `g.is_det()`) at run time.
//! Python: `check_automaton` in `core_aut/verified_core/check.py` (`check_code` returns the
//! same result codes).
//!
//! Glossary (in addition to `aut.rs`):
//! - `requires P`: precondition, the caller must establish `P`.
//! - `ensures P`: postcondition, the function guarantees `P`; `r` names the return value.
//! - `invariant P` (on a loop): `P` holds before the loop and after every iteration.
//! - `decreases t`: `t` is a natural number that shrinks every iteration, so the loop ends.
//! - `assert(P)`: a fact the solver must prove here; it is also a hint for later steps.

use crate::core_aut::aut::*;
use vstd::prelude::*;

verus! {

/// Decides `sizes_ok`: the lengths of all the lists agree with `n` and `m`.
pub fn check_sizes(g: &Aut) -> (r: bool)
    // Math: r ↔ sizes_ok(g)
    ensures r == g.sizes_ok(),
{
    // Math: |in_e| = m ∧ |in_euc| = m ∧ |in_euo| = m ∧ |init| = n ∧ |marked| = n
    //       ∧ |start| ≥ 1 ∧ |start| - 1 = n ∧ |dst| = |evt|
    // Why: `|start| - 1 = n` is `|start| = n + 1` written without computing n + 1, which could
    //      overflow when n is the largest machine integer.
    g.in_e.len() == g.m && g.in_euc.len() == g.m && g.in_euo.len() == g.m && g.init.len() == g.n
        && g.marked.len() == g.n && g.start.len() >= 1 && g.start.len() - 1 == g.n
        && g.dst.len() == g.evt.len()
}

/// Decides `blocks_ok`: `start` begins at 0, ends at `T`, and never decreases.
pub fn check_blocks(g: &Aut) -> (r: bool)
    // Math: sizes_ok(g)
    // Why: so start[0] and start[n] can be read.
    requires
        // Why: facts about g, restated in each loop (a loop only knows its invariant).
        g.sizes_ok(),
    // Math: r ↔ blocks_ok(g)
    ensures
        r == g.blocks_ok(),
{
    // Math: start[0] ≠ 0 ∨ start[n] ≠ T → ¬blocks_ok
    if g.start[0] != 0 || g.start[g.n] != g.evt.len() {
        return false;
    }
    // x: the boundaries start[0 ..= x] are checked.
    // Math: x = 0 (x walks the states)
    let mut x: usize = 0;
    while x < g.n
        invariant
            // Why: facts about g are restated: a loop only knows what its invariant says.
            // Why: facts about g, restated in each loop (a loop only knows its invariant).
            g.sizes_ok(),
            g.start@[0] == 0,
            g.start@[g.n as int] == g.num_trans(),
            // Math: 0 ≤ x ≤ n
            x <= g.n,
            // Math: ∀ a, b: 0 ≤ a ≤ b ≤ x → start[a] ≤ start[b]
            // Why: the part of `blocks_ok` established so far.
            forall|a: int, b: int|
                0 <= a <= b <= x ==> #[trigger] g.start@[a] <= #[trigger] g.start@[b],
        // Math: n - x decreases.
        // Math: n - x decreases
        decreases g.n - x,
    {
        // Math: start[x] > start[x+1] → ¬blocks_ok (the pair (x, x+1) breaks it)
        if g.start[x] > g.start[x + 1] {
            return false;
        }
        // Why: hint for the invariant at x + 1: for a ≤ x, start[a] ≤ start[x] ≤ start[x+1].
        assert(forall|a: int| 0 <= a <= x ==> #[trigger] g.start@[a] <= g.start@[x + 1]);
        // Math: x := x + 1
        x += 1;
    }
    // Math: x = n, so the invariant is blocks_ok.
    true
}

/// Decides `sorted_ok`: every block is sorted by event.
pub fn check_sorted(g: &Aut) -> (r: bool)
    // Math: sizes_ok ∧ blocks_ok
    // Why: the blocks are ranges inside evt, so evt[k] can be read for k in a block.
    requires
        // Why: facts about g, restated in each loop (a loop only knows its invariant).
        g.sizes_ok(),
        // Math: blocks_ok(g)
        g.blocks_ok(),
    // Math: r ↔ sorted_ok(g)
    ensures
        r == g.sorted_ok(),
{
    // x: blocks 0 .. x-1 are checked.
    // Math: x = 0 (x walks the states)
    let mut x: usize = 0;
    while x < g.n
        invariant
            // Why: facts about g, restated in each loop (a loop only knows its invariant).
            g.sizes_ok(),
            // Math: blocks_ok(g)
            g.blocks_ok(),
            // Math: 0 ≤ x ≤ n
            x <= g.n,
            // Math: ∀ y ∈ [0, x): blk_sorted(y)
            // Math: ∀ y < x: blk_sorted(y)  (blocks done)
            forall|y: int| 0 <= y < x ==> #[trigger] g.blk_sorted(y),
        // Math: n - x decreases
        decreases g.n - x,
    {
        // Math: lo = start[x], hi = start[x+1]
        // Math: [lo, hi) = x's block
        let lo = g.start[x];
        let hi = g.start[x + 1];
        // Why: hint: lo ≤ hi ≤ T (blocks_ok for the pairs (x, x+1) and (x+1, n)), so the block
        //      lies inside evt.
        assert(g.start@[x as int] <= g.start@[x + 1] <= g.start@[g.n as int]);
        // Math: a block of at most one position is trivially sorted / repeat-free
        if lo < hi {
            // k: positions lo .. k-1 are sorted.
            // Math: k = lo + 1 (k walks the block; compares k-1 and k)
            let mut k: usize = lo + 1;
            while k < hi
                invariant
                    // Why: facts about g, restated in each loop (a loop only knows its invariant).
                    g.sizes_ok(),
                    // Math: x < n
                    // Why: x names a state, so blk_sorted(x) is part of sorted_ok.
                    x < g.n,
                    // Math: lo = start[x], hi = start[x+1] ≤ |evt|
                    lo == g.start@[x as int],
                    hi == g.start@[x + 1],
                    hi <= g.evt@.len(),
                    // Math: lo < k ≤ hi
                    lo < k <= hi,
                    // Math: ∀ a, b: lo ≤ a ≤ b < k → evt[a] ≤ evt[b]
                    forall|a: int, b: int|
                        lo <= a <= b < k ==> #[trigger] g.evt@[a] <= #[trigger] g.evt@[b],
                // Math: hi - k decreases
                decreases hi - k,
            {
                // Math: evt[k-1] > evt[k] → ¬blk_sorted(x) → ¬sorted_ok
                if g.evt[k - 1] > g.evt[k] {
                    // Why: hint: names the block whose `blk_sorted` fails, so the solver uses
                    //      sorted_ok at x.
                    assert(!g.blk_sorted(x as int));
                    return false;
                }
                // Why: hint for the invariant at k + 1: evt[a] ≤ evt[k-1] ≤ evt[k].
                assert(forall|a: int| lo <= a <= k ==> #[trigger] g.evt@[a] <= g.evt@[k as int]);
                // Math: k := k + 1
                k += 1;
            }
        }
        // Math: blk_sorted(x)
        // Why: the inner loop ended with k = hi (or the block has at most one position).
        assert(g.blk_sorted(x as int));
        // Math: x := x + 1
        x += 1;
    }
    true
}

/// Decides `trans_ok`: (W1), and every event and target in range.
pub fn check_trans(g: &Aut) -> (r: bool)
    requires
        // Why: facts about g, restated in each loop (a loop only knows its invariant).
        g.sizes_ok(),
    // Math: r ↔ trans_ok(g)
    ensures
        r == g.trans_ok(),
{
    // k: positions 0 .. k-1 are checked.
    // Math: k = 0 (k walks the transition positions)
    let mut k: usize = 0;
    while k < g.evt.len()
        invariant
            // Why: facts about g, restated in each loop (a loop only knows its invariant).
            g.sizes_ok(),
            // Math: 0 ≤ k ≤ T
            k <= g.evt@.len(),
            // Math: ∀ j ∈ [0, k): evt[j] < m ∧ in_e[evt[j]] ∧ dst[j] < n
            forall|j: int|
                #![trigger g.evt@[j]]
                #![trigger g.dst@[j]]
                0 <= j < k ==> g.evt@[j] < g.m && g.in_e@[g.evt@[j] as int] && g.dst@[j] < g.n,
        // Math: T - k decreases
        decreases g.evt@.len() - k,
    {
        // Math: e = evt[k]
        let e = g.evt[k];
        // Math: e ≥ m ∨ ¬in_e[e] ∨ dst[k] ≥ n → ¬trans_ok (position k breaks it)
        // Why: `||` evaluates left to right, so in_e[e] is read only when e < m = |in_e|.
        if e >= g.m || !g.in_e[e] || g.dst[k] >= g.n {
            return false;
        }
        // Math: k := k + 1
        k += 1;
    }
    true
}

/// Decides `events_ok`: (W2).
pub fn check_events(g: &Aut) -> (r: bool)
    requires
        // Why: facts about g, restated in each loop (a loop only knows its invariant).
        g.sizes_ok(),
    // Math: r ↔ events_ok(g)
    ensures
        r == g.events_ok(),
{
    // e: events 0 .. e-1 are checked.
    // Math: e = 0 (e walks the events)
    let mut e: usize = 0;
    while e < g.m
        invariant
            // Why: facts about g, restated in each loop (a loop only knows its invariant).
            g.sizes_ok(),
            // Math: 0 ≤ e ≤ m
            e <= g.m,
            // Math: ∀ a ∈ [0, e): (in_euc[a] → in_e[a]) ∧ (in_euo[a] → in_e[a])
            forall|a: int|
                #![trigger g.in_euc@[a]]
                #![trigger g.in_euo@[a]]
                0 <= a < e ==> (g.in_euc@[a] ==> g.in_e@[a]) && (g.in_euo@[a] ==> g.in_e@[a]),
        // Math: m - e decreases
        decreases g.m - e,
    {
        // Math: (in_euc[e] ∨ in_euo[e]) ∧ ¬in_e[e] → ¬events_ok
        if (g.in_euc[e] || g.in_euo[e]) && !g.in_e[e] {
            return false;
        }
        // Math: e := e + 1
        e += 1;
    }
    true
}

/// Decides `init_ok`: (W3).
pub fn check_init(g: &Aut) -> (r: bool)
    requires
        // Why: facts about g, restated in each loop (a loop only knows its invariant).
        g.sizes_ok(),
    // Math: r ↔ init_ok(g)
    ensures
        r == g.init_ok(),
{
    // x: states 0 .. x-1 are scanned; `found`: one of them is initial.
    // Math: x = 0 (x walks the states)
    let mut x: usize = 0;
    // Math: found = false
    let mut found = false;
    while x < g.n
        invariant
            // Why: facts about g, restated in each loop (a loop only knows its invariant).
            g.sizes_ok(),
            // Math: 0 ≤ x ≤ n
            x <= g.n,
            // Math: found ↔ ∃ y ∈ [0, x): init[y]
            found == (exists|y: int| 0 <= y < x && #[trigger] g.init@[y]),
        // Math: n - x decreases
        decreases g.n - x,
    {
        // Math: x initial?
        if g.init[x] {
            // Math: found := true
            found = true;
        }
        // Math: x := x + 1
        x += 1;
    }
    // Math: (n > 0) ↔ found
    (g.n > 0) == found
}

/// Decides the first part of `is_det`: at most one initial state.
pub fn check_one_init(g: &Aut) -> (r: bool)
    requires
        // Why: facts about g, restated in each loop (a loop only knows its invariant).
        g.sizes_ok(),
    // Math: r ↔ ∀ x, y ∈ [0, n): init[x] ∧ init[y] → x = y
    ensures
        r == (forall|x: int, y: int|
            0 <= x < g.n && 0 <= y < g.n && #[trigger] g.init@[x] && #[trigger] g.init@[y] ==> x
                == y),
{
    // x: states 0 .. x-1 are scanned; `found`: one of them, `first`, is initial.
    // Math: x = 0 (x walks the states)
    let mut x: usize = 0;
    // Math: found = false
    let mut found = false;
    // Why: ghost: `first` is only used by the proof (the invariant), not by the check.
    let ghost mut first: int = 0;
    while x < g.n
        invariant
            // Why: facts about g, restated in each loop (a loop only knows its invariant).
            g.sizes_ok(),
            // Math: 0 ≤ x ≤ n
            x <= g.n,
            // Math: found → first < x ∧ init[first]
            found ==> 0 <= first < x && g.init@[first],
            // Math: ¬found → ∀ y ∈ [0, x): ¬init[y]
            !found ==> forall|y: int| 0 <= y < x ==> !#[trigger] g.init@[y],
            // Math: ∀ y, z ∈ [0, x): init[y] ∧ init[z] → y = z
            forall|y: int, z: int|
                0 <= y < x && 0 <= z < x && #[trigger] g.init@[y] && #[trigger] g.init@[z] ==> y
                    == z,
        // Math: n - x decreases
        decreases g.n - x,
    {
        // Math: x initial?
        if g.init[x] {
            // Math: found ∧ init[x] → first ≠ x are two initial states
            if found {
                return false;
            }
            // Math: found := true
            found = true;
            proof {
                // Math: first := x
                first = x as int;
            }
        }
        // Math: x := x + 1
        x += 1;
    }
    true
}

/// Decides the second part of `is_det`: no event twice in a block.
pub fn check_det_blocks(g: &Aut) -> (r: bool)
    // Why: sorted blocks let one comparison of neighbours decide it (a repeat is adjacent).
    requires
        // Why: facts about g, restated in each loop (a loop only knows its invariant).
        g.sizes_ok(),
        // Math: blocks_ok(g)
        g.blocks_ok(),
        // Math: sorted_ok(g)
        g.sorted_ok(),
    // Math: r ↔ ∀ x ∈ [0, n): blk_det(x)
    ensures
        r == (forall|x: int| 0 <= x < g.n ==> #[trigger] g.blk_det(x)),
{
    // Math: x = 0 (x walks the states)
    let mut x: usize = 0;
    while x < g.n
        invariant
            // Why: facts about g, restated in each loop (a loop only knows its invariant).
            g.sizes_ok(),
            // Math: blocks_ok(g)
            g.blocks_ok(),
            // Math: sorted_ok(g)
            g.sorted_ok(),
            // Math: 0 ≤ x ≤ n
            x <= g.n,
            // Math: ∀ y ∈ [0, x): blk_det(y)
            // Math: ∀ y < x: blk_det(y)  (blocks done)
            forall|y: int| 0 <= y < x ==> #[trigger] g.blk_det(y),
        // Math: n - x decreases
        decreases g.n - x,
    {
        // Math: [lo, hi) = x's block
        let lo = g.start[x];
        let hi = g.start[x + 1];
        // Why: hint: lo ≤ hi ≤ T, as in check_sorted.
        assert(g.start@[x as int] <= g.start@[x + 1] <= g.start@[g.n as int]);
        // Why: hint: open sorted_ok at x (used when a repeat is found).
        assert(g.blk_sorted(x as int));
        // Math: a block of at most one position is trivially sorted / repeat-free
        if lo < hi {
            // Math: k = lo + 1 (k walks the block; compares k-1 and k)
            let mut k: usize = lo + 1;
            while k < hi
                invariant
                    // Why: facts about g, restated in each loop (a loop only knows its invariant).
                    g.sizes_ok(),
                    // Math: x < n
                    x < g.n,
                    g.blk_sorted(x as int),
                    // Math: lo = start[x], hi = start[x+1] ≤ |evt|
                    lo == g.start@[x as int],
                    hi == g.start@[x + 1],
                    hi <= g.evt@.len(),
                    // Math: lo < k ≤ hi
                    lo < k <= hi,
                    // Math: ∀ a, b: lo ≤ a < b < k → evt[a] < evt[b]
                    // Why: strictly increasing so far; implies no repeat.
                    forall|a: int, b: int|
                        lo <= a < b < k ==> #[trigger] g.evt@[a] < #[trigger] g.evt@[b],
                // Math: hi - k decreases
                decreases hi - k,
            {
                // Math: evt[k-1] ≥ evt[k], and sorted gives evt[k-1] ≤ evt[k], so they are equal.
                if g.evt[k - 1] >= g.evt[k] {
                    // Why: hint: positions k-1 < k carry the same event.
                    assert(g.evt@[k - 1] == g.evt@[k as int]);
                    assert(!g.blk_det(x as int));
                    return false;
                }
                // Why: hint for the invariant at k + 1: evt[a] ≤ evt[k-1] < evt[k].
                assert(forall|a: int| lo <= a < k ==> #[trigger] g.evt@[a] < g.evt@[k as int]);
                // Math: k := k + 1
                k += 1;
            }
        }
        // Math: blk_det(x)
        assert(g.blk_det(x as int));
        // Math: x := x + 1
        x += 1;
    }
    true
}

/// The checker: `r` is true exactly when `g` is a valid automaton (and deterministic, if
/// `det` is asked). Python: `check_automaton`.
pub fn check(g: &Aut, det: bool) -> (r: bool)
    // Math: r ↔ wf(g) ∧ (det → is_det(g))
    ensures
        r == (g.wf() && (det ==> g.is_det())),
{
    // Each check needs the ones before it (to read the lists safely), so they run in order.
    // Math: the checks in order; each needs the earlier ones to read the lists safely
    if !check_sizes(g) {
        return false;
    }
    if !check_blocks(g) {
        return false;
    }
    if !check_sorted(g) {
        return false;
    }
    if !check_trans(g) {
        return false;
    }
    if !check_events(g) {
        return false;
    }
    if !check_init(g) {
        return false;
    }
    if det {
        // Math: is_det ↔ one_init ∧ ∀ x: blk_det(x)
        check_one_init(g) && check_det_blocks(g)
    } else {
        true
    }
}

/// The checker with a reason: `0` exactly when `check(g, det)` is true; otherwise the number
/// of the first condition that fails, as in Python's `check_automaton` (the messages are in
/// `core_aut/trusted/wrapper.py`, `MESSAGES`).
pub fn check_code(g: &Aut, det: bool) -> (r: u8)
    ensures
        // Math: r = 0 ↔ wf(g) ∧ (det → is_det(g))
        // Why: the same guarantee as `check`; the code adds only the reason.
        (r == 0) == (g.wf() && (det ==> g.is_det())),
        // Math: r = 1 → ¬sizes_ok(g)
        // Why: code 1, "sizes": a list has the wrong length.
        r == 1 ==> !g.sizes_ok(),
        // Math: r = 2 → sizes_ok(g) ∧ ¬blocks_ok(g)
        // Why: code 2, the block boundaries `start` are inconsistent.
        r == 2 ==> g.sizes_ok() && !g.blocks_ok(),
        // Math: r = 8 → sizes_ok(g) ∧ blocks_ok(g) ∧ ¬sorted_ok(g)
        // Why: code 8, a block is not sorted by event.
        r == 8 ==> g.sizes_ok() && g.blocks_ok() && !g.sorted_ok(),
        // Math: r = 3 → sizes_ok(g) ∧ ¬trans_ok(g)
        // Why: code 3, a transition has an unknown event, an event not in E, or a bad target.
        r == 3 ==> g.sizes_ok() && !g.trans_ok(),
        // Math: r = 4 → sizes_ok(g) ∧ ¬events_ok(g)
        // Why: code 4, Euc or Euo is not inside E.
        r == 4 ==> g.sizes_ok() && !g.events_ok(),
        // Math: r = 5 → sizes_ok(g) ∧ ¬init_ok(g)
        // Why: code 5, there is no initial state although there are states.
        r == 5 ==> g.sizes_ok() && !g.init_ok(),
        // Math: r ∈ {6, 7} → det ∧ wf(g) ∧ ¬is_det(g)
        // Why: codes 6 (two initial states) and 7 (an event twice in a block): valid, but not
        //      deterministic, and determinism was asked.
        (r == 6 || r == 7) ==> det && g.wf() && !g.is_det(),
        // Math: r ∈ {0, ..., 8}
        r <= 8,
{
    // Math: the checks of `check`, in the same order; each needs the earlier ones.
    if !check_sizes(g) {
        return 1;
    }
    if !check_blocks(g) {
        return 2;
    }
    if !check_sorted(g) {
        return 8;
    }
    if !check_trans(g) {
        return 3;
    }
    if !check_events(g) {
        return 4;
    }
    if !check_init(g) {
        return 5;
    }
    // Math: here wf(g) holds (all six parts passed).
    if det {
        // Math: ¬(∀ x, y: init[x] ∧ init[y] → x = y) → ¬is_det
        if !check_one_init(g) {
            return 6;
        }
        // Math: ¬(∀ x: blk_det(x)) → ¬is_det
        if !check_det_blocks(g) {
            return 7;
        }
    }
    0
}

} // verus!
