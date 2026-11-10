//! Parallel composition / product: the search (from the spike, `compose_core`), on the shared
//! `Aut` type. Spec: certisc-proof/spec/parallel.md, section 3. The Lean-level contract is in
//! `compose.rs` (`compose_aut`, `is_composition`); this file states and proves the search in
//! terms of positions (`composition_ok`).
//!
//! Glossary (in addition to `aut.rs`, `check.rs`, `reach.rs`, `delete.rs`):
//! - `#[verifier::opaque]`: the body of a spec fn is hidden; `reveal(f)` opens it inside one
//!   proof. Used for big bundles so the solver does not unfold them everywhere (its budget, the
//!   "rlimit", would run out).
//! - `by (nonlinear_arith)`: prove an arithmetic fact with products of variables (the solver's
//!   default arithmetic is linear); `requires` lists the only facts it may use.
//! - `HashMapWithView<u64, usize>`: Rust's hash map; `map@` is its mathematical map.
//! - `Set<int>`: a finite mathematical set (vstd); `s.len()`: its size.
//! - `&mut x` parameters: `old(x)` is the value at the call, `final(x)` at the return.
//! - `global size_of usize == 8`: the code assumes 64-bit machines (checked by the compiler).

use crate::core_aut::aut::Aut;
use vstd::hash_map::HashMapWithView;
use vstd::prelude::*;

verus! {

// Math: |usize| = 64 bits
// Why: pair keys x1 * n2 + x2 are stored as u64 and converted to usize.
global size_of usize == 8;

// Event modes (Lean `Mode`): NONE: no move; LEFT: only G1 moves; RIGHT: only G2 moves;
// BOTH: both move.
pub const NONE: u8 = 0;
pub const LEFT: u8 = 1;
pub const RIGHT: u8 = 2;
pub const BOTH: u8 = 3;
// Math: ABSENT = 2^64 - 1
// Why: the dense table's "no state yet" entry (never a state number).
pub const ABSENT: usize = usize::MAX;
// Math: DENSE_MAX = 2^26
// Why: use the dense table (one entry per pair) when n1 · n2 ≤ 2^26, else the hash map.
pub const DENSE_MAX: u64 = 67108864;


// The event description: m1 = G1's event count; mode[e] for each output event e;
// inv2[e] = the G2 event of a shared event e; map2[e2] = the output number of G2 event e2.
pub struct Events {
    pub m1: usize,
    pub mode: Vec<u8>,
    pub inv2: Vec<usize>,
    pub map2: Vec<usize>,
}

// The output states: state i is the pair (p1[i], p2[i]), with its flags.
pub struct Pairs {
    pub p1: Vec<usize>,
    pub p2: Vec<usize>,
    pub init: Vec<bool>,
    pub marked: Vec<bool>,
}

// The output transitions, grouped by source (as `Aut`), the determinism flag, and two ghost
// lists: w1[k], w2[k] = the G1 and G2 positions output position k comes from (-1: stays).
pub struct Trans {
    pub start: Vec<usize>,
    pub evt: Vec<usize>,
    pub dst: Vec<usize>,
    pub det: bool,
    pub w1: Ghost<Seq<int>>,
    pub w2: Ghost<Seq<int>>,
}

// The table of pairs found: `tab` (dense: tab[key] = state or ABSENT) or `map` (hash map
// key → state); `used`: the set of keys present (ghost).
pub struct Seen {
    pub dense: bool,
    pub tab: Vec<usize>,
    pub map: HashMapWithView<u64, usize>,
    pub used: Ghost<Set<int>>,
}

// ---------------------------------------------------------------------------------------------
// Specs
// ---------------------------------------------------------------------------------------------

// The key of the pair (a, b): a · n2 + b (distinct pairs, distinct keys).
pub open spec fn key(a: int, b: int, n2: int) -> int {
    a * n2 + b
}

#[verifier::opaque]
// s[lo .. hi-1] is sorted, in neighbour form.
pub open spec fn adj_le(s: Seq<usize>, lo: int, hi: int) -> bool {
    // Math: ∀ k: lo ≤ k ∧ k + 1 < hi → s[k] ≤ s[k+1]
    // Why: opaque: its trigger s[k] creates s[k+1] (a matching loop); revealed only where needed.
    forall|k: int| lo <= k && k + 1 < hi ==> #[trigger] s[k] <= s[k + 1]
}

// s[lo .. hi-1] is sorted, in pair form.
pub open spec fn all_le(s: Seq<usize>, lo: int, hi: int) -> bool {
    // Math: ∀ k ≤ l in [lo, hi): s[k] ≤ s[l]
    forall|k: int, l: int| lo <= k <= l < hi ==> #[trigger] s[k] <= #[trigger] s[l]
}

// s[lo .. hi-1] is strictly increasing (no repeated event: determinism).
pub open spec fn strict(s: Seq<usize>, lo: int, hi: int) -> bool {
    // Math: ∀ k: lo ≤ k ∧ k + 1 < hi → s[k] < s[k+1]
    forall|k: int| lo <= k && k + 1 < hi ==> #[trigger] s[k] < s[k + 1]
}

// State x's block is sorted by event (neighbour form).
pub open spec fn sorted_blk(g: &Aut, x: int) -> bool {
    // Math: adj_le(evt, start[x], start[x+1])
    adj_le(g.evt@, g.start@[x] as int, g.start@[x + 1] as int)
}

// The search's input condition on one automaton with m event numbers (follows from wf:
// `compose.rs`, `lemma_aut_ok`).
pub open spec fn aut_ok(g: &Aut, m: int) -> bool {
    // Math: |init| = |marked| = n, |start| = n + 1, |dst| = |evt|
    &&& g.init@.len() == g.n
    &&& g.marked@.len() == g.n
    &&& g.start@.len() == g.n + 1
    &&& g.dst@.len() == g.evt@.len()
    // Math: start[0] = 0, start[n] = T, start sorted
    &&& g.start@[0] == 0
    &&& g.start@[g.n as int] == g.evt@.len()
    &&& adj_le(g.start@, 0, g.n + 1)
    // Math: ∀ k: evt[k] < m ∧ dst[k] < n
    &&& forall|k: int| 0 <= k < g.evt@.len() ==> #[trigger] g.evt@[k] < m && g.dst@[k] < g.n
    // Math: ∀ x < n: block x sorted
    &&& forall|x: int| 0 <= x < g.n ==> #[trigger] sorted_blk(g, x)
}

// The event description is consistent (m2: G2's event count).
pub open spec fn ev_ok(ev: &Events, m2: int) -> bool {
    // Math: m = |mode|, the number of output events
    let m = ev.mode@.len();
    // Math: m1 ≤ m, |inv2| = m, |map2| = m2, ∀ e2: map2[e2] < m
    &&& ev.m1 <= m
    &&& ev.inv2@.len() == m
    &&& ev.map2@.len() == m2
    &&& forall|e2: int| 0 <= e2 < m2 ==> #[trigger] ev.map2@[e2] < m
    // Math: ∀ e < m: left → e < m1; both → e < m1 ∧ inv2[e] < m2; right → e ≥ m1
    // Why: G1's events come first, so a block's LEFT/BOTH moves come before its RIGHT ones
    //      (blocks come out sorted with no sorting).
    &&& forall|e: int|
        0 <= e < m ==> {
            &&& #[trigger] ev.mode@[e] == LEFT ==> e < ev.m1
            &&& ev.mode@[e] == BOTH ==> e < ev.m1 && ev.inv2@[e] < m2
            &&& ev.mode@[e] == RIGHT ==> e >= ev.m1
        }
    // Math: map2 is increasing on the G2-only events (≥ m1)
    // Why: RIGHT moves, emitted in G2's block order, come out sorted.
    &&& forall|i: int, j: int|
        0 <= i <= j < m2 && ev.map2@[i] >= ev.m1 && ev.map2@[j] >= ev.m1 ==> #[trigger] ev.map2@[i]
            <= #[trigger] ev.map2@[j]
}

// Position k belongs to state x's block (same as Aut::in_blk).
pub open spec fn in_blk(g: &Aut, x: int, k: int) -> bool {
    // Math: x ∈ [0, n) ∧ start[x] ≤ k < start[x+1]
    0 <= x < g.n && g.start@[x] <= k < g.start@[x + 1]
}

/// A move of the composition from (a, b) by output event e to (c, d), using G1 transition k1
/// and G2 transition k2 (-1: that side stays).
pub open spec fn move_by(
    g1: &Aut,
    g2: &Aut,
    ev: &Events,
    a: int,
    b: int,
    e: int,
    c: int,
    d: int,
    k1: int,
    k2: int,
) -> bool {
    // Math: LEFT: k1 ∈ block1(a), evt1[k1] = e, dst1[k1] = c, k2 = -1, d = b
    0 <= e < ev.mode@.len() && if ev.mode@[e] == LEFT {
        in_blk(g1, a, k1) && g1.evt@[k1] as int == e && g1.dst@[k1] as int == c && k2 == -1 && d
            == b
    // Math: BOTH: as LEFT for G1, and k2 ∈ block2(b), evt2[k2] = inv2[e], dst2[k2] = d
    } else if ev.mode@[e] == BOTH {
        in_blk(g1, a, k1) && g1.evt@[k1] as int == e && g1.dst@[k1] as int == c && in_blk(
            g2,
            b,
            k2,
        ) && g2.evt@[k2] == ev.inv2@[e] && g2.dst@[k2] as int == d
    // Math: RIGHT: k1 = -1, c = a, k2 ∈ block2(b), map2[evt2[k2]] = e, dst2[k2] = d
    } else if ev.mode@[e] == RIGHT {
        k1 == -1 && c == a && in_blk(g2, b, k2) && ev.map2@[g2.evt@[k2] as int] as int == e
            && g2.dst@[k2] as int == d
    // Math: NONE: no move
    } else {
        false
    }
}

#[verifier::opaque]
// The output states so far: labels in range, flags right; the first n0 are exactly the
// initial pairs.
pub open spec fn pairs_ok(st: &Pairs, g1: &Aut, g2: &Aut, n0: int) -> bool {
    // Math: n = |p1|
    let n = st.p1@.len();
    // Math: |p2| = |init| = |marked| = n, 0 ≤ n0 ≤ n
    // Math: |p2| = |init| = |marked| = n
    &&& st.p2@.len() == n
    &&& st.init@.len() == n
    &&& st.marked@.len() == n
    &&& 0 <= n0 <= n
    &&& forall|i: int|
        0 <= i < n ==> {
            // Math: p1[i] < n1, p2[i] < n2
            &&& #[trigger] st.p1@[i] < g1.n
            &&& st.p2@[i] < g2.n
            // Math: marked[i] = marked1[p1[i]] ∧ marked2[p2[i]]
            &&& st.marked@[i] == (g1.marked@[st.p1@[i] as int] && g2.marked@[st.p2@[i] as int])
            // Math: init[i] ↔ i < n0 ↔ init1[p1[i]] ∧ init2[p2[i]]
            &&& st.init@[i] == (i < n0)
            &&& (i < n0) == (g1.init@[st.p1@[i] as int] && g2.init@[st.p2@[i] as int])
        }
}

// Key x is in the table.
pub open spec fn in_tab(seen: &Seen, x: int) -> bool {
    // Math: dense: x < |tab| ∧ tab[x] ≠ ABSENT; hash: x ∈ dom(map)
    if seen.dense {
        0 <= x < seen.tab@.len() && seen.tab@[x] != ABSENT
    } else {
        seen.map@.contains_key(x as u64)
    }
}

// The state stored for key x.
pub open spec fn tab_at(seen: &Seen, x: int) -> int {
    // Math: dense: tab[x]; hash: map[x]
    if seen.dense {
        seen.tab@[x] as int
    } else {
        seen.map@[x as u64] as int
    }
}

#[verifier::opaque]
// The table matches the states (np = n1 · n2 = the number of keys).
pub open spec fn seen_ok(seen: &Seen, st: &Pairs, n2: int, np: int) -> bool {
    // Math: dense → |tab| = np
    &&& seen.dense ==> seen.tab@.len() == np
    // Math: |used| = n (one key per state)
    // Why: bounds the number of states by np (termination, lemma_used_bound).
    &&& seen.used@.len() == st.p1@.len()
    // Math: used ⊆ [0, np)
    &&& forall|x: int| #[trigger] seen.used@.contains(x) ==> 0 <= x < np
    // Math: ∀ x < np: in_tab(x) ↔ x ∈ used
    &&& forall|x: int| 0 <= x < np ==> (#[trigger] in_tab(seen, x) == seen.used@.contains(x))
    &&& forall|x: int|
        // Math: in_tab(x) → tab_at(x) < n ∧ key(p1[tab_at(x)], p2[tab_at(x)]) = x
        // Why: the table's state for x is the pair with that key.
        0 <= x < np && #[trigger] in_tab(seen, x) ==> {
            &&& 0 <= tab_at(seen, x) < st.p1@.len()
            &&& key(st.p1@[tab_at(seen, x)] as int, st.p2@[tab_at(seen, x)] as int, n2) == x
        }
}

/// Every initial pair is in the table.
#[verifier::opaque]
// Math: ∀ a ∈ X01, b ∈ X02: key(a, b) ∈ table
pub open spec fn init_in(seen: &Seen, g1: &Aut, g2: &Aut) -> bool {
    forall|a: int, b: int|
        0 <= a < g1.n && 0 <= b < g2.n && #[trigger] g1.init@[a] && #[trigger] g2.init@[b] ==> in_tab(
            seen,
            key(a, b, g2.n as int),
        )
}

// st extends st0: the old states are unchanged (the list only grows).
pub open spec fn ext_pairs(st0: &Pairs, st: &Pairs) -> bool {
    // Math: |p1_0| ≤ |p1| ∧ ∀ i < |p1_0|: p1[i] = p1_0[i] ∧ p2[i] = p2_0[i]
    &&& st0.p1@.len() <= st.p1@.len()
    &&& forall|i: int|
        #![trigger st.p1@[i]]
        #![trigger st0.p1@[i]]
        0 <= i < st0.p1@.len() ==> st.p1@[i] == st0.p1@[i] && st.p2@[i] == st0.p2@[i]
}

// tr extends tr0: old positions and block starts unchanged.
pub open spec fn ext_trans(tr0: &Trans, tr: &Trans) -> bool {
    // Math: positions k < |evt_0| keep evt, dst, w1, w2; starts x < |start_0| keep start
    &&& tr0.evt@.len() <= tr.evt@.len()
    &&& forall|k: int|
        #![trigger tr.evt@[k]]
        #![trigger tr0.evt@[k]]
        0 <= k < tr0.evt@.len() ==> tr.evt@[k] == tr0.evt@[k] && tr.dst@[k] == tr0.dst@[k]
            && tr.w1@[k] == tr0.w1@[k] && tr.w2@[k] == tr0.w2@[k]
    &&& tr0.start@.len() <= tr.start@.len()
    &&& forall|x: int|
        #![trigger tr.start@[x]]
        #![trigger tr0.start@[x]]
        0 <= x < tr0.start@.len() ==> tr.start@[x] == tr0.start@[x]
}

// Math: ∀ k: dst[k] < n (targets are states)
pub open spec fn dst_in(tr: &Trans, st: &Pairs) -> bool {
    forall|k: int| 0 <= k < tr.evt@.len() ==> #[trigger] tr.dst@[k] < st.p1@.len()
}

#[verifier::opaque]
// The transition lists so far: equal lengths, targets are states, every event has a mode.
pub open spec fn tr_ok(tr: &Trans, st: &Pairs, ev: &Events) -> bool {
    // Math: t = |evt|; |dst| = |w1| = |w2| = t; dst_in
    let t = tr.evt@.len();
    &&& tr.dst@.len() == t
    &&& tr.w1@.len() == t
    &&& tr.w2@.len() == t
    &&& dst_in(tr, st)
    &&& forall|k: int|
        // Math: ∀ k < t: evt[k] < m ∧ mode[evt[k]] ≠ NONE
        0 <= k < t ==> {
            &&& #[trigger] tr.evt@[k] < ev.mode@.len()
            &&& ev.mode@[tr.evt@[k] as int] != NONE
        }
}

// Position k of block i is a move of the composition from state i to state dst[k], with
// witnesses w1[k], w2[k].
pub open spec fn sound_at(
    tr: &Trans,
    st: &Pairs,
    g1: &Aut,
    g2: &Aut,
    ev: &Events,
    i: int,
    k: int,
) -> bool {
    // Math: (e, c, d, k1, k2) is a move from φ(h)
    move_by(
        g1,
        g2,
        ev,
        st.p1@[i] as int,
        st.p2@[i] as int,
        tr.evt@[k] as int,
        st.p1@[tr.dst@[k] as int] as int,
        st.p2@[tr.dst@[k] as int] as int,
        tr.w1@[k],
        tr.w2@[k],
    )
}

// Some position in [lo, hi) carries event e to a state labelled (c, d).
pub open spec fn found_in(
    tr: &Trans,
    st: &Pairs,
    lo: int,
    hi: int,
    e: int,
    c: int,
    d: int,
) -> bool {
    // Math: ∃ k ∈ [lo, hi): evt[k] = e ∧ φ(dst[k]) = (c, d)
    exists|k: int|
        lo <= k < hi && #[trigger] tr.evt@[k] as int == e && st.p1@[tr.dst@[k] as int] as int == c
            && st.p2@[tr.dst@[k] as int] as int == d
}

// The moves already walked: G1 positions before a1; at a1, G2 positions before b1; RIGHT
// moves (k1 = -1) with G2 positions before a2.
pub open spec fn covered(k1: int, k2: int, a1: int, b1: int, a2: int) -> bool {
    // Math: k1 ∈ [0, a1) ∨ (k1 = a1 ∧ k2 < b1) ∨ (k1 = -1 ∧ k2 < a2)
    (0 <= k1 < a1) || (k1 == a1 && k2 < b1) || (k1 == -1 && k2 < a2)
}

/// Partial completeness of block i (positions [lo, hi)): every covered move is emitted.
#[verifier::opaque]
pub open spec fn cov(
    tr: &Trans,
    st: &Pairs,
    g1: &Aut,
    g2: &Aut,
    ev: &Events,
    i: int,
    lo: int,
    hi: int,
    a1: int,
    b1: int,
    a2: int,
) -> bool {
    // Math: ∀ moves (e, c, d, k1, k2) from state i that are covered: found in [lo, hi)
    forall|e: int, c: int, d: int, k1: int, k2: int|
        #[trigger] move_by(g1, g2, ev, st.p1@[i] as int, st.p2@[i] as int, e, c, d, k1, k2)
            && covered(k1, k2, a1, b1, a2) ==> found_in(tr, st, lo, hi, e, c, d)
}

// Block i, positions [lo, hi): every move from state i is emitted.
pub open spec fn complete(
    tr: &Trans,
    st: &Pairs,
    g1: &Aut,
    g2: &Aut,
    ev: &Events,
    i: int,
    lo: int,
    hi: int,
) -> bool {
    // Math: ∀ moves (e, c, d, k1, k2) from state i: found in [lo, hi)
    forall|e: int, c: int, d: int, k1: int, k2: int|
        #[trigger] move_by(g1, g2, ev, st.p1@[i] as int, st.p2@[i] as int, e, c, d, k1, k2)
            ==> found_in(tr, st, lo, hi, e, c, d)
}

/// Block i, positions [lo, hi): sound and sorted.
#[verifier::opaque]
pub open spec fn blk_ok(
    tr: &Trans,
    st: &Pairs,
    g1: &Aut,
    g2: &Aut,
    ev: &Events,
    i: int,
    lo: int,
    hi: int,
) -> bool {
    // Math: ∀ k ∈ [lo, hi): sound_at(i, k); evt[lo .. hi-1] sorted
    &&& forall|k: int| lo <= k < hi ==> #[trigger] sound_at(tr, st, g1, g2, ev, i, k)
    &&& adj_le(tr.evt@, lo, hi)
}

// Block i is finished: sound, sorted and complete over [start[i], start[i+1]).
pub open spec fn blk_done(tr: &Trans, st: &Pairs, g1: &Aut, g2: &Aut, ev: &Events, i: int) -> bool {
    &&& blk_ok(tr, st, g1, g2, ev, i, tr.start@[i] as int, tr.start@[i + 1] as int)
    &&& complete(tr, st, g1, g2, ev, i, tr.start@[i] as int, tr.start@[i + 1] as int)
}

// Block i has no repeated event.
pub open spec fn strict_blk(tr: &Trans, i: int) -> bool {
    strict(tr.evt@, tr.start@[i] as int, tr.start@[i + 1] as int)
}

/// Blocks 0..h are finished; block h is being written from lo = start[h].
#[verifier::opaque]
pub open spec fn done_ok(tr: &Trans, st: &Pairs, g1: &Aut, g2: &Aut, ev: &Events, h: int) -> bool {
    // Math: |start| = h + 1, start[0] = 0, start sorted, start[h] ≤ |evt|, ∀ i < h: blk_done(i)
    &&& tr.start@.len() == h + 1
    &&& tr.start@[0] == 0
    &&& adj_le(tr.start@, 0, h + 1)
    &&& tr.start@[h] <= tr.evt@.len()
    &&& forall|i: int| 0 <= i < h ==> #[trigger] blk_done(tr, st, g1, g2, ev, i)
}

/// Blocks 0..h have no repeated event.
#[verifier::opaque]
pub open spec fn all_strict(tr: &Trans, h: int) -> bool {
    // Math: ∀ i < h: strict_blk(i)
    forall|i: int| 0 <= i < h ==> #[trigger] strict_blk(tr, i)
}

#[verifier::opaque]
// det is exact so far: at most one initial state, and no repeated event in blocks 0 .. h
// (block h: up to now).
pub open spec fn det_ok(tr: &Trans, h: int, n0: int) -> bool {
    // Math: det ↔ n0 ≤ 1 ∧ ∀ i < h: strict_blk(i) ∧ strict(evt, start[h], |evt|)
    tr.det == (n0 <= 1 && all_strict(tr, h) && strict(
        tr.evt@,
        tr.start@[h] as int,
        tr.evt@.len() as int,
    ))
}

/// Everything that holds while block h is being written.
#[verifier::opaque]
pub open spec fn cur_ok(
    tr: &Trans,
    st: &Pairs,
    seen: &Seen,
    g1: &Aut,
    g2: &Aut,
    ev: &Events,
    np: int,
    n0: int,
    h: int,
    prev: Option<usize>,
) -> bool {
    // Math: lo = start[h], t = |evt|: block h is [lo, t) so far
    let lo = tr.start@[h] as int;
    let t = tr.evt@.len() as int;
    // Math: h < n; pairs, table, transitions, finished blocks, block h so far, det: all ok
    &&& 0 <= h < st.p1@.len()
    &&& pairs_ok(st, g1, g2, n0)
    &&& seen_ok(seen, st, g2.n as int, np)
    &&& init_in(seen, g1, g2)
    &&& tr_ok(tr, st, ev)
    &&& done_ok(tr, st, g1, g2, ev, h)
    &&& blk_ok(tr, st, g1, g2, ev, h, lo, t)
    // Math: det exact for blocks 0 .. h-1
    &&& det_ok(tr, h, n0)
    // Math: prev = the last event of block h (None if empty)
    // Why: the determinism check compares each new event with it.
    &&& prev == (if t > lo {
        Some(tr.evt@[t - 1])
    } else {
        None::<usize>
    })
}

/// The inputs, with the derived monotonicity of start.
#[verifier::opaque]
pub open spec fn inputs_ok(g1: &Aut, g2: &Aut, ev: &Events, np: int) -> bool {
    // Math: both inputs ok, events ok, starts sorted (pair form), np = n1 · n2 ≤ 2^64 - 1
    &&& aut_ok(g1, ev.m1 as int)
    &&& aut_ok(g2, ev.map2@.len() as int)
    &&& ev_ok(ev, ev.map2@.len() as int)
    &&& all_le(g1.start@, 0, g1.n + 1)
    &&& all_le(g2.start@, 0, g2.n + 1)
    &&& np == g1.n * g2.n
    &&& np <= u64::MAX
}

// ---------------------------------------------------------------------------------------------
// Lemmas
// ---------------------------------------------------------------------------------------------

/// Keys are in range: 0 ≤ a · n2 + b < n1 · n2 for a < n1, b < n2.
proof fn lemma_key_range(a: int, b: int, n1: int, n2: int)
    requires
        0 <= a < n1,
        0 <= b < n2,
    ensures
        0 <= a * n2,
        0 <= key(a, b, n2) < n1 * n2,
{
    // Math: a ≥ 0 ∧ n2 ≥ 0 → a · n2 ≥ 0
    assert(0 <= a * n2) by (nonlinear_arith)
        requires
            0 <= a,
            0 <= n2,
    ;
    // Math: a + 1 ≤ n1 → (a + 1) · n2 ≤ n1 · n2; with b < n2 the key is < n1 · n2
    assert(a * n2 + n2 <= n1 * n2) by (nonlinear_arith)
        requires
            a + 1 <= n1,
            0 <= n2,
    ;
}

/// Keys are injective: a · n2 + b = c · n2 + d with b, d < n2 → a = c ∧ b = d.
proof fn lemma_key_inj(a: int, b: int, c: int, d: int, n2: int)
    requires
        0 <= b < n2,
        0 <= d < n2,
        key(a, b, n2) == key(c, d, n2),
    ensures
        a == c,
        b == d,
{
    // Math: a < c → a · n2 + n2 ≤ c · n2, so a · n2 + b < c · n2 + d: impossible
    if a < c {
        assert(a * n2 + n2 <= c * n2) by (nonlinear_arith)
            requires
                a + 1 <= c,
                0 <= n2,
        ;
    }
    // Math: c < a: symmetric
    if c < a {
        assert(c * n2 + n2 <= a * n2) by (nonlinear_arith)
            requires
                c + 1 <= a,
                0 <= n2,
        ;
    }
}

/// Neighbour order gives pair order: adj_le(s, lo, hi), lo ≤ k ≤ l < hi → s[k] ≤ s[l].
proof fn lemma_le_kl(s: Seq<usize>, lo: int, hi: int, k: int, l: int)
    requires
        adj_le(s, lo, hi),
        lo <= k <= l < hi,
    ensures
        s[k] <= s[l],
    decreases l - k,
{
    // Why: open the opaque bundles used here.
    reveal(adj_le);
    if k < l {
        // Math: induction on l - k: s[k] ≤ s[l-1] ≤ s[l]
        lemma_le_kl(s, lo, hi, k, l - 1);
    }
}

/// adj_le(s, lo, hi) → all_le(s, lo, hi).
pub proof fn lemma_all_le(s: Seq<usize>, lo: int, hi: int)
    requires
        adj_le(s, lo, hi),
    ensures
        all_le(s, lo, hi),
{
    assert forall|k: int, l: int| lo <= k <= l < hi implies #[trigger] s[k] <= #[trigger] s[l] by {
        // Math: s[k] ≤ s[l]
        lemma_le_kl(s, lo, hi, k, l);
    }
}

/// The table holds fewer than np keys.
proof fn lemma_used_bound(used: Set<int>, np: int)
    requires
        0 <= np,
        forall|x: int| #[trigger] used.contains(x) ==> 0 <= x < np,
    ensures
        used.len() <= np,
{
    // Math: |[0, np)| = np; used ⊆ [0, np), so |used| ≤ np
    vstd::set_lib::lemma_int_range(0, np);
    vstd::set_lib::lemma_len_subset(used, vstd::set_lib::set_int_range(0, np));
}

/// found_in survives growth: a move found in [lo, hi0) of tr0 is found in [lo, hi) of tr
/// (old positions and states unchanged).
proof fn lemma_found_ext(
    tr0: &Trans,
    st0: &Pairs,
    tr: &Trans,
    st: &Pairs,
    lo: int,
    hi0: int,
    hi: int,
    e: int,
    c: int,
    d: int,
)
    requires
        ext_trans(tr0, tr),
        ext_pairs(st0, st),
        dst_in(tr0, st0),
        0 <= lo,
        hi0 <= hi,
        hi0 <= tr0.evt@.len(),
        found_in(tr0, st0, lo, hi0, e, c, d),
    ensures
        found_in(tr, st, lo, hi, e, c, d),
{
    // Math: k: the position where it was found
    let k = choose|k: int|
        lo <= k < hi0 && #[trigger] tr0.evt@[k] as int == e && st0.p1@[tr0.dst@[k] as int] as int
            == c && st0.p2@[tr0.dst@[k] as int] as int == d;
    // Math: evt[k] and the labels of dst[k] are unchanged
    assert(tr.evt@[k] == tr0.evt@[k]);
    assert(st.p1@[tr0.dst@[k] as int] == st0.p1@[tr0.dst@[k] as int]);
}

/// A finished block stays finished when the lists grow (it lies before the end).
proof fn lemma_blk_done_ext(
    tr0: &Trans,
    st0: &Pairs,
    tr: &Trans,
    st: &Pairs,
    g1: &Aut,
    g2: &Aut,
    ev: &Events,
    i: int,
)
    requires
        ext_trans(tr0, tr),
        ext_pairs(st0, st),
        dst_in(tr0, st0),
        0 <= i < st0.p1@.len(),
        i + 1 < tr0.start@.len(),
        tr0.start@[i + 1] <= tr0.evt@.len(),
        blk_done(tr0, st0, g1, g2, ev, i),
    ensures
        blk_done(tr, st, g1, g2, ev, i),
{
    // Why: open the opaque bundles used here.
    reveal(adj_le);
    reveal(blk_ok);
    // Math: [lo, hi) = block i
    let lo = tr0.start@[i] as int;
    let hi = tr0.start@[i + 1] as int;
    // Math: block i's bounds and φ(i) are unchanged
    assert(tr.start@[i] == tr0.start@[i]);
    assert(tr.start@[i + 1] == tr0.start@[i + 1]);
    assert(st.p1@[i] == st0.p1@[i]);
    // Math: sound at each k ∈ [lo, hi) (old positions)
    assert forall|k: int| lo <= k < hi implies #[trigger] sound_at(tr, st, g1, g2, ev, i, k) by {
        assert(sound_at(tr0, st0, g1, g2, ev, i, k));
        assert(tr.evt@[k] == tr0.evt@[k]);
        assert(st.p1@[tr0.dst@[k] as int] == st0.p1@[tr0.dst@[k] as int]);
    }
    // Math: still sorted
    assert forall|k: int| lo <= k && k + 1 < hi implies #[trigger] tr.evt@[k] <= tr.evt@[k + 1] by {
        assert(tr0.evt@[k] <= tr0.evt@[k + 1]);
        assert(tr.evt@[k + 1] == tr0.evt@[k + 1]);
    }
    assert forall|e: int, c: int, d: int, k1: int, k2: int|
        #[trigger] move_by(
            g1,
            g2,
            ev,
            st.p1@[i] as int,
            st.p2@[i] as int,
            e,
            c,
            d,
            k1,
            k2,
        ) implies found_in(tr, st, lo, hi, e, c, d) by {
        assert(move_by(g1, g2, ev, st0.p1@[i] as int, st0.p2@[i] as int, e, c, d, k1, k2));
        // Math: complete: each move still found
        lemma_found_ext(tr0, st0, tr, st, lo, hi, hi, e, c, d);
    }
}

/// Finished blocks stay finished when the lists grow.
proof fn lemma_done_ext(
    tr0: &Trans,
    st0: &Pairs,
    tr: &Trans,
    st: &Pairs,
    g1: &Aut,
    g2: &Aut,
    ev: &Events,
    h: int,
)
    requires
        ext_trans(tr0, tr),
        ext_pairs(st0, st),
        dst_in(tr0, st0),
        0 <= h < st0.p1@.len(),
        tr.start@ == tr0.start@,
        done_ok(tr0, st0, g1, g2, ev, h),
    ensures
        done_ok(tr, st, g1, g2, ev, h),
        forall|i: int| 0 <= i < h ==> #[trigger] strict_blk(tr, i) == strict_blk(tr0, i),
{
    // Why: open done_ok.
    reveal(done_ok);
    // Math: start sorted (pair form): start[i+1] ≤ start[h] ≤ |evt0|
    // Math: start sorted (pair form)
    lemma_all_le(tr0.start@, 0, h + 1);
    // Math: each finished block stays finished
    // Math: blocks i < h stay finished
    assert forall|i: int| 0 <= i < h implies #[trigger] blk_done(tr, st, g1, g2, ev, i) by {
        assert(tr0.start@[i + 1] <= tr0.start@[h]);
        lemma_blk_done_ext(tr0, st0, tr, st, g1, g2, ev, i);
    }
    // Math: and keeps its strictness (same events)
    // Math: blocks i < h: same bounds, same strictness
    assert forall|i: int| 0 <= i < h implies #[trigger] strict_blk(tr, i) == strict_blk(tr0, i) by {
        assert(tr0.start@[i + 1] <= tr0.start@[h]);
        // Math: [lo, hi) = block i
        let lo = tr0.start@[i] as int;
        let hi = tr0.start@[i + 1] as int;
        assert forall|k: int| lo <= k && k + 1 < hi implies #[trigger] tr.evt@[k] == tr0.evt@[k]
            && tr.evt@[k + 1] == tr0.evt@[k + 1] by {}
    }
}

/// Partial completeness of the current block survives growth (hi grows with the list).
proof fn lemma_cov_ext(
    tr0: &Trans,
    st0: &Pairs,
    tr: &Trans,
    st: &Pairs,
    g1: &Aut,
    g2: &Aut,
    ev: &Events,
    i: int,
    lo: int,
    a1: int,
    b1: int,
    a2: int,
)
    requires
        ext_trans(tr0, tr),
        ext_pairs(st0, st),
        dst_in(tr0, st0),
        0 <= i < st0.p1@.len(),
        0 <= lo,
        cov(tr0, st0, g1, g2, ev, i, lo, tr0.evt@.len() as int, a1, b1, a2),
    ensures
        cov(tr, st, g1, g2, ev, i, lo, tr.evt@.len() as int, a1, b1, a2),
{
    // Why: open cov.
    reveal(cov);
    assert(st.p1@[i] == st0.p1@[i]);
    assert forall|e: int, c: int, d: int, k1: int, k2: int|
        #[trigger] move_by(
            g1,
            g2,
            ev,
            st.p1@[i] as int,
            st.p2@[i] as int,
            e,
            c,
            d,
            k1,
            k2,
        ) && covered(k1, k2, a1, b1, a2) implies found_in(
        tr,
        st,
        lo,
        tr.evt@.len() as int,
        e,
        c,
        d,
    ) by {
        assert(move_by(g1, g2, ev, st0.p1@[i] as int, st0.p2@[i] as int, e, c, d, k1, k2));
        // Math: each covered move still found
        lemma_found_ext(tr0, st0, tr, st, lo, tr0.evt@.len() as int, tr.evt@.len() as int, e, c, d);
    }
}

// ---------------------------------------------------------------------------------------------
// Code
// ---------------------------------------------------------------------------------------------

/// The output state of the pair (a, b): its number if the table has it, else a new state
/// (appended, with its flags). `initial`: called while adding the initial pairs.
fn find_or_add(
    st: &mut Pairs,
    seen: &mut Seen,
    g1: &Aut,
    g2: &Aut,
    a: usize,
    b: usize,
    initial: bool,
    Ghost(np): Ghost<int>,
    Ghost(n0): Ghost<int>,
) -> (r: usize)
    requires
        // Math: |init1| = |marked1| = n1, |init2| = |marked2| = n2, a < n1, b < n2
        g1.init@.len() == g1.n,
        g1.marked@.len() == g1.n,
        g2.init@.len() == g2.n,
        g2.marked@.len() == g2.n,
        // Math: a < n1, b < n2
        a < g1.n,
        // Math: b < n2; hi2 = start2[b+1] ≤ T2
        b < g2.n,
        // Math: np = n1 · n2 ≤ 2^64 - 1 (keys fit in u64)
        // Math: np = n1 · n2 ≤ 2^64 - 1; facts about the inputs, restated
        np == g1.n * g2.n,
        np <= u64::MAX,
        // Math: the states and the table are consistent before the call
        pairs_ok(old(st), g1, g2, n0),
        seen_ok(old(seen), old(st), g2.n as int, np),
        // Math: initial → n0 = n and (a, b) is an initial pair (the first n0 states are the initial ones)
        initial ==> n0 == old(st).p1@.len() && g1.init@[a as int] && g2.init@[b as int],
        // Math: ¬initial → all initial pairs are in the table already (so a new state is not initial)
        !initial ==> init_in(old(seen), g1, g2),
    ensures
        // Math: r < n', φ(r) = (a, b)
        r < final(st).p1@.len(),
        final(st).p1@[r as int] == a,
        final(st).p2@[r as int] == b,
        // Math: old states unchanged; at most one new state
        ext_pairs(old(st), final(st)),
        // Math: at most one new state; old keys stay
        final(st).p1@.len() <= old(st).p1@.len() + 1,
        // Math: pairs_ok after (with n0 = n' while adding initial pairs)
        pairs_ok(
            final(st),
            g1,
            g2,
            if initial {
                final(st).p1@.len() as int
            } else {
                n0
            },
        ),
        // Math: the table matches; key(a, b) is in it; old keys stay; same kind of table
        seen_ok(final(seen), final(st), g2.n as int, np),
        in_tab(final(seen), key(a as int, b as int, g2.n as int)),
        forall|x: int| 0 <= x < np && #[trigger] in_tab(old(seen), x) ==> in_tab(final(seen), x),
        final(seen).dense == old(seen).dense,
{
    proof {
        // Why: open the bundles this function changes.
        reveal(pairs_ok);
        reveal(seen_ok);
        // Math: init_part(n1, 0) is init_in
        reveal(init_in);
        // Math: 0 ≤ key(a, b) < n1 · n2
        lemma_key_range(a as int, b as int, g1.n as int, g2.n as int);
    }
    // Math: kk = key(a, b) (ghost)
    let ghost kk = key(a as int, b as int, g2.n as int);
    // Why: ghost copies before the changes.
    let ghost seen0 = *seen;
    let ghost st0 = *st;
    // Math: key_u = a · n2 + b (no overflow: < n1 · n2 ≤ 2^64 - 1)
    let key_u: u64 = (a as u64) * (g2.n as u64) + (b as u64);
    // Math: key_u = kk
    assert(key_u as int == kk);
    // Math: found = the state stored for key_u, if any
    let found: Option<usize> = if seen.dense {
        // Math: j = tab[key_u]
        let j = seen.tab[key_u as usize];
        // Math: ABSENT → none
        if j == ABSENT {
            None
        } else {
            Some(j)
        }
    } else {
        // Math: map[key_u], if present
        match seen.map.get(&key_u) {
            Some(j) => Some(*j),
            None => None,
        }
    };
    // Math: found?
    match found {
        Some(j) => {
            proof {
                // Math: kk ∈ table
                assert(in_tab(seen, kk));
                // Math: key(p1[j], p2[j]) = kk = key(a, b) → φ(j) = (a, b)
                lemma_key_inj(
                    st.p1@[j as int] as int,
                    st.p2@[j as int] as int,
                    a as int,
                    b as int,
                    g2.n as int,
                );
            }
            j
        },
        None => {
            proof {
                // Math: kk ∉ table, kk ∉ used
                assert(!in_tab(seen, kk));
                assert(!seen.used@.contains(kk));
                // Math: |used ∪ {kk}| ≤ np (keys are below np)
                // Why: |p1| + 1 ≤ np, so the new number fits.
                lemma_used_bound(seen.used@.insert(kk), np);
                // Math: not adding initial pairs: (a, b) initial would be in the table (init_in), so it is not initial
                if !initial && g1.init@[a as int] && g2.init@[b as int] {
                    assert(in_tab(seen, kk));
                }
            }
            // Math: j = n, the new state's number
            let j = st.p1.len();
            // Math: append (a, b), init = initial, marked = marked1[a] ∧ marked2[b]
            st.p1.push(a);
            st.p2.push(b);
            st.init.push(initial);
            let mk = g1.marked[a] && g2.marked[b];
            st.marked.push(mk);
            // Math: table[key_u] := j; used := used ∪ {kk}
            if seen.dense {
                seen.tab.set(key_u as usize, j);
            } else {
                seen.map.insert(key_u, j);
            }
            seen.used = Ghost(seen.used@.insert(kk));
            proof {
                // Math: in_tab(x) ↔ x ∈ used, for all keys (kk is new; others unchanged)
                assert forall|x: int| 0 <= x < np implies (#[trigger] in_tab(seen, x)
                    == seen.used@.contains(x)) by {
                    if x != kk {
                        assert(in_tab(seen, x) == in_tab(&seen0, x));
                    }
                }
                // Math: the stored state of each key is the pair with that key (kk ↦ j = (a, b))
                assert forall|x: int| 0 <= x < np && #[trigger] in_tab(seen, x) implies {
                    &&& 0 <= tab_at(seen, x) < st.p1@.len()
                    &&& key(st.p1@[tab_at(seen, x)] as int, st.p2@[tab_at(seen, x)] as int, g2.n as int)
                        == x
                } by {
                    if x != kk {
                        assert(in_tab(&seen0, x));
                        assert(tab_at(seen, x) == tab_at(&seen0, x));
                    }
                }
                // Math: old keys stay in the table
                assert forall|x: int| 0 <= x < np && #[trigger] in_tab(&seen0, x) implies in_tab(seen, x) by {
                    if x != kk {
                        assert(in_tab(seen, x) == in_tab(&seen0, x));
                    }
                }
            }
            j
        },
    }
}

/// Append (e, t) to the block being written; a repeat of the previous event clears det.
fn emit(
    tr: &mut Trans,
    prev: &mut Option<usize>,
    e: usize,
    t: usize,
    Ghost(k1): Ghost<int>,
    Ghost(k2): Ghost<int>,
)
    ensures
        // Math: evt · [e], dst · [t], w1 · [k1], w2 · [k2]; start unchanged
        final(tr).evt@ == old(tr).evt@.push(e),
        final(tr).dst@ == old(tr).dst@.push(t),
        final(tr).w1@ == old(tr).w1@.push(k1),
        final(tr).w2@ == old(tr).w2@.push(k2),
        final(tr).start@ == old(tr).start@,
        // Math: det' = det ∧ prev ≠ e (a repeat of the previous event: not deterministic)
        final(tr).det == (old(tr).det && *old(prev) != Some(e)),
        // Math: prev' = e
        *final(prev) == Some(e),
{
    // Math: prev = e → det := false
    match *prev {
        Some(p) => {
            if p == e {
                tr.det = false;
            }
        },
        None => {},
    }
    // Math: append e, t, and the ghost witnesses k1, k2; prev := e
    tr.evt.push(e);
    tr.dst.push(t);
    tr.w1 = Ghost(tr.w1@.push(k1));
    tr.w2 = Ghost(tr.w2@.push(k2));
    *prev = Some(e);
}

/// First position r in [lo, hi) with evt[r] >= e (evt sorted on [lo, hi)).
fn lbound(evt: &Vec<usize>, lo: usize, hi: usize, e: usize) -> (r: usize)
    requires
        // Math: [lo, hi) ⊆ evt and sorted
        lo <= hi <= evt@.len(),
        all_le(evt@, lo as int, hi as int),
    ensures
        // Math: lo ≤ r ≤ hi; before r: < e; from r: ≥ e
        lo <= r <= hi,
        forall|k: int| lo <= k < r ==> #[trigger] evt@[k] < e,
        forall|k: int| r <= k < hi ==> #[trigger] evt@[k] >= e,
{
    // Math: [l, u) undecided (binary search, as lower_bound in basic_ops.rs)
    let mut l = lo;
    let mut u = hi;
    while l < u
        invariant
            // Math: lo ≤ l ≤ u ≤ hi; left of l: < e; from u: ≥ e
            lo <= l <= u <= hi,
            hi <= evt@.len(),
            all_le(evt@, lo as int, hi as int),
            forall|k: int| lo <= k < l ==> #[trigger] evt@[k] < e,
            forall|k: int| u <= k < hi ==> #[trigger] evt@[k] >= e,
        // Math: u - l decreases
        decreases u - l,
    {
        // Math: mid = l + ⌊(u - l)/2⌋ (no overflow)
        let mid = l + (u - l) / 2;
        // Math: evt[mid] < e → l := mid + 1 (sorted: all up to mid are < e); else u := mid
        if evt[mid] < e {
            l = mid + 1;
        } else {
            u = mid;
        }
    }
    l
}

/// One move of state h: find or add its target (c, d), then emit (e, target).
/// Contract: from the state of block h being written (cur_ok), one move
/// (e, c, d) with witnesses (k1, k2), and e not smaller than the block's last event.
fn step(
    tr: &mut Trans,
    st: &mut Pairs,
    seen: &mut Seen,
    prev: &mut Option<usize>,
    g1: &Aut,
    g2: &Aut,
    ev: &Events,
    e: usize,
    c: usize,
    d: usize,
    Ghost(k1): Ghost<int>,
    Ghost(k2): Ghost<int>,
    Ghost(np): Ghost<int>,
    Ghost(n0): Ghost<int>,
    Ghost(h): Ghost<int>,
)
    requires
        // Math: the inputs are ok
        // Math: the inputs are ok (restated)
        inputs_ok(g1, g2, ev, np),
        // Math: cur_ok before (block h being written)
        cur_ok(old(tr), old(st), old(seen), g1, g2, ev, np, n0, h, *old(prev)),
        move_by(
            g1,
            g2,
            ev,
            old(st).p1@[h] as int,
            old(st).p2@[h] as int,
            e as int,
            c as int,
            d as int,
            k1,
            k2,
        ),
        // Math: block h non-empty → its last event ≤ e
        // Why: the block stays sorted.
        old(tr).evt@.len() > old(tr).start@[h] ==> old(tr).evt@[old(tr).evt@.len() - 1] <= e,
    ensures
        // Math: cur_ok after; the lists only grew; one new position, carrying e, found_in it
        cur_ok(final(tr), final(st), final(seen), g1, g2, ev, np, n0, h, *final(prev)),
        ext_trans(old(tr), final(tr)),
        ext_pairs(old(st), final(st)),
        final(tr).start@ == old(tr).start@,
        final(tr).evt@.len() == old(tr).evt@.len() + 1,
        final(tr).evt@[old(tr).evt@.len() as int] == e,
        found_in(
            final(tr),
            final(st),
            old(tr).evt@.len() as int,
            final(tr).evt@.len() as int,
            e as int,
            c as int,
            d as int,
        ),
        final(st).p1@.len() <= old(st).p1@.len() + 1,
        forall|x: int| 0 <= x < np && #[trigger] in_tab(old(seen), x) ==> in_tab(final(seen), x),
{
    proof {
        // Why: open the bundle (it is opaque).
        reveal(cur_ok);
    }
    // Why: ghost copies before the changes; t0 = |evt|, lo = start[h].
    let ghost tr0 = *tr;
    let ghost st0 = *st;
    let ghost seen0 = *seen;
    let ghost prev0 = *prev;
    let ghost t0 = tr.evt@.len() as int;
    let ghost lo = tr.start@[h] as int;
    proof {
        // Math: the basic input facts (lengths, ranges)
        // Math: basic input facts
        lemma_inputs_basic(g1, g2, ev, np);
        reveal(pairs_ok);
        reveal(tr_ok);
        reveal(done_ok);
        // Math: φ(h) ∈ [0, n1) × [0, n2)
        assert(st.p1@[h] < g1.n);
        assert(st.p2@[h] < g2.n);
        // Math: c < n1, d < n2, e < m, mode[e] ≠ NONE
        lemma_move_bounds(g1, g2, ev, np, st.p1@[h] as int, st.p2@[h] as int, e as int, c as int, d as int, k1, k2);
    }
    // Math: t = the state of (c, d) (found or new)
    let t = find_or_add(st, seen, g1, g2, c, d, false, Ghost(np), Ghost(n0));
    // Math: append h --e--> t
    emit(tr, prev, e, t, Ghost(k1), Ghost(k2));
    proof {
        // Math: init_in still holds (keys only grow)
        lemma_init_in_mono(&seen0, seen, g1, g2, np);
        // Math: tr_ok after
        lemma_step_tr(&tr0, &st0, tr, st, ev, e, t);
        // Math: the finished blocks stay finished
        lemma_done_ext(&tr0, &st0, tr, st, g1, g2, ev, h);
        // Math: the old lists have equal lengths
        assert(tr0.dst@.len() == tr0.evt@.len() && tr0.w1@.len() == tr0.evt@.len() && tr0.w2@.len() == tr0.evt@.len()) by { reveal(tr_ok); }
        // Math: block h so far stays sound and sorted
        lemma_step_blk(&tr0, &st0, tr, st, g1, g2, ev, h, lo, e, t, c as int, d as int, k1, k2);
        // Math: det stays exact
        lemma_step_det(&tr0, tr, h, n0, e, prev0);
        reveal(cur_ok);
        // Math: the move is at position t0
        assert(found_in(tr, st, t0, t0 + 1, e as int, c as int, d as int)) by {
            assert(tr.evt@[t0] as int == e as int);
        }
    }
}

/// The ends of a move are states, its event is a real one (mode not NONE).
/// A move from (a, b) ends at a pair of states (c, d), on an event with a mode (not NONE).
proof fn lemma_move_bounds(g1: &Aut, g2: &Aut, ev: &Events, np: int, a: int, b: int, e: int, c: int, d: int, k1: int, k2: int)
    requires
        // Math: the inputs are ok (restated)
        inputs_ok(g1, g2, ev, np),
        0 <= a < g1.n,
        0 <= b < g2.n,
        move_by(g1, g2, ev, a, b, e, c, d, k1, k2),
    ensures
        0 <= c < g1.n,
        0 <= d < g2.n,
        0 <= e < ev.mode@.len(),
        ev.mode@[e] != NONE,
{
    reveal(inputs_ok);
    // Math: G1 moves: k1 ∈ block1(a) ⊆ [0, T1), so c = dst1[k1] < n1
    if k1 != -1 {
        // Math: start1[a+1] ≤ start1[n1] = T1
        assert(g1.start@[a + 1] <= g1.start@[g1.n as int]);
        assert(g1.dst@[k1] < g1.n);
    }
    // Math: G2 moves: k2 ∈ block2(b), so d = dst2[k2] < n2
    if k2 != -1 && ev.mode@[e] != LEFT {
        // Math: start2[b+1] ≤ start2[n2] = T2
        assert(g2.start@[b + 1] <= g2.start@[g2.n as int]);
        assert(g2.dst@[k2] < g2.n);
    }
}

/// init_in survives when the table only grows.
proof fn lemma_init_in_mono(seen0: &Seen, seen: &Seen, g1: &Aut, g2: &Aut, np: int)
    requires
        init_in(seen0, g1, g2),
        // Math: np = n1 · n2 ≤ 2^64 - 1; facts about the inputs, restated
        np == g1.n * g2.n,
        forall|x: int| 0 <= x < np && #[trigger] in_tab(seen0, x) ==> in_tab(seen, x),
    ensures
        init_in(seen, g1, g2),
{
    reveal(init_in);
    assert forall|a: int, b: int|
        0 <= a < g1.n && 0 <= b < g2.n && #[trigger] g1.init@[a] && #[trigger] g2.init@[b]
        implies in_tab(seen, key(a, b, g2.n as int)) by {
        // Math: key(a, b) < np
        // Math: init_complete: key(a, b) is in the table (init_in), and its state i has φ(i) = (a, b)
        lemma_key_range(a, b, g1.n as int, g2.n as int);
        // Math: it was in the old table
        assert(in_tab(seen0, key(a, b, g2.n as int)));
    }
}

/// tr_ok survives appending (e, t), t a state, mode[e] ≠ NONE.
proof fn lemma_step_tr(tr0: &Trans, st0: &Pairs, tr: &Trans, st: &Pairs, ev: &Events, e: usize, t: usize)
    requires
        tr_ok(tr0, st0, ev),
        tr.evt@ == tr0.evt@.push(e),
        tr.dst@ == tr0.dst@.push(t),
        tr.w1@.len() == tr0.w1@.len() + 1,
        tr.w2@.len() == tr0.w2@.len() + 1,
        t < st.p1@.len(),
        st0.p1@.len() <= st.p1@.len(),
        e < ev.mode@.len(),
        ev.mode@[e as int] != NONE,
    ensures
        tr_ok(tr, st, ev),
{
    reveal(tr_ok);
    // Math: n = the old length; old positions keep their facts, position n is the new one
    let n = tr0.evt@.len() as int;
    assert forall|k: int| 0 <= k < tr.evt@.len() implies #[trigger] tr.dst@[k] < st.p1@.len() by {
        if k < n {
            assert(tr0.dst@[k] < st0.p1@.len());
        }
    }
    assert forall|k: int| 0 <= k < tr.evt@.len() implies {
        &&& #[trigger] tr.evt@[k] < ev.mode@.len()
        &&& ev.mode@[tr.evt@[k] as int] != NONE
    } by {
        if k < n {
            assert(tr0.evt@[k] == tr.evt@[k]);
        }
    }
}

/// Block h so far stays sound and sorted after appending the move (e, t) with witnesses
/// (k1, k2), when e is not below the block's last event.
proof fn lemma_step_blk(
    tr0: &Trans,
    st0: &Pairs,
    tr: &Trans,
    st: &Pairs,
    g1: &Aut,
    g2: &Aut,
    ev: &Events,
    h: int,
    lo: int,
    e: usize,
    t: usize,
    c: int,
    d: int,
    k1: int,
    k2: int,
)
    requires
        blk_ok(tr0, st0, g1, g2, ev, h, lo, tr0.evt@.len() as int),
        0 <= lo <= tr0.evt@.len(),
        tr0.dst@.len() == tr0.evt@.len(),
        tr0.w1@.len() == tr0.evt@.len(),
        tr0.w2@.len() == tr0.evt@.len(),
        0 <= h < st0.p1@.len(),
        dst_in(tr0, st0),
        ext_pairs(st0, st),
        tr.evt@ == tr0.evt@.push(e),
        tr.dst@ == tr0.dst@.push(t),
        tr.w1@ == tr0.w1@.push(k1),
        tr.w2@ == tr0.w2@.push(k2),
        t < st.p1@.len(),
        st.p1@[t as int] as int == c,
        st.p2@[t as int] as int == d,
        move_by(g1, g2, ev, st0.p1@[h] as int, st0.p2@[h] as int, e as int, c, d, k1, k2),
        tr0.evt@.len() > lo ==> tr0.evt@[tr0.evt@.len() - 1] <= e,
    ensures
        blk_ok(tr, st, g1, g2, ev, h, lo, tr.evt@.len() as int),
{
    // Why: open the opaque bundles used here.
    reveal(adj_le);
    reveal(blk_ok);
    // Math: t0 = the old length
    let t0 = tr0.evt@.len() as int;
    // Math: φ(h) unchanged
    assert(st.p1@[h] == st0.p1@[h]);
    // Math: sound at every k ∈ [lo, t0]: old positions unchanged; t0 is the new move
    assert forall|k: int| lo <= k < t0 + 1 implies #[trigger] sound_at(tr, st, g1, g2, ev, h, k) by {
        if k < t0 {
            assert(sound_at(tr0, st0, g1, g2, ev, h, k));
            assert(tr0.dst@[k] < st0.p1@.len());
            assert(tr.evt@[k] == tr0.evt@[k]);
            assert(tr.dst@[k] == tr0.dst@[k]);
            assert(tr.w1@[k] == tr0.w1@[k]);
            assert(tr.w2@[k] == tr0.w2@[k]);
            assert(st.p1@[tr0.dst@[k] as int] == st0.p1@[tr0.dst@[k] as int]);
        } else {
            assert(tr.evt@[k] == e);
            assert(tr.dst@[k] == t);
            assert(tr.w1@[k] == k1);
            assert(tr.w2@[k] == k2);
        }
    }
    // Math: sorted: old pairs unchanged; (t0-1, t0) by last ≤ e
    assert forall|k: int| lo <= k && k + 1 < t0 + 1 implies #[trigger] tr.evt@[k] <= tr.evt@[k + 1] by {
        if k + 1 < t0 {
            assert(tr0.evt@[k] <= tr0.evt@[k + 1]);
        }
    }
}

/// all_strict is the same for tr and tr0 when each finished block's strictness is.
/// (Two directions: the solver does not prove an equality of two foralls in one step.)
proof fn lemma_all_strict_eq(tr0: &Trans, tr: &Trans, h: int)
    requires
        forall|i: int| 0 <= i < h ==> #[trigger] strict_blk(tr, i) == strict_blk(tr0, i),
    ensures
        all_strict(tr, h) == all_strict(tr0, h),
{
    reveal(all_strict);
    if all_strict(tr0, h) {
        assert forall|i: int| 0 <= i < h implies #[trigger] strict_blk(tr, i) by {
            assert(strict_blk(tr0, i));
        }
    }
    if all_strict(tr, h) {
        assert forall|i: int| 0 <= i < h implies #[trigger] strict_blk(tr0, i) by {
            assert(strict_blk(tr, i));
        }
    }
}

/// strict(s0 · [e], lo, |s0|+1) ↔ strict(s0, lo, |s0|) ∧ (last of s0 < e).
proof fn lemma_strict_push(s0: Seq<usize>, s: Seq<usize>, lo: int, e: usize)
    requires
        0 <= lo <= s0.len(),
        s == s0.push(e),
    ensures
        strict(s, lo, s0.len() + 1 as int) == (strict(s0, lo, s0.len() as int) && (s0.len() > lo ==> s0[s0.len() - 1] < e)),
{
    let t0 = s0.len() as int;
    if strict(s0, lo, t0) && (t0 > lo ==> s0[t0 - 1] < e) {
        assert forall|k: int| lo <= k && k + 1 < t0 + 1 implies #[trigger] s[k] < s[k + 1] by {
            if k + 1 < t0 {
                assert(s0[k] < s0[k + 1]);
            }
        }
    }
    if strict(s, lo, t0 + 1) {
        assert forall|k: int| lo <= k && k + 1 < t0 implies #[trigger] s0[k] < s0[k + 1] by {
            assert(s[k] < s[k + 1]);
        }
        if t0 > lo {
            assert(s[t0 - 1] < s[t0]);
        }
    }
}

/// det stays exact after appending e: it turns false exactly when e repeats the previous event
/// (the block is sorted, so a repeat is always next to it).
proof fn lemma_step_det(tr0: &Trans, tr: &Trans, h: int, n0: int, e: usize, prev0: Option<usize>)
    requires
        det_ok(tr0, h, n0),
        0 <= h,
        tr.start@ == tr0.start@,
        tr0.start@.len() == h + 1,
        tr0.start@[h] <= tr0.evt@.len(),
        forall|i: int| 0 <= i < h ==> #[trigger] strict_blk(tr, i) == strict_blk(tr0, i),
        tr.evt@ == tr0.evt@.push(e),
        tr.det == (tr0.det && prev0 != Some(e)),
        prev0 == (if tr0.evt@.len() > tr0.start@[h] {
            Some(tr0.evt@[tr0.evt@.len() - 1])
        } else {
            None::<usize>
        }),
        tr0.evt@.len() > tr0.start@[h] ==> tr0.evt@[tr0.evt@.len() - 1] <= e,
    ensures
        det_ok(tr, h, n0),
{
    reveal(det_ok);
    // Math: finished blocks: same strictness
    lemma_all_strict_eq(tr0, tr, h);
    // Math: block h: strict after ↔ strict before ∧ prev < e
    lemma_strict_push(tr0.evt@, tr.evt@, tr0.start@[h] as int, e);
}

// ---------------------------------------------------------------------------------------------
// Coverage steps (each one small)
// ---------------------------------------------------------------------------------------------

/// found_in on [lo, hi) gives found_in on a wider range [lo2, hi2).
proof fn lemma_found_widen(tr: &Trans, st: &Pairs, lo: int, hi: int, lo2: int, hi2: int, e: int, c: int, d: int)
    requires
        lo2 <= lo,
        hi <= hi2,
        found_in(tr, st, lo, hi, e, c, d),
    ensures
        found_in(tr, st, lo2, hi2, e, c, d),
{
    // Math: k: the position where it was found
    let k = choose|k: int|
        lo <= k < hi && #[trigger] tr.evt@[k] as int == e && st.p1@[tr.dst@[k] as int] as int == c
            && st.p2@[tr.dst@[k] as int] as int == d;
    assert(tr.evt@[k] as int == e);
}

/// Extensions compose: tr0 ⊑ tr1 ⊑ tr gives tr0 ⊑ tr (and the same for the pairs).
proof fn lemma_ext_trans(tr0: &Trans, st0: &Pairs, tr1: &Trans, st1: &Pairs, tr: &Trans, st: &Pairs)
    requires
        ext_trans(tr0, tr1),
        ext_pairs(st0, st1),
        ext_trans(tr1, tr),
        ext_pairs(st1, st),
    ensures
        ext_trans(tr0, tr),
        ext_pairs(st0, st),
{
    assert forall|k: int| 0 <= k < tr0.evt@.len() implies #[trigger] tr.evt@[k] == tr0.evt@[k]
        && tr.dst@[k] == tr0.dst@[k] && tr.w1@[k] == tr0.w1@[k] && tr.w2@[k] == tr0.w2@[k] by {
        assert(tr1.evt@[k] == tr0.evt@[k]);
    }
    assert forall|x: int| 0 <= x < tr0.start@.len() implies #[trigger] tr.start@[x] == tr0.start@[x] by {
        assert(tr1.start@[x] == tr0.start@[x]);
    }
    assert forall|i: int| 0 <= i < st0.p1@.len() implies #[trigger] st.p1@[i] == st0.p1@[i]
        && st.p2@[i] == st0.p2@[i] by {
        assert(st1.p1@[i] == st0.p1@[i]);
    }
}

/// Before G1's block: nothing is claimed yet.
/// cov holds at the start of block h: nothing is covered yet (G1 positions before the block's
/// start do not belong to it).
proof fn lemma_cov_start(tr: &Trans, st: &Pairs, g1: &Aut, g2: &Aut, ev: &Events, h: int, lo: int)
    requires
        0 <= h < st.p1@.len(),
        st.p1@[h] < g1.n,
    ensures
        cov(tr, st, g1, g2, ev, h, lo, tr.evt@.len() as int, g1.start@[st.p1@[h] as int] as int, -1, 0),
{
    reveal(cov);
}

/// G1 transition k1 has a LEFT event, and its move was emitted.
/// After emitting the LEFT move of k1: cov covers k1 + 1.
proof fn lemma_cov_left(tr: &Trans, st: &Pairs, g1: &Aut, g2: &Aut, ev: &Events, h: int, lo: int, k1: int)
    requires
        0 <= h < st.p1@.len(),
        0 <= k1 < g1.evt@.len(),
        ev.mode@[g1.evt@[k1] as int] == LEFT,
        cov(tr, st, g1, g2, ev, h, lo, tr.evt@.len() as int, k1, -1, 0),
        found_in(tr, st, lo, tr.evt@.len() as int, g1.evt@[k1] as int, g1.dst@[k1] as int, st.p2@[h] as int),
    ensures
        cov(tr, st, g1, g2, ev, h, lo, tr.evt@.len() as int, k1 + 1, -1, 0),
{
    reveal(cov);
}

/// G1 transition k1 has an event with no move (NONE).
/// k1's event is neither LEFT nor BOTH: no move uses k1; cov covers k1 + 1.
proof fn lemma_cov_none(tr: &Trans, st: &Pairs, g1: &Aut, g2: &Aut, ev: &Events, h: int, lo: int, k1: int)
    requires
        0 <= k1 < g1.evt@.len(),
        ev.mode@[g1.evt@[k1] as int] != LEFT,
        ev.mode@[g1.evt@[k1] as int] != BOTH,
        cov(tr, st, g1, g2, ev, h, lo, tr.evt@.len() as int, k1, -1, 0),
    ensures
        cov(tr, st, g1, g2, ev, h, lo, tr.evt@.len() as int, k1 + 1, -1, 0),
{
    reveal(cov);
}

/// BOTH at k1: the G2 transitions before r have smaller events, so none is a move.
/// BOTH at k1: G2 positions before r carry smaller events than inv2[e], so no move; cov covers (k1, r).
proof fn lemma_cov_both_start(
    tr: &Trans, st: &Pairs, g1: &Aut, g2: &Aut, ev: &Events, h: int, lo: int, k1: int, r: int,
)
    requires
        0 <= h < st.p1@.len(),
        0 <= k1 < g1.evt@.len(),
        ev.mode@[g1.evt@[k1] as int] == BOTH,
        forall|k: int| 0 <= k < r && in_blk(g2, st.p2@[h] as int, k) ==> #[trigger] g2.evt@[k] < ev.inv2@[g1.evt@[k1] as int],
        cov(tr, st, g1, g2, ev, h, lo, tr.evt@.len() as int, k1, -1, 0),
    ensures
        cov(tr, st, g1, g2, ev, h, lo, tr.evt@.len() as int, k1, r, 0),
{
    reveal(cov);
}

/// BOTH at k1: the move with G2 transition k2 was emitted.
/// After emitting the BOTH move (k1, k2): cov covers (k1, k2 + 1).
proof fn lemma_cov_both_step(
    tr: &Trans, st: &Pairs, g1: &Aut, g2: &Aut, ev: &Events, h: int, lo: int, k1: int, k2: int,
)
    requires
        0 <= h < st.p1@.len(),
        0 <= k1 < g1.evt@.len(),
        0 <= k2 < g2.evt@.len(),
        ev.mode@[g1.evt@[k1] as int] == BOTH,
        cov(tr, st, g1, g2, ev, h, lo, tr.evt@.len() as int, k1, k2, 0),
        found_in(tr, st, lo, tr.evt@.len() as int, g1.evt@[k1] as int, g1.dst@[k1] as int, g2.dst@[k2] as int),
    ensures
        cov(tr, st, g1, g2, ev, h, lo, tr.evt@.len() as int, k1, k2 + 1, 0),
{
    reveal(cov);
}

/// BOTH at k1: from k2 on, G2's events are larger (or the block ended): k1 is done.
/// BOTH at k1: from k2 on, G2 events are larger than inv2[e]; cov covers k1 + 1.
proof fn lemma_cov_both_end(
    tr: &Trans, st: &Pairs, g1: &Aut, g2: &Aut, ev: &Events, h: int, lo: int, k1: int, k2: int,
)
    requires
        0 <= h < st.p1@.len(),
        0 <= k1 < g1.evt@.len(),
        ev.mode@[g1.evt@[k1] as int] == BOTH,
        forall|k: int| k2 <= k && in_blk(g2, st.p2@[h] as int, k) ==> #[trigger] g2.evt@[k] > ev.inv2@[g1.evt@[k1] as int],
        cov(tr, st, g1, g2, ev, h, lo, tr.evt@.len() as int, k1, k2, 0),
    ensures
        cov(tr, st, g1, g2, ev, h, lo, tr.evt@.len() as int, k1 + 1, -1, 0),
{
    reveal(cov);
}

/// After G1's block: start G2's block (RIGHT moves) with nothing claimed.
/// Start of the RIGHT phase: G2 positions before b's block start do not belong to it.
proof fn lemma_cov_mid(tr: &Trans, st: &Pairs, g1: &Aut, g2: &Aut, ev: &Events, h: int, lo: int, a1: int)
    requires
        0 <= h < st.p1@.len(),
        st.p2@[h] < g2.n,
        cov(tr, st, g1, g2, ev, h, lo, tr.evt@.len() as int, a1, -1, 0),
    ensures
        cov(tr, st, g1, g2, ev, h, lo, tr.evt@.len() as int, a1, -1, g2.start@[st.p2@[h] as int] as int),
{
    reveal(cov);
}

/// G2 transition k2: its RIGHT move (if any) was emitted.
/// After G2 position k2 (its RIGHT move emitted, if it has one): cov covers k2 + 1.
proof fn lemma_cov_right(
    tr: &Trans, st: &Pairs, g1: &Aut, g2: &Aut, ev: &Events, h: int, lo: int, a1: int, k2: int,
)
    requires
        0 <= h < st.p1@.len(),
        0 <= k2 < g2.evt@.len(),
        g2.evt@[k2] < ev.map2@.len(),
        cov(tr, st, g1, g2, ev, h, lo, tr.evt@.len() as int, a1, -1, k2),
        ev.mode@[ev.map2@[g2.evt@[k2] as int] as int] == RIGHT ==> found_in(
            tr, st, lo, tr.evt@.len() as int, ev.map2@[g2.evt@[k2] as int] as int, st.p1@[h] as int, g2.dst@[k2] as int),
    ensures
        cov(tr, st, g1, g2, ev, h, lo, tr.evt@.len() as int, a1, -1, k2 + 1),
{
    reveal(cov);
}

/// Both blocks walked: every move is emitted.
/// Both blocks walked to their ends: every move of h is covered, so complete(h).
proof fn lemma_cov_complete(tr: &Trans, st: &Pairs, g1: &Aut, g2: &Aut, ev: &Events, h: int, lo: int)
    requires
        0 <= h < st.p1@.len(),
        st.p1@[h] < g1.n,
        st.p2@[h] < g2.n,
        cov(tr, st, g1, g2, ev, h, lo, tr.evt@.len() as int,
            g1.start@[st.p1@[h] + 1] as int, -1, g2.start@[st.p2@[h] + 1] as int),
    ensures
        complete(tr, st, g1, g2, ev, h, lo, tr.evt@.len() as int),
{
    reveal(cov);
}

// ---------------------------------------------------------------------------------------------
// Facts extracted from the opaque bundles (so loops stay small)
// ---------------------------------------------------------------------------------------------

/// The basic facts inside inputs_ok (it is opaque): lengths, np, m1 ≤ m.
proof fn lemma_inputs_basic(g1: &Aut, g2: &Aut, ev: &Events, np: int)
    requires
        // Math: the inputs are ok (restated)
        inputs_ok(g1, g2, ev, np),
    ensures
        g1.init@.len() == g1.n,
        g1.marked@.len() == g1.n,
        g2.init@.len() == g2.n,
        g2.marked@.len() == g2.n,
        g1.start@.len() == g1.n + 1,
        g2.start@.len() == g2.n + 1,
        g1.dst@.len() == g1.evt@.len(),
        g2.dst@.len() == g2.evt@.len(),
        // Math: np = n1 · n2 ≤ 2^64 - 1; facts about the inputs, restated
        np == g1.n * g2.n,
        np <= u64::MAX,
        ev.m1 <= ev.mode@.len(),
        ev.inv2@.len() == ev.mode@.len(),
{
    reveal(inputs_ok);
}

/// G1's block of a: in range and sorted; its events are G1 events.
/// G1's block of a: inside evt1, sorted (pair form), events < m1, targets < n1.
proof fn lemma_blk1(g1: &Aut, g2: &Aut, ev: &Events, np: int, a: int)
    requires
        // Math: the inputs are ok (restated)
        inputs_ok(g1, g2, ev, np),
        0 <= a < g1.n,
    ensures
        g1.start@[a] <= g1.start@[a + 1] <= g1.evt@.len(),
        all_le(g1.evt@, g1.start@[a] as int, g1.start@[a + 1] as int),
        forall|k: int| g1.start@[a] <= k < g1.start@[a + 1] ==> #[trigger] g1.evt@[k] < ev.m1 && g1.dst@[k] < g1.n,
{
    reveal(inputs_ok);
    assert(g1.start@[a + 1] <= g1.start@[g1.n as int]);
    // Math: block a sorted (neighbour form), then pair form
    assert(sorted_blk(g1, a));
    lemma_all_le(g1.evt@, g1.start@[a] as int, g1.start@[a + 1] as int);
}

/// G2's block of b: in range and sorted; its events map into the output events.
/// G2's block of b: inside evt2, sorted (pair form), events < m2 with map2 < m, targets < n2.
proof fn lemma_blk2(g1: &Aut, g2: &Aut, ev: &Events, np: int, b: int)
    requires
        // Math: the inputs are ok (restated)
        inputs_ok(g1, g2, ev, np),
        0 <= b < g2.n,
    ensures
        g2.start@[b] <= g2.start@[b + 1] <= g2.evt@.len(),
        all_le(g2.evt@, g2.start@[b] as int, g2.start@[b + 1] as int),
        forall|k: int| g2.start@[b] <= k < g2.start@[b + 1] ==> #[trigger] g2.evt@[k] < ev.map2@.len()
            && g2.dst@[k] < g2.n && ev.map2@[g2.evt@[k] as int] < ev.mode@.len(),
{
    reveal(inputs_ok);
    assert(g2.start@[b + 1] <= g2.start@[g2.n as int]);
    // Math: block b sorted (neighbour form), then pair form
    assert(sorted_blk(g2, b));
    lemma_all_le(g2.evt@, g2.start@[b] as int, g2.start@[b + 1] as int);
}

/// What the mode table says about event e.
/// The mode facts of event e (from ev_ok inside inputs_ok).
proof fn lemma_mode(g1: &Aut, g2: &Aut, ev: &Events, np: int, e: int)
    requires
        // Math: the inputs are ok (restated)
        inputs_ok(g1, g2, ev, np),
        0 <= e < ev.mode@.len(),
    ensures
        ev.mode@[e] == LEFT ==> e < ev.m1,
        ev.mode@[e] == BOTH ==> e < ev.m1 && ev.inv2@[e] < ev.map2@.len(),
        ev.mode@[e] == RIGHT ==> e >= ev.m1,
{
    reveal(inputs_ok);
}

/// map2 is increasing on the G2-only events (numbers >= m1).
/// map2 is increasing on G2-only events (from ev_ok inside inputs_ok).
proof fn lemma_map2_mono(g1: &Aut, g2: &Aut, ev: &Events, np: int, i: int, j: int)
    requires
        // Math: the inputs are ok (restated)
        inputs_ok(g1, g2, ev, np),
        0 <= i <= j < ev.map2@.len(),
        ev.map2@[i] >= ev.m1,
        ev.map2@[j] >= ev.m1,
    ensures
        ev.map2@[i] <= ev.map2@[j],
{
    reveal(inputs_ok);
}

/// The facts inside cur_ok used by the walks (it is opaque).
proof fn lemma_cur_facts(
    tr: &Trans, st: &Pairs, seen: &Seen, g1: &Aut, g2: &Aut, ev: &Events, np: int, n0: int, h: int,
    prev: Option<usize>,
)
    requires
        cur_ok(tr, st, seen, g1, g2, ev, np, n0, h, prev),
    ensures
        0 <= h < st.p1@.len(),
        st.p2@.len() == st.p1@.len(),
        st.p1@[h] < g1.n,
        st.p2@[h] < g2.n,
        dst_in(tr, st),
        tr.start@.len() == h + 1,
        tr.start@[h] <= tr.evt@.len(),
{
    reveal(cur_ok);
    reveal(pairs_ok);
    reveal(tr_ok);
    reveal(done_ok);
}

/// After one step at (k1, k2): the claimed set grows by that move; ext chains.
/// After a step: the extensions compose, cov carries over, and the new move is found in the
/// whole block [lo, |evt|).
proof fn lemma_after_step(
    tr0: &Trans, st0: &Pairs, tr1: &Trans, st1: &Pairs, tr: &Trans, st: &Pairs,
    g1: &Aut, g2: &Aut, ev: &Events, h: int, lo: int, a1: int, b1: int, a2: int,
    e: int, c: int, d: int,
)
    requires
        ext_trans(tr0, tr1),
        ext_pairs(st0, st1),
        ext_trans(tr1, tr),
        ext_pairs(st1, st),
        dst_in(tr1, st1),
        0 <= h < st1.p1@.len(),
        0 <= lo <= tr1.evt@.len(),
        cov(tr1, st1, g1, g2, ev, h, lo, tr1.evt@.len() as int, a1, b1, a2),
        found_in(tr, st, tr1.evt@.len() as int, tr.evt@.len() as int, e, c, d),
    ensures
        ext_trans(tr0, tr),
        ext_pairs(st0, st),
        cov(tr, st, g1, g2, ev, h, lo, tr.evt@.len() as int, a1, b1, a2),
        found_in(tr, st, lo, tr.evt@.len() as int, e, c, d),
{
    // Math: cov carries over to the grown lists
    lemma_cov_ext(tr1, st1, tr, st, g1, g2, ev, h, lo, a1, b1, a2);
    // Math: the new move, found in [|evt1|, |evt|), is found in [lo, |evt|)
    lemma_found_widen(tr, st, tr1.evt@.len() as int, tr.evt@.len() as int, lo, tr.evt@.len() as int, e, c, d);
    // Math: tr0 ⊑ tr, st0 ⊑ st
    lemma_ext_trans(tr0, st0, tr1, st1, tr, st);
}

// ---------------------------------------------------------------------------------------------
// The walks
// ---------------------------------------------------------------------------------------------

/// The last emitted event of the current block is at most x.
/// Block h (from lo) is empty or its last event is ≤ x (the next event keeps it sorted).
pub open spec fn last_le(tr: &Trans, lo: int, x: int) -> bool {
    tr.evt@.len() > lo ==> tr.evt@[tr.evt@.len() - 1] as int <= x
}

/// All BOTH moves of state h through G1 transition k1.
fn walk_both(
    tr: &mut Trans,
    st: &mut Pairs,
    seen: &mut Seen,
    prev: &mut Option<usize>,
    g1: &Aut,
    g2: &Aut,
    ev: &Events,
    k1: usize,
    Ghost(np): Ghost<int>,
    Ghost(n0): Ghost<int>,
    hu: usize,
)
    requires
        // Math: the inputs are ok (restated)
        inputs_ok(g1, g2, ev, np),
        cur_ok(old(tr), old(st), old(seen), g1, g2, ev, np, n0, hu as int, *old(prev)),
        (hu as int) < old(st).p1@.len(),
        // Math: k1 ∈ block1(p1[h]), mode[evt1[k1]] = BOTH
        in_blk(g1, old(st).p1@[hu as int] as int, k1 as int),
        ev.mode@[g1.evt@[k1 as int] as int] == BOTH,
        // Math: all moves with G1 position < k1 are emitted
        cov(old(tr), old(st), g1, g2, ev, hu as int, old(tr).start@[hu as int] as int, old(tr).evt@.len() as int, k1 as int, -1, 0),
        // Math: block h's last event ≤ evt1[k1] (stays sorted)
        last_le(old(tr), old(tr).start@[hu as int] as int, g1.evt@[k1 as int] as int),
    ensures
        cur_ok(final(tr), final(st), final(seen), g1, g2, ev, np, n0, hu as int, *final(prev)),
        ext_trans(old(tr), final(tr)),
        ext_pairs(old(st), final(st)),
        final(tr).start@ == old(tr).start@,
        // Math: after: all moves with G1 position ≤ k1 are emitted
        cov(final(tr), final(st), g1, g2, ev, hu as int, old(tr).start@[hu as int] as int, final(tr).evt@.len() as int, k1 + 1, -1, 0),
        last_le(final(tr), old(tr).start@[hu as int] as int, g1.evt@[k1 as int] as int),
{
    // Math: h = hu; ghost copies of tr, st; lo = start[h]
    let ghost h = hu as int;
    // Math: tr0 = tr before block h (ghost)
    let ghost tr0 = *tr;
    let ghost st0 = *st;
    let ghost lo = tr.start@[h] as int;
    proof {
        // Math: facts from cur_ok (h < n, φ(h) in range, ...)
        lemma_cur_facts(tr, st, seen, g1, g2, ev, np, n0, h, *prev);
        // Math: basic input facts
        lemma_inputs_basic(g1, g2, ev, np);
    }
    // Math: (a, b) = φ(h)
    let a = st.p1[hu];
    let b = st.p2[hu];
    proof {
        // Math: G1's block of a: in range, sorted, events < m1
        lemma_blk1(g1, g2, ev, np, a as int);
        // Math: G2's block of b: in range, sorted, events mapped below m
        lemma_blk2(g1, g2, ev, np, b as int);
        // Math: the mode facts of e = evt1[k1] (BOTH: e < m1, inv2[e] < m2)
        lemma_mode(g1, g2, ev, np, g1.evt@[k1 as int] as int);
    }
    // Math: e = evt1[k1], c = dst1[k1], e2 = inv2[e] (G2's number of e)
    let e = g1.evt[k1];
    let c = g1.dst[k1];
    let e2 = ev.inv2[e];
    // Math: hi2 = end of G2's block of b
    let hi2 = g2.start[b + 1];
    // Math: r = first position of b's block with event ≥ e2
    let r = lbound(&g2.evt, g2.start[b], hi2, e2);
    proof {
        // Math: cov with (k1, r): G2 positions before r have events < e2, so no move there
        lemma_cov_both_start(tr, st, g1, g2, ev, h, lo, k1 as int, r as int);
    }
    // Math: k2 = r; walk G2's transitions on e2
    let mut k2 = r;
    while k2 < hi2 && g2.evt[k2] == e2
        invariant
            // Math: the inputs are ok (restated)
            inputs_ok(g1, g2, ev, np),
            // Math: cur_ok: block h being written, everything consistent
            cur_ok(tr, st, seen, g1, g2, ev, np, n0, h, *prev),
            // Math: tr, st only grew since the call; start unchanged
            ext_trans(&tr0, tr),
            ext_pairs(&st0, st),
            tr.start@ == tr0.start@,
            // Math: h = hu (ghost and run-time copies of the state number)
            h == hu as int,
            st.p1@.len() > h,
            // Math: φ(h) = (a, b)
            st.p1@[h] == a,
            st.p2@[h] == b,
            // Math: lo = start[h], where block h starts
            lo == tr.start@[h],
            // Math: k1 < T1; e = evt1[k1], c = dst1[k1], e2 = inv2[e], mode[e] = BOTH
            k1 < g1.evt@.len(),
            e == g1.evt@[k1 as int],
            c == g1.dst@[k1 as int],
            e2 == ev.inv2@[e as int],
            (e as int) < ev.mode@.len(),
            ev.mode@[e as int] == BOTH,
            in_blk(g1, a as int, k1 as int),
            b < g2.n,
            hi2 == g2.start@[b as int + 1],
            hi2 <= g2.evt@.len(),
            g2.dst@.len() == g2.evt@.len(),
            // Math: start2[b] ≤ r ≤ k2 ≤ hi2
            g2.start@[b as int] <= r <= k2 <= hi2,
            all_le(g2.evt@, g2.start@[b as int] as int, hi2 as int),
            // Math: from r on, events ≥ e2
            forall|k: int| r <= k < hi2 ==> #[trigger] g2.evt@[k] >= e2,
            // Math: moves with G1 position < k1, or = k1 with G2 position < k2, are emitted
            cov(tr, st, g1, g2, ev, h, lo, tr.evt@.len() as int, k1 as int, k2 as int, 0),
            // Math: block h's last event ≤ e
            last_le(tr, lo, e as int),
        decreases hi2 - k2,
    {
        // Math: d = dst2[k2]
        let d = g2.dst[k2];
        // Why: ghost copies before this step.
        let ghost tr1 = *tr;
        let ghost st1 = *st;
        proof {
            // Math: facts from cur_ok (h < n, φ(h) in range, ...)
            lemma_cur_facts(tr, st, seen, g1, g2, ev, np, n0, h, *prev);
            // Math: (e, c, d) is a BOTH move from (a, b), by k1 and k2
            assert(move_by(g1, g2, ev, a as int, b as int, e as int, c as int, d as int, k1 as int, k2 as int));
        }
        // Math: emit h --e--> state(c, d)
        step(tr, st, seen, prev, g1, g2, ev, e, c, d, Ghost(k1 as int), Ghost(k2 as int), Ghost(np), Ghost(n0), Ghost(h));
        proof {
            // Math: the loop invariant after the step (cov grows by the move just emitted)
            lemma_after_step(&tr0, &st0, &tr1, &st1, tr, st, g1, g2, ev, h, lo, k1 as int, k2 as int, 0, e as int, c as int, d as int);
            // Math: cov now covers (k1, k2 + 1)
            lemma_cov_both_step(tr, st, g1, g2, ev, h, lo, k1 as int, k2 as int);
        }
        // Math: k2 := k2 + 1
        k2 = k2 + 1;
    }
    proof {
        // Math: from k2 on, events > e2 (evt2[k2] ≠ e2 and ≥ e2, sorted), so no more moves
        assert forall|k: int| k2 <= k && in_blk(g2, b as int, k) implies #[trigger] g2.evt@[k] > e2 by {
            assert(g2.evt@[k2 as int] <= g2.evt@[k]);
        }
        // Math: cov covers k1 + 1
        lemma_cov_both_end(tr, st, g1, g2, ev, h, lo, k1 as int, k2 as int);
    }
}

/// All LEFT and BOTH moves of state h (G1's block of p1[h]).
fn walk_left(
    tr: &mut Trans,
    st: &mut Pairs,
    seen: &mut Seen,
    prev: &mut Option<usize>,
    g1: &Aut,
    g2: &Aut,
    ev: &Events,
    Ghost(np): Ghost<int>,
    Ghost(n0): Ghost<int>,
    hu: usize,
)
    requires
        // Math: the inputs are ok (restated)
        inputs_ok(g1, g2, ev, np),
        cur_ok(old(tr), old(st), old(seen), g1, g2, ev, np, n0, hu as int, *old(prev)),
        // Math: block h is empty so far
        old(tr).evt@.len() == old(tr).start@[hu as int],
    ensures
        cur_ok(final(tr), final(st), final(seen), g1, g2, ev, np, n0, hu as int, *final(prev)),
        ext_trans(old(tr), final(tr)),
        ext_pairs(old(st), final(st)),
        final(tr).start@ == old(tr).start@,
        // Math: h < n, p1[h] < n1
        (hu as int) < final(st).p1@.len(),
        final(st).p1@[hu as int] < g1.n,
        // Math: all moves with a G1 position (LEFT and BOTH) are emitted
        cov(final(tr), final(st), g1, g2, ev, hu as int, old(tr).start@[hu as int] as int, final(tr).evt@.len() as int,
            g1.start@[final(st).p1@[hu as int] as int + 1] as int, -1, 0),
        // Math: block h's events so far are < m1 (G1 events)
        last_le(final(tr), old(tr).start@[hu as int] as int, ev.m1 as int - 1),
{
    // Math: h = hu; ghost copies of tr, st; lo = start[h]
    let ghost h = hu as int;
    let ghost tr0 = *tr;
    let ghost st0 = *st;
    let ghost lo = tr.start@[h] as int;
    proof {
        // Math: facts from cur_ok (h < n, φ(h) in range, ...)
        lemma_cur_facts(tr, st, seen, g1, g2, ev, np, n0, h, *prev);
        // Math: basic input facts
        lemma_inputs_basic(g1, g2, ev, np);
    }
    // Math: (a, b) = φ(h)
    let a = st.p1[hu];
    let b = st.p2[hu];
    proof {
        // Math: G1's block of a: in range, sorted, events < m1
        lemma_blk1(g1, g2, ev, np, a as int);
        // Math: cov at the start (nothing covered)
        lemma_cov_start(tr, st, g1, g2, ev, h, lo);
    }
    // Math: [k1, hi1) = G1's block of a, walked by k1
    let hi1 = g1.start[a + 1];
    let mut k1 = g1.start[a];
    while k1 < hi1
        invariant
            // Math: the inputs are ok (restated)
            inputs_ok(g1, g2, ev, np),
            // Math: cur_ok: block h being written, everything consistent
            cur_ok(tr, st, seen, g1, g2, ev, np, n0, h, *prev),
            // Math: tr, st only grew since the call; start unchanged
            ext_trans(&tr0, tr),
            ext_pairs(&st0, st),
            tr.start@ == tr0.start@,
            // Math: h = hu (ghost and run-time copies of the state number)
            h == hu as int,
            st.p1@.len() > h,
            // Math: φ(h) = (a, b)
            st.p1@[h] == a,
            st.p2@[h] == b,
            // Math: a < n1, b < n2
            a < g1.n,
            b < g2.n,
            // Math: lo = start[h], where block h starts
            lo == tr.start@[h],
            // Math: hi1 = start1[a+1] ≤ T1
            hi1 == g1.start@[a as int + 1],
            hi1 <= g1.evt@.len(),
            g1.dst@.len() == g1.evt@.len(),
            // Math: m ≥ m1
            ev.mode@.len() >= ev.m1,
            // Math: start1[a] ≤ k1 ≤ hi1
            g1.start@[a as int] <= k1 <= hi1,
            // Math: G1's block of a is sorted
            all_le(g1.evt@, g1.start@[a as int] as int, hi1 as int),
            // Math: its events < m1, targets < n1
            forall|k: int| g1.start@[a as int] <= k < hi1 ==> #[trigger] g1.evt@[k] < ev.m1 && g1.dst@[k] < g1.n,
            // Math: moves with G1 position < k1 are emitted
            cov(tr, st, g1, g2, ev, h, lo, tr.evt@.len() as int, k1 as int, -1, 0),
            // Math: block h non-empty → its last event ≤ evt1[k1-1]
            // Why: the next event evt1[k1] ≥ evt1[k1-1] keeps it sorted.
            tr.evt@.len() > lo ==> k1 > g1.start@[a as int] && tr.evt@[tr.evt@.len() - 1] <= g1.evt@[k1 - 1],
        // Math: hi1 - k1 decreases
        decreases hi1 - k1,
    {
        // Math: e = evt1[k1], md = mode[e]
        let e = g1.evt[k1];
        let md = ev.mode[e];
        // Why: ghost copies before this step.
        let ghost tr1 = *tr;
        let ghost st1 = *st;
        proof {
            // Math: last ≤ evt1[k1-1] ≤ evt1[k1] = e
            if tr.evt@.len() > lo {
                assert(g1.evt@[k1 - 1] <= g1.evt@[k1 as int]);
            }
            // Math: block h's last event ≤ e
            assert(last_le(tr, lo, e as int));
            // Math: k1 ∈ block1(a)
            assert(in_blk(g1, a as int, k1 as int));
        }
        // Math: LEFT: one move to (c, b)
        if md == LEFT {
            // Math: c = dst1[k1]
            let c = g1.dst[k1];
            proof {
                // Math: facts from cur_ok (h < n, φ(h) in range, ...)
                lemma_cur_facts(tr, st, seen, g1, g2, ev, np, n0, h, *prev);
                // Math: (e, c, b) is a LEFT move
                assert(move_by(g1, g2, ev, a as int, b as int, e as int, c as int, b as int, k1 as int, -1));
            }
            // Math: emit h --e--> state(c, b)
            step(tr, st, seen, prev, g1, g2, ev, e, c, b, Ghost(k1 as int), Ghost(-1), Ghost(np), Ghost(n0), Ghost(h));
            proof {
                // Math: the loop invariant after the step
                lemma_after_step(&tr0, &st0, &tr1, &st1, tr, st, g1, g2, ev, h, lo, k1 as int, -1, 0, e as int, c as int, b as int);
                // Math: cov covers k1 + 1
                lemma_cov_left(tr, st, g1, g2, ev, h, lo, k1 as int);
            }
        // Math: BOTH: all G2 partners (walk_both)
        } else if md == BOTH {
            // Math: emit every BOTH move by k1
            walk_both(tr, st, seen, prev, g1, g2, ev, k1, Ghost(np), Ghost(n0), hu);
            proof {
                // Math: the extensions compose (tr0 ⊑ tr1 ⊑ tr)
                lemma_ext_trans(&tr0, &st0, &tr1, &st1, tr, st);
            }
        } else {
            proof {
                // Math: NONE/RIGHT here: no G1 move by k1; cov covers k1 + 1
                lemma_cov_none(tr, st, g1, g2, ev, h, lo, k1 as int);
            }
        }
        // Math: k1 := k1 + 1
        k1 = k1 + 1;
    }
    proof {
        // Math: facts from cur_ok (h < n, φ(h) in range, ...)
        lemma_cur_facts(tr, st, seen, g1, g2, ev, np, n0, h, *prev);
        if tr.evt@.len() > lo {
            // Math: block h's last event ≤ evt1[k1-1] < m1
            assert(g1.evt@[k1 - 1] < ev.m1);
        }
    }
}

/// All RIGHT moves of state h (G2's block of p2[h]).
fn walk_right(
    tr: &mut Trans,
    st: &mut Pairs,
    seen: &mut Seen,
    prev: &mut Option<usize>,
    g1: &Aut,
    g2: &Aut,
    ev: &Events,
    Ghost(np): Ghost<int>,
    Ghost(n0): Ghost<int>,
    hu: usize,
    Ghost(a1): Ghost<int>,
)
    requires
        // Math: the inputs are ok (restated)
        inputs_ok(g1, g2, ev, np),
        cur_ok(old(tr), old(st), old(seen), g1, g2, ev, np, n0, hu as int, *old(prev)),
        // Math: all moves with a G1 position are emitted (a1 = end of G1's block)
        cov(old(tr), old(st), g1, g2, ev, hu as int, old(tr).start@[hu as int] as int, old(tr).evt@.len() as int, a1, -1, 0),
        // Math: block h's events so far are < m1
        last_le(old(tr), old(tr).start@[hu as int] as int, ev.m1 as int - 1),
    ensures
        cur_ok(final(tr), final(st), final(seen), g1, g2, ev, np, n0, hu as int, *final(prev)),
        ext_trans(old(tr), final(tr)),
        ext_pairs(old(st), final(st)),
        final(tr).start@ == old(tr).start@,
        (hu as int) < final(st).p1@.len(),
        // Math: p2[h] < n2; φ(h) unchanged
        final(st).p2@[hu as int] < g2.n,
        final(st).p1@[hu as int] == old(st).p1@[hu as int],
        final(st).p2@[hu as int] == old(st).p2@[hu as int],
        cov(final(tr), final(st), g1, g2, ev, hu as int, old(tr).start@[hu as int] as int, final(tr).evt@.len() as int,
            // Math: after: also all RIGHT moves (whole G2 block of b)
            a1, -1, g2.start@[final(st).p2@[hu as int] as int + 1] as int),
{
    // Math: h = hu; ghost copies of tr, st; lo = start[h]
    let ghost h = hu as int;
    let ghost tr0 = *tr;
    let ghost st0 = *st;
    let ghost lo = tr.start@[h] as int;
    proof {
        // Math: facts from cur_ok (h < n, φ(h) in range, ...)
        lemma_cur_facts(tr, st, seen, g1, g2, ev, np, n0, h, *prev);
        // Math: basic input facts
        lemma_inputs_basic(g1, g2, ev, np);
    }
    // Math: (a, b) = φ(h)
    let a = st.p1[hu];
    let b = st.p2[hu];
    proof {
        // Math: G2's block of b: in range, sorted, events mapped below m
        lemma_blk2(g1, g2, ev, np, b as int);
        // Math: cov in the RIGHT phase, no RIGHT move yet
        lemma_cov_mid(tr, st, g1, g2, ev, h, lo, a1);
    }
    let hi2 = g2.start[b + 1];
    // Math: k2 walks G2's block of b
    let mut k2 = g2.start[b];
    // Math: last2 = the G2 position of the last RIGHT move emitted (ghost)
    let ghost mut last2: int = -1;
    while k2 < hi2
        invariant
            // Math: the inputs are ok (restated)
            inputs_ok(g1, g2, ev, np),
            // Math: cur_ok: block h being written, everything consistent
            cur_ok(tr, st, seen, g1, g2, ev, np, n0, h, *prev),
            // Math: tr, st only grew since the call; start unchanged
            ext_trans(&tr0, tr),
            ext_pairs(&st0, st),
            tr.start@ == tr0.start@,
            // Math: h = hu (ghost and run-time copies of the state number)
            h == hu as int,
            st.p1@.len() > h,
            // Math: φ(h) = (a, b)
            st.p1@[h] == a,
            st.p2@[h] == b,
            // Math: a < n1, b < n2
            a < g1.n,
            b < g2.n,
            // Math: lo = start[h], where block h starts
            lo == tr.start@[h],
            // Math: hi2 = start2[b+1] ≤ T2
            hi2 == g2.start@[b as int + 1],
            hi2 <= g2.evt@.len(),
            g2.dst@.len() == g2.evt@.len(),
            // Math: start2[b] ≤ k2 ≤ hi2, block sorted
            g2.start@[b as int] <= k2 <= hi2,
            all_le(g2.evt@, g2.start@[b as int] as int, hi2 as int),
            // Math: its events < m2, targets < n2, map2[evt2[k]] < m
            forall|k: int| g2.start@[b as int] <= k < hi2 ==> #[trigger] g2.evt@[k] < ev.map2@.len()
                && g2.dst@[k] < g2.n && ev.map2@[g2.evt@[k] as int] < ev.mode@.len(),
            // Math: G1 moves and RIGHT moves with G2 position < k2 are emitted
            cov(tr, st, g1, g2, ev, h, lo, tr.evt@.len() as int, a1, -1, k2 as int),
            // Math: block h's last event: < m1 (a G1 event), or map2[evt2[last2]] ≥ m1 with last2 < k2
            // Why: map2 is increasing on G2-only events, so the next one is not smaller.
            tr.evt@.len() > lo ==> (tr.evt@[tr.evt@.len() - 1] < ev.m1 || (g2.start@[b as int] <= last2 < k2
                && tr.evt@[tr.evt@.len() - 1] == ev.map2@[g2.evt@[last2] as int] && ev.map2@[g2.evt@[last2] as int] >= ev.m1)),
        // Math: hi2 - k2 decreases
        decreases hi2 - k2,
    {
        // Math: e = map2[evt2[k2]], the output event
        let e = ev.map2[g2.evt[k2]];
        // Why: ghost copies before this step.
        let ghost tr1 = *tr;
        let ghost st1 = *st;
        proof {
            // Math: mode facts of e
            lemma_mode(g1, g2, ev, np, e as int);
        }
        // Math: a RIGHT move (G2-only event)
        if e >= ev.m1 && ev.mode[e] == RIGHT {
            // Math: d = dst2[k2]
            let d = g2.dst[k2];
            proof {
                // Math: facts from cur_ok (h < n, φ(h) in range, ...)
                lemma_cur_facts(tr, st, seen, g1, g2, ev, np, n0, h, *prev);
                // Math: last event from G2 (position last2 < k2): evt2[last2] ≤ evt2[k2], so map2 of them ≤
                if tr.evt@.len() > lo && tr.evt@[tr.evt@.len() - 1] >= ev.m1 {
                    assert(g2.evt@[last2] <= g2.evt@[k2 as int]);
                    lemma_map2_mono(g1, g2, ev, np, g2.evt@[last2] as int, g2.evt@[k2 as int] as int);
                }
                // Math: block h's last event ≤ e
                assert(last_le(tr, lo, e as int));
                // Math: k2 ∈ block2(b)
                assert(in_blk(g2, b as int, k2 as int));
                // Math: (e, a, d) is a RIGHT move
                assert(move_by(g1, g2, ev, a as int, b as int, e as int, a as int, d as int, -1, k2 as int));
            }
            // Math: emit h --e--> state(a, d)
            step(tr, st, seen, prev, g1, g2, ev, e, a, d, Ghost(-1), Ghost(k2 as int), Ghost(np), Ghost(n0), Ghost(h));
            proof {
                // Math: the loop invariant after the step
                lemma_after_step(&tr0, &st0, &tr1, &st1, tr, st, g1, g2, ev, h, lo, a1, -1, k2 as int, e as int, a as int, d as int);
                // Math: cov covers k2 + 1
                lemma_cov_right(tr, st, g1, g2, ev, h, lo, a1, k2 as int);
                // Math: last2 := k2
                last2 = k2 as int;
            }
        } else {
            proof {
                // Math: cov covers k2 + 1
                lemma_cov_right(tr, st, g1, g2, ev, h, lo, a1, k2 as int);
            }
        }
        // Math: k2 := k2 + 1
        k2 = k2 + 1;
    }
    proof {
        // Math: facts from cur_ok (h < n, φ(h) in range, ...)
        lemma_cur_facts(tr, st, seen, g1, g2, ev, np, n0, h, *prev);
    }
}

// ---------------------------------------------------------------------------------------------
// Between states, and the result
// ---------------------------------------------------------------------------------------------

/// Blocks 0..h are finished and nothing of block h is written yet.
#[verifier::opaque]
pub open spec fn outer_ok(
    tr: &Trans,
    st: &Pairs,
    seen: &Seen,
    g1: &Aut,
    g2: &Aut,
    ev: &Events,
    np: int,
    n0: int,
    h: int,
) -> bool {
    // Math: h ≤ n; pairs, table, init_in, transitions ok; blocks 0 .. h-1 finished
    &&& 0 <= h <= st.p1@.len()
    &&& pairs_ok(st, g1, g2, n0)
    &&& seen_ok(seen, st, g2.n as int, np)
    &&& init_in(seen, g1, g2)
    &&& tr_ok(tr, st, ev)
    &&& done_ok(tr, st, g1, g2, ev, h)
    // Math: start[h] = |evt|: nothing of block h written yet
    &&& tr.start@[h] == tr.evt@.len()
    &&& det_ok(tr, h, n0)
    // Math: n0 > 0 ∨ n = 0 (states exist only if an initial pair does)
    &&& (n0 > 0 || st.p1@.len() == 0)
}

/// The number of states is at most np: one key per state, all keys below np.
proof fn lemma_len_bound(seen: &Seen, st: &Pairs, n2: int, np: int)
    requires
        seen_ok(seen, st, n2, np),
        0 <= np,
    ensures
        st.p1@.len() <= np,
{
    reveal(seen_ok);
    // Math: n = |used| ≤ np
    lemma_used_bound(seen.used@, np);
}

/// Starting block h: outer_ok gives cur_ok with an empty block and prev = None.
proof fn lemma_outer_to_cur(
    tr: &Trans, st: &Pairs, seen: &Seen, g1: &Aut, g2: &Aut, ev: &Events, np: int, n0: int, h: int,
)
    requires
        outer_ok(tr, st, seen, g1, g2, ev, np, n0, h),
        h < st.p1@.len(),
    ensures
        cur_ok(tr, st, seen, g1, g2, ev, np, n0, h, None),
        tr.evt@.len() == tr.start@[h],
{
    reveal(outer_ok);
    reveal(cur_ok);
    reveal(blk_ok);
    // Why: open the opaque bundles used here.
    reveal(adj_le);
}

/// Closing block h: its positions [start[h], t) are sound, sorted and complete.
/// Closing block h at t (start := start · [t]): the block over [start[h], t), sound, sorted
/// and complete, is finished.
proof fn lemma_blk_close(
    tr0: &Trans, tr: &Trans, st: &Pairs, g1: &Aut, g2: &Aut, ev: &Events, h: int, t: usize,
)
    requires
        0 <= h,
        tr0.start@.len() == h + 1,
        blk_ok(tr0, st, g1, g2, ev, h, tr0.start@[h] as int, t as int),
        complete(tr0, st, g1, g2, ev, h, tr0.start@[h] as int, t as int),
        tr.start@ == tr0.start@.push(t),
        tr.evt@ == tr0.evt@,
        tr.dst@ == tr0.dst@,
        tr.w1@ == tr0.w1@,
        tr.w2@ == tr0.w2@,
    ensures
        blk_done(tr, st, g1, g2, ev, h),
{
    // Why: open the opaque bundles used here.
    reveal(adj_le);
    reveal(blk_ok);
    let lo = tr0.start@[h] as int;
    // Math: start[h] unchanged, start[h+1] = t
    assert(tr.start@[h] == tr0.start@[h]);
    // Math: start[h+1] = t = |evt|
    assert(tr.start@[h + 1] == t);
    // Math: sound at each k (same lists)
    assert forall|k: int| lo <= k < t as int implies #[trigger] sound_at(tr, st, g1, g2, ev, h, k) by {
        assert(sound_at(tr0, st, g1, g2, ev, h, k));
    }
    assert forall|e: int, c: int, d: int, k1: int, k2: int|
        #[trigger] move_by(g1, g2, ev, st.p1@[h] as int, st.p2@[h] as int, e, c, d, k1, k2)
        implies found_in(tr, st, lo, t as int, e, c, d) by {
        // Math: complete: each move found (same lists)
        assert(found_in(tr0, st, lo, t as int, e, c, d));
        let k = choose|k: int| lo <= k < t as int && #[trigger] tr0.evt@[k] as int == e
            && st.p1@[tr0.dst@[k] as int] as int == c && st.p2@[tr0.dst@[k] as int] as int == d;
        assert(tr.evt@[k] == tr0.evt@[k]);
    }
}

/// Closing block h: the finished blocks are now 0..h+1.
/// done_ok at h + 1 after closing block h.
proof fn lemma_done_push(
    tr0: &Trans, tr: &Trans, st: &Pairs, g1: &Aut, g2: &Aut, ev: &Events, h: int, t: usize,
)
    requires
        done_ok(tr0, st, g1, g2, ev, h),
        dst_in(tr0, st),
        0 <= h < st.p1@.len(),
        blk_ok(tr0, st, g1, g2, ev, h, tr0.start@[h] as int, t as int),
        complete(tr0, st, g1, g2, ev, h, tr0.start@[h] as int, t as int),
        t == tr0.evt@.len(),
        tr.start@ == tr0.start@.push(t),
        tr.evt@ == tr0.evt@,
        tr.dst@ == tr0.dst@,
        tr.w1@ == tr0.w1@,
        tr.w2@ == tr0.w2@,
    ensures
        done_ok(tr, st, g1, g2, ev, h + 1),
{
    reveal(done_ok);
    // Math: |start| = h + 1
    assert(tr0.start@.len() == h + 1);
    // Math: tr extends tr0 (same lists, one more start)
    assert(ext_trans(tr0, tr));
    assert(ext_pairs(st, st));
    lemma_all_le(tr0.start@, 0, h + 1);
    assert forall|i: int| 0 <= i < h implies #[trigger] blk_done(tr, st, g1, g2, ev, i) by {
        assert(tr0.start@[i + 1] <= tr0.start@[h]);
        assert(blk_done(tr0, st, g1, g2, ev, i));
        lemma_blk_done_ext(tr0, st, tr, st, g1, g2, ev, i);
    }
    // Math: block h is finished
    lemma_blk_close(tr0, tr, st, g1, g2, ev, h, t);
    // Math: start · [t] still sorted (t = |evt| ≥ start[h])
    lemma_adj_push(tr0.start@, tr.start@, t);
}

/// Pushing a value no smaller than the last keeps a sequence ordered.
/// Appending t ≥ the last element keeps a sequence sorted (neighbour form).
proof fn lemma_adj_push(s0: Seq<usize>, s: Seq<usize>, t: usize)
    requires
        s0.len() > 0,
        adj_le(s0, 0, s0.len() as int),
        s0[s0.len() - 1] <= t,
        s == s0.push(t),
    ensures
        adj_le(s, 0, s.len() as int),
{
    // Why: open the opaque bundles used here.
    reveal(adj_le);
    assert forall|k: int| 0 <= k && k + 1 < s.len() implies #[trigger] s[k] <= s[k + 1] by {
        if k + 1 < s0.len() {
            assert(s0[k] <= s0[k + 1]);
        }
    }
}

/// Closing block h: the determinism flag now covers blocks 0..h+1.
/// det_ok at h + 1 after closing block h: "block h so far" becomes strict_blk(h).
proof fn lemma_det_push(tr0: &Trans, tr: &Trans, h: int, n0: int, t: usize)
    requires
        det_ok(tr0, h, n0),
        0 <= h,
        tr0.start@.len() == h + 1,
        t == tr0.evt@.len(),
        tr.start@ == tr0.start@.push(t),
        tr.evt@ == tr0.evt@,
        tr.det == tr0.det,
    ensures
        det_ok(tr, h + 1, n0),
{
    reveal(det_ok);
    reveal(all_strict);
    let lo = tr0.start@[h] as int;
    assert forall|i: int| 0 <= i < h implies #[trigger] strict_blk(tr, i) == strict_blk(tr0, i) by {
        assert(tr.start@[i] == tr0.start@[i]);
        assert(tr.start@[i + 1] == tr0.start@[i + 1]);
    }
    // Math: strict_blk(h) = strict(evt, start[h], t)
    assert(strict_blk(tr, h) == strict(tr0.evt@, lo, t as int)) by {
        // Math: start[h] unchanged, start[h+1] = t
        assert(tr.start@[h] == tr0.start@[h]);
        // Math: start[h+1] = t = |evt|
        assert(tr.start@[h + 1] == t);
    }
    // Math: start[h+1] = t = |evt|
    assert(tr.start@[h + 1] == t);
    // Math: → all_strict(h + 1)
    if all_strict(tr0, h) && strict(tr0.evt@, lo, t as int) {
        assert forall|i: int| 0 <= i < h + 1 implies #[trigger] strict_blk(tr, i) by {
            if i < h {
                assert(strict_blk(tr0, i));
            }
        }
    }
    // Math: ← all_strict(h) and block h strict
    if all_strict(tr, h + 1) {
        assert forall|i: int| 0 <= i < h implies #[trigger] strict_blk(tr0, i) by {
            assert(strict_blk(tr, i));
        }
        assert(strict_blk(tr, h));
    }
}

/// tr_ok depends only on evt, dst, w1, w2: the same lists give the same answer.
proof fn lemma_tr_ok_same(tr0: &Trans, tr: &Trans, st: &Pairs, ev: &Events)
    requires
        tr_ok(tr0, st, ev),
        tr.evt@ == tr0.evt@,
        tr.dst@ == tr0.dst@,
        tr.w1@ == tr0.w1@,
        tr.w2@ == tr0.w2@,
    ensures
        tr_ok(tr, st, ev),
        dst_in(tr, st),
{
    reveal(tr_ok);
}

/// Closing block h: from cur_ok and complete(h) to outer_ok at h + 1.
proof fn lemma_cur_to_outer(
    tr0: &Trans, tr: &Trans, st: &Pairs, seen: &Seen, g1: &Aut, g2: &Aut, ev: &Events, np: int,
    n0: int, h: int, prev: Option<usize>, t: usize,
)
    requires
        cur_ok(tr0, st, seen, g1, g2, ev, np, n0, h, prev),
        (n0 > 0 || st.p1@.len() == 0),
        complete(tr0, st, g1, g2, ev, h, tr0.start@[h] as int, tr0.evt@.len() as int),
        t == tr0.evt@.len(),
        tr.start@ == tr0.start@.push(t),
        tr.evt@ == tr0.evt@,
        tr.dst@ == tr0.dst@,
        tr.w1@ == tr0.w1@,
        tr.w2@ == tr0.w2@,
        tr.det == tr0.det,
    ensures
        outer_ok(tr, st, seen, g1, g2, ev, np, n0, h + 1),
{
    reveal(cur_ok);
    // Math: tr_ok for tr (same lists)
    lemma_tr_ok_same(tr0, tr, st, ev);
    // Math: dst_in for tr0
    lemma_tr_ok_same(tr0, tr0, st, ev);
    assert(tr0.start@.len() == h + 1) by {
        reveal(done_ok);
    }
    // Math: done_ok at h + 1
    lemma_done_push(tr0, tr, st, g1, g2, ev, h, t);
    // Math: det_ok at h + 1
    lemma_det_push(tr0, tr, h, n0, t);
    reveal(outer_ok);
    // Math: start[h+1] = t = |evt|
    assert(tr.start@[h + 1] == t);
}

/// The output: a valid encoding whose states are pairs, whose transitions are exactly the moves
/// of the composition, with the right initial and marked flags, and an exact determinism flag.
/// The search's postcondition, in positions (compose.rs turns it into Lean's IsComposition):
/// the labels and flags, the initial pairs, the encoding, every block finished, det exact.
pub open spec fn composition_ok(g1: &Aut, g2: &Aut, ev: &Events, st: &Pairs, tr: &Trans) -> bool {
    // Math: n = |p1|, the number of output states
    let n = st.p1@.len() as int;
    // Math: |p2| = |init| = |marked| = n
    &&& st.p2@.len() == n
    &&& st.init@.len() == n
    &&& st.marked@.len() == n
    // Math: ∀ i: φ(i) ∈ [0, n1) × [0, n2); marked and init are the conjunctions of the sides
    &&& forall|i: int| 0 <= i < n ==> {
        &&& #[trigger] st.p1@[i] < g1.n
        &&& st.p2@[i] < g2.n
        &&& st.marked@[i] == (g1.marked@[st.p1@[i] as int] && g2.marked@[st.p2@[i] as int])
        &&& st.init@[i] == (g1.init@[st.p1@[i] as int] && g2.init@[st.p2@[i] as int])
    }
    // Math: ∀ (a, b) ∈ X01 × X02, ∃ i: φ(i) = (a, b)  (init_complete)
    &&& forall|a: int, b: int| 0 <= a < g1.n && 0 <= b < g2.n && #[trigger] g1.init@[a] && #[trigger] g2.init@[b]
        ==> exists|i: int| 0 <= i < n && #[trigger] st.p1@[i] == a && st.p2@[i] == b
    // Math: n > 0 → some state is initial (W3)
    &&& (n > 0 ==> exists|i: int| 0 <= i < n && #[trigger] st.init@[i])
    // Math: the blocks: |start| = n + 1, start[0] = 0, start[n] = T, sorted; |dst| = |evt|
    &&& tr.start@.len() == n + 1
    &&& tr.start@[0] == 0
    &&& tr.start@[n as int] == tr.evt@.len()
    &&& adj_le(tr.start@, 0, n + 1)
    &&& tr.dst@.len() == tr.evt@.len()
    // Math: ∀ k: evt[k] < m, mode[evt[k]] ≠ NONE, dst[k] < n
    &&& forall|k: int| 0 <= k < tr.evt@.len() ==> {
        &&& #[trigger] tr.evt@[k] < ev.mode@.len()
        &&& ev.mode@[tr.evt@[k] as int] != NONE
        &&& tr.dst@[k] < n
    }
    // Math: ∀ i: blk_done(i) (sound, sorted, complete)
    &&& forall|i: int| 0 <= i < n ==> #[trigger] blk_done(tr, st, g1, g2, ev, i)
    // Math: det ↔ at most one initial state ∧ no repeated event in a block
    &&& tr.det == ((forall|i: int, j: int| 0 <= i < n && 0 <= j < n && #[trigger] st.init@[i] && #[trigger] st.init@[j] ==> i == j)
        && (forall|i: int| 0 <= i < n ==> #[trigger] strict_blk(tr, i)))
}

/// At the end of the search (h = n): composition_ok.
proof fn lemma_final(
    tr: &Trans, st: &Pairs, seen: &Seen, g1: &Aut, g2: &Aut, ev: &Events, np: int, n0: int,
)
    requires
        outer_ok(tr, st, seen, g1, g2, ev, np, n0, st.p1@.len() as int),
        // Math: np = n1 · n2 ≤ 2^64 - 1; facts about the inputs, restated
        np == g1.n * g2.n,
    ensures
        composition_ok(g1, g2, ev, st, tr),
{
    reveal(outer_ok);
    reveal(pairs_ok);
    reveal(seen_ok);
    reveal(init_in);
    reveal(tr_ok);
    reveal(done_ok);
    reveal(det_ok);
    reveal(all_strict);
    reveal(blk_ok);
    // Math: n = |p1|, the number of output states
    let n = st.p1@.len() as int;
    assert forall|a: int, b: int| 0 <= a < g1.n && 0 <= b < g2.n && #[trigger] g1.init@[a] && #[trigger] g2.init@[b]
        implies exists|i: int| 0 <= i < n && #[trigger] st.p1@[i] == a && st.p2@[i] == b by {
        lemma_key_range(a, b, g1.n as int, g2.n as int);
        // Math: x = key(a, b); i = tab_at(x)
        let x = key(a, b, g2.n as int);
        assert(in_tab(seen, x));
        let i = tab_at(seen, x);
        // Math: key(φ(i)) = x = key(a, b) → φ(i) = (a, b)
        lemma_key_inj(st.p1@[i] as int, st.p2@[i] as int, a, b, g2.n as int);
        assert(st.p1@[i] == a);
    }
    // Math: n > 0 → n0 > 0 (outer_ok), so state 0 is initial
    if n > 0 {
        assert(st.p1@[0] < g1.n);
        assert(st.init@[0]);
    }
    // Math: n0 ≥ 2: states 0 and 1 are both initial (so det is false: two initial states)
    if n0 >= 2 {
        assert(st.p1@[0] < g1.n);
        assert(st.p1@[1] < g1.n);
        assert(st.init@[0] && st.init@[1]);
    }
    // Math: n0 ≤ 1: at most one initial state
    if n0 <= 1 {
        assert forall|i: int, j: int| 0 <= i < n && 0 <= j < n && #[trigger] st.init@[i] && #[trigger] st.init@[j] implies i == j by {
            assert(st.p1@[i] < g1.n);
            assert(st.p1@[j] < g1.n);
        }
    }
    // Math: start sorted
    assert(adj_le(tr.start@, 0, n + 1));
    // Math: all_strict(n) unfolded
    assert(all_strict(tr, n) == (forall|i: int| 0 <= i < n ==> #[trigger] strict_blk(tr, i)));
    assert(tr.det == ((forall|i: int, j: int| 0 <= i < n && 0 <= j < n && #[trigger] st.init@[i] && #[trigger] st.init@[j] ==> i == j)
        && (forall|i: int| 0 <= i < n ==> #[trigger] strict_blk(tr, i))));
    assert forall|k: int| 0 <= k < tr.evt@.len() implies {
        &&& #[trigger] tr.evt@[k] < ev.mode@.len()
        &&& ev.mode@[tr.evt@[k] as int] != NONE
        &&& tr.dst@[k] < n
    } by {
        // Math: dst[k] < n (dst_in)
        assert(tr.dst@[k] < st.p1@.len());
    }
}

/// A table of n entries, all ABSENT.
fn absent_table(n: usize) -> (v: Vec<usize>)
    ensures
        v@.len() == n,
        forall|i: int| 0 <= i < n ==> #[trigger] v@[i] == ABSENT,
{
    // Math: v = [ABSENT] * n (built by a loop: vec![x; n] is only specified through clone)
    let mut v: Vec<usize> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            v@.len() == i,
            // Math: |v| = i, all ABSENT
            forall|j: int| 0 <= j < i ==> #[trigger] v@[j] == ABSENT,
        decreases n - i,
    {
        // Math: v := v · [ABSENT]; i := i + 1
        v.push(ABSENT);
        i = i + 1;
    }
    v
}

/// The initial pairs a' < a (and a' == a, b' < b) are in the table.
pub open spec fn init_part(seen: &Seen, g1: &Aut, g2: &Aut, a: int, b: int) -> bool {
    // Math: ∀ initial (x, y) with x < a, or x = a ∧ y < b: key(x, y) ∈ table
    forall|x: int, y: int|
        0 <= x < g1.n && 0 <= y < g2.n && #[trigger] g1.init@[x] && #[trigger] g2.init@[y]
            && (x < a || (x == a && y < b)) ==> in_tab(seen, key(x, y, g2.n as int))
}

proof fn lemma_init_part_mono(seen0: &Seen, seen: &Seen, g1: &Aut, g2: &Aut, np: int, a: int, b: int)
    requires
        init_part(seen0, g1, g2, a, b),
        // Math: np = n1 · n2 ≤ 2^64 - 1; facts about the inputs, restated
        np == g1.n * g2.n,
        forall|x: int| 0 <= x < np && #[trigger] in_tab(seen0, x) ==> in_tab(seen, x),
    ensures
        init_part(seen, g1, g2, a, b),
{
    assert forall|x: int, y: int|
        0 <= x < g1.n && 0 <= y < g2.n && #[trigger] g1.init@[x] && #[trigger] g2.init@[y]
            && (x < a || (x == a && y < b)) implies in_tab(seen, key(x, y, g2.n as int)) by {
        // Math: key(x, y) < np
        lemma_key_range(x, y, g1.n as int, g2.n as int);
        // Math: it was in the old table, so it is in the new one
        assert(in_tab(seen0, key(x, y, g2.n as int)));
    }
}

/// The initial pairs X01 x X02, numbered first (states 0..n0 are exactly the initial ones).
fn init_pairs(g1: &Aut, g2: &Aut, ev: &Events, Ghost(np): Ghost<int>, force_hash: bool) -> (out: (Pairs, Seen))
    requires
        // Math: the inputs are ok (restated)
        inputs_ok(g1, g2, ev, np),
    ensures
        // Math: pairs_ok with n0 = n (all states so far are initial), the table matches, all initial pairs are in it
        pairs_ok(&out.0, g1, g2, out.0.p1@.len() as int),
        seen_ok(&out.1, &out.0, g2.n as int, np),
        init_in(&out.1, g1, g2),
{
    proof {
        // Math: basic input facts
        lemma_inputs_basic(g1, g2, ev, np);
    }
    // Math: n1, n2; pairs = n1 · n2 (fits in u64: inputs_ok)
    let n1 = g1.n;
    let n2 = g2.n;
    let pairs: u64 = (n1 as u64) * (n2 as u64);
    // Math: dense ↔ n1 · n2 ≤ 2^26 (unless the hash map is forced, for tests)
    let dense = pairs <= DENSE_MAX && !force_hash;
    // Math: tab = [ABSENT] * (n1 · n2) if dense, else []
    let tab = if dense {
        absent_table(pairs as usize)
    } else {
        Vec::new()
    };
    // Math: empty table (used = ∅), no states
    let mut seen = Seen { dense, tab, map: HashMapWithView::new(), used: Ghost(Set::empty()) };
    let mut st = Pairs { p1: Vec::new(), p2: Vec::new(), init: Vec::new(), marked: Vec::new() };
    proof {
        reveal(seen_ok);
        reveal(pairs_ok);
        // Math: seen_ok, pairs_ok hold for the empty start
        assert(seen_ok(&seen, &st, n2 as int, np));
        assert(pairs_ok(&st, g1, g2, 0));
    }
    // Math: a walks G1's states, b G2's: initial pairs in order (a, b)
    let mut a: usize = 0;
    while a < n1
        invariant
            // Math: np = n1 · n2 ≤ 2^64 - 1; facts about the inputs, restated
            np == g1.n * g2.n,
            np <= u64::MAX,
            n1 == g1.n,
            n2 == g2.n,
            g1.init@.len() == g1.n,
            g2.init@.len() == g2.n,
            g1.marked@.len() == g1.n,
            g2.marked@.len() == g2.n,
            // Math: a ≤ n1
            a <= n1,
            // Math: pairs_ok with n0 = n; the table matches
            pairs_ok(&st, g1, g2, st.p1@.len() as int),
            seen_ok(&seen, &st, n2 as int, np),
            // Math: the initial pairs (x, y) with x < a are in the table
            init_part(&seen, g1, g2, a as int, 0),
        // Math: n1 - a decreases
        decreases n1 - a,
    {
        // Math: a ∈ X01?
        if g1.init[a] {
            // Math: b = 0
            let mut b: usize = 0;
            while b < n2
                invariant
                    // Math: np = n1 · n2 ≤ 2^64 - 1; facts about the inputs, restated
                    np == g1.n * g2.n,
                    np <= u64::MAX,
                    n1 == g1.n,
                    n2 == g2.n,
                    g1.init@.len() == g1.n,
                    g2.init@.len() == g2.n,
                    g1.marked@.len() == g1.n,
                    g2.marked@.len() == g2.n,
                    a < n1,
                    // Math: a < n1, a ∈ X01, b ≤ n2
                    g1.init@[a as int],
                    b <= n2,
                    // Math: pairs_ok with n0 = n; the table matches
                    pairs_ok(&st, g1, g2, st.p1@.len() as int),
                    seen_ok(&seen, &st, n2 as int, np),
                    // Math: initial pairs before (a, b) are in the table
                    init_part(&seen, g1, g2, a as int, b as int),
                // Math: n2 - b decreases
                decreases n2 - b,
            {
                // Math: b ∈ X02? then add the state (a, b) (initial)
                if g2.init[b] {
                    // Math: ghost copies; n0 = n
                    let ghost seen0 = seen;
                    let ghost n0 = st.p1@.len() as int;
                    // Math: add (a, b) (new: initial pairs are added once)
                    let _ = find_or_add(&mut st, &mut seen, g1, g2, a, b, true, Ghost(np), Ghost(n0));
                    proof {
                        // Math: init_part still holds (keys only grow)
                        lemma_init_part_mono(&seen0, &seen, g1, g2, np, a as int, b as int);
                    }
                }
                // Math: b := b + 1
                b = b + 1;
            }
        }
        // Math: a := a + 1
        a = a + 1;
    }
    proof {
        reveal(init_in);
    }
    (st, seen)
}

/// The start of the search: no block written, the flag says "at most one initial state".
proof fn lemma_outer_start(
    tr: &Trans, st: &Pairs, seen: &Seen, g1: &Aut, g2: &Aut, ev: &Events, np: int, n0: int,
)
    requires
        pairs_ok(st, g1, g2, n0),
        seen_ok(seen, st, g2.n as int, np),
        init_in(seen, g1, g2),
        n0 == st.p1@.len(),
        // Math: start = [0], no transitions, det ↔ n0 ≤ 1
        tr.start@ == seq![0usize],
        tr.evt@.len() == 0,
        tr.dst@.len() == 0,
        tr.w1@.len() == 0,
        tr.w2@.len() == 0,
        tr.det == (n0 <= 1),
    ensures
        outer_ok(tr, st, seen, g1, g2, ev, np, n0, 0),
{
    // Why: open the opaque bundles used here.
    reveal(adj_le);
    reveal(outer_ok);
    reveal(tr_ok);
    reveal(done_ok);
    reveal(det_ok);
    reveal(all_strict);
    reveal(pairs_ok);
}

/// Forward search: block h is written while h is processed.
fn search(
    tr: &mut Trans,
    st: &mut Pairs,
    seen: &mut Seen,
    g1: &Aut,
    g2: &Aut,
    ev: &Events,
    Ghost(np): Ghost<int>,
    Ghost(n0): Ghost<int>,
)
    requires
        // Math: the inputs are ok (restated)
        inputs_ok(g1, g2, ev, np),
        // Math: np = n1 · n2 ≤ 2^64 - 1; facts about the inputs, restated
        np == g1.n * g2.n,
        // Math: outer_ok at h = 0
        outer_ok(old(tr), old(st), old(seen), g1, g2, ev, np, n0, 0),
    ensures
        // Math: outer_ok at h = n: every state's block is finished
        outer_ok(final(tr), final(st), final(seen), g1, g2, ev, np, n0, final(st).p1@.len() as int),
{
    // Math: h = 0: states 0 .. h-1 are expanded (their blocks finished); st works as the queue
    let mut h: usize = 0;
    while h < st.p1.len()
        invariant
            // Math: the inputs are ok (restated)
            inputs_ok(g1, g2, ev, np),
            // Math: np = n1 · n2 ≤ 2^64 - 1; facts about the inputs, restated
            np == g1.n * g2.n,
            // Math: outer_ok at h
            outer_ok(tr, st, seen, g1, g2, ev, np, n0, h as int),
        // Math: np - h decreases (n ≤ np: one key per state, lemma_len_bound)
        decreases np - h,
    {
        proof {
            reveal(outer_ok);
            // Math: n ≤ np, so h < np
            lemma_len_bound(seen, st, g2.n as int, np);
            // Math: cur_ok for block h, empty, prev = None
            lemma_outer_to_cur(tr, st, seen, g1, g2, ev, np, n0, h as int);
        }
        // Math: prev = None (block h has no event yet)
        let mut prev: Option<usize> = None;
        let ghost tr0 = *tr;
        // Math: emit the LEFT and BOTH moves of h
        walk_left(tr, st, seen, &mut prev, g1, g2, ev, Ghost(np), Ghost(n0), h);
        // Math: a1 = end of G1's block of p1[h]
        let ghost a1 = g1.start@[st.p1@[h as int] as int + 1] as int;
        // Math: emit the RIGHT moves of h
        walk_right(tr, st, seen, &mut prev, g1, g2, ev, Ghost(np), Ghost(n0), h, Ghost(a1));
        proof {
            // Math: every move of h is emitted: complete(h)
            lemma_cov_complete(tr, st, g1, g2, ev, h as int, tr0.start@[h as int] as int);
            reveal(outer_ok);
            // Math: n0 > 0 ∨ n = 0 (unchanged)
            assert(n0 > 0 || st.p1@.len() == 0) by {
                reveal(pairs_ok);
                reveal(cur_ok);
            }
        }
        // Why: ghost copies before this step.
        let ghost tr1 = *tr;
        // Math: start := start · [|evt|] (block h ends here)
        let t = tr.evt.len();
        tr.start.push(t);
        proof {
            // Math: outer_ok at h + 1
            lemma_cur_to_outer(&tr1, tr, st, seen, g1, g2, ev, np, n0, h as int, prev, t);
        }
        // Math: h := h + 1
        h = h + 1;
    }
    proof {
        reveal(outer_ok);
    }
}

proof fn lemma_inputs_establish(g1: &Aut, g2: &Aut, ev: &Events, np: int)
    requires
        // Math: both inputs ok; events ok; n1 · n2 ≤ 2^64 - 1
        aut_ok(g1, ev.m1 as int),
        aut_ok(g2, ev.map2@.len() as int),
        ev_ok(ev, ev.map2@.len() as int),
        // Math: np = n1 · n2 ≤ 2^64 - 1; facts about the inputs, restated
        np == g1.n * g2.n,
        np <= u64::MAX,
    ensures
        // Math: the inputs are ok (restated)
        inputs_ok(g1, g2, ev, np),
{
    // Math: start1, start2 sorted in pair form; then inputs_ok
    lemma_all_le(g1.start@, 0, g1.n + 1);
    lemma_all_le(g2.start@, 0, g2.n + 1);
    reveal(inputs_ok);
}

/// The reachable part of the composition of g1 and g2 by the modes of ev.
pub fn compose(g1: &Aut, g2: &Aut, ev: &Events, force_hash: bool) -> (out: (Pairs, Trans))
    requires
        // Math: both inputs ok; events ok; n1 · n2 ≤ 2^64 - 1
        aut_ok(g1, ev.m1 as int),
        aut_ok(g2, ev.map2@.len() as int),
        ev_ok(ev, ev.map2@.len() as int),
        g1.n * g2.n <= u64::MAX,
    ensures
        // Math: composition_ok: the output is the reachable composition (positions form)
        composition_ok(g1, g2, ev, &out.0, &out.1),
{
    // Math: np = n1 · n2
    let ghost np: int = g1.n * g2.n;
    proof {
        // Math: inputs_ok
        lemma_inputs_establish(g1, g2, ev, np);
    }
    // Math: the initial pairs X01 × X02 first
    let (mut st, mut seen) = init_pairs(g1, g2, ev, Ghost(np), force_hash);
    // Math: n0 = |X01 × X02|
    let ghost n0: int = st.p1@.len() as int;
    // Math: no transitions; det = (n0 ≤ 1)
    let mut tr = Trans {
        start: Vec::new(),
        evt: Vec::new(),
        dst: Vec::new(),
        det: st.p1.len() <= 1,
        w1: Ghost(Seq::empty()),
        w2: Ghost(Seq::empty()),
    };
    // Math: start = [0]
    tr.start.push(0);
    proof {
        // Math: outer_ok at h = 0
        lemma_outer_start(&tr, &st, &seen, g1, g2, ev, np, n0);
    }
    // Math: the search: outer_ok at h = n
    search(&mut tr, &mut st, &mut seen, g1, g2, ev, Ghost(np), Ghost(n0));
    proof {
        // Math: composition_ok
        lemma_final(&tr, &st, &seen, g1, g2, ev, np, n0);
    }
    (st, tr)
}

} // verus!
