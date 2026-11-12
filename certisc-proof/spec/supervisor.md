# Spec: supervisory control (part 1: prefix-closed)

Status: **implemented 2026-11-11** (questions answered by the user 2026-11-10, §8). What was
built differs from the draft §2–§3 in one design choice; see **§9** first.

One public call, `supervisor(G, H, ...)`, with options added part by part:
1. prefix-closed (this spec);
2. nonblocking (later: adds coaccessibility to the fixed point);
3. partial observation (later).

## 1. Definitions (math)

Plant `G`, specification `H`: valid, **deterministic** automata (Q2). `Euc` = the plant's
uncontrollable events. Languages over strings of events.

- Legal language: `K = L(G) ∩ L(H)` (prefix-closed, since both are). (Q1 fixes how events of
  `G` that `H` does not mention are treated.)
- `K` is **controllable** (w.r.t. `L(G)`, `Euc`): `K·Euc ∩ L(G) ⊆ K`. In words: no string of
  `K` can be pushed out of `K` by an uncontrollable event that the plant can do.
- `K↑C`: the **supremal controllable sublanguage** of `K` (the union of all controllable
  sublanguages of `K`; it is controllable and prefix-closed). For prefix-closed `K`:

      K↑C = { s ∈ K | ∀ u ∈ Euc*:  s·u ∈ L(G)  →  s·u ∈ K }

- The supervisor is an automaton `S` with `L(S) = K↑C`; under it the closed loop is
  `L(S/G) = L(S) ∩ L(G) = K↑C`.

## 2. The algorithm (state level)

**Refinement** (makes the spec a strict subautomaton of the plant):
1. `Hc` = `H` completed over `E_G` with one extra **dump** state `d`: for `e ∈ E_G \ E_H`, a
   self-loop at every state (Q1: the spec does not constrain it); for `e ∈ E_G ∩ E_H` where
   `H` has no `e`-transition, `x --e--> d`; `d` loops on every `e ∈ E_G`.
2. `P = G × Hc` (the verified product). Since `Hc` never blocks a `G` event, `L(P) = L(G)`
   and `P` is deterministic: `P` is `G` refined (state-split).
3. Inside states `I = {(g, h) | h ≠ d}`; outside `O = {(g, d)}`. `L(P restricted to I) = K`:
   `H' = P` minus `O` is a strict subautomaton of `P` (a copy with fewer states).

**Bad states** (the user's linear backward propagation): a state is bad if an uncontrollable
string leads from it to `O`:

    Bad = coreach over the Euc-transitions of P, from O         (O ⊆ Bad)

This is exactly the queue-based reverse traversal: start with `O` (equivalently `X_bad,0` plus
`O`), follow incoming uncontrollable transitions backwards, mark each state once.

**Supervisor**: `S = Ac(P without Bad)` (delete `Bad`, keep the accessible part). If the initial
state is bad, `K↑C = ∅` and `S` is the empty automaton (`EmptyAutomatonWarning`, as delete).

Cost: `P` has at most `|X_G|·(|X_H|+1)` states; every step after building `P` is linear in
`|P|` (states + transitions): one reverse index, one backward search, one deletion, one forward
search. This is the "fast" implementation. The "naive" one (repeat: delete states with a
disabled uncontrollable event, take `Ac`, until nothing changes) is quadratic in `|G × H|`.

## 3. What is proved, and where

Every step is a verified building block with a view-level contract; one new Lean theorem links
them to `K↑C`.

| step | Rust (Verus) | contract | new? |
|---|---|---|---|
| `Hc` | `complete(h, eG)` | `IsCompletion`: `h`'s states and moves kept; the dump state `d = n`; self-loops on `E_G \ E_H`; every other `(x, e)` with `e ∈ E_G ∩ E_H` goes to `d`; `d` loops on `E_G` | new |
| `P` | `compose_aut` (prod) | `IsComposition(prodMode, G, Hc, P, φ)` | exists |
| uc part | `keep_events(p, Euc)` | same states, `delta' = {(x, e, y) ∈ delta | e ∈ Euc}` | new |
| `Bad` | `coreachable` | `coreach(O)` in the uc part | exists |
| delete | `delete_states` | `IsDeletion(P, Bad, ...)` | exists |
| `S` | `accessible` | `IsDeletion` of the states outside `Ac` | exists |

New Lean (`DESopsProof/Supervisor.lean`):
- `Controllable K LG Euc`, `supC K LG Euc` (as the union of controllable sublanguages),
  and `supC_prefix_closed`: the formula of §1 for prefix-closed `K`.
- `IsCompletion` and `L (complete H) ⊇ L(H)`, with `L(G × Hc) = L(G)` and the inside part's
  language `= K`.
- **Main theorem** `supcon_strict_sub`: if `P` is deterministic, `I` is a set of states with
  `L(P|I) = K ⊆ L(P)`, `Bad = coreach_{Euc}(X_P \ I)`, and `S = Ac(P \ Bad)`, then
  `L(S) = supC K L(P) Euc`.

Trusted: the Python glue (event names, `Euc` flags as passed, state names), as for the other
operations. Not verified at all: `method="naive"` (Q3), a plain Python iteration over `G × H`, kept
as an alternative and as the tests' oracle.

## 4. Public API (proposal)

    supervisor(G, H, *, mode="prefix_closed", method="fast", backend="rust") -> ValidAutomaton

- `G`, `H`: `Automaton` or `ValidAutomaton`; raises `ValueError` if either is not
  deterministic (Q2) or if the two disagree on a shared event's controllability /
  observability (the verified `check_agree`).
- Result: `S` with `L(S) = K↑C`; state names `(g_name, h_name)` (tuples, as `parallel_2aut`).
  Its events are `E_G ∪ E_H`; `Euc`, `Euo` the unions.
- Later modes: `"nonblocking"`, partial observation (option names decided then).

## 5. Tests

- Against the naive iteration on `G × H` (Python, unverified oracle): same language, on random
  pairs (including specs that mention fewer events than the plant, and nondeterministic inputs
  rejected).
- Against the language formula of §1, word by word up to a length bound: `L(S) = K↑C`.
- Textbook examples (Cassandras–Lafortune, the machine/buffer models in
  `Examples/v2/testing/models/`), compared with legacy `DESops`'
  `supremal_sublanguage` by language, once, by hand (certisc tests never import legacy).

## 6. Example

`Examples/v2/testing/certisc/10_supervisor.py`: plant `M1 ‖ M2`, spec the buffer `B2`.

## 7. Order of work (after review)

1. Lean: controllability, `supC`, the prefix-closed formula, `supcon_strict_sub`.
2. Verus: `complete`, `keep_events`; reuse the rest.
3. Python: `supervisor` in `ops_aut` (a new `sup` package later, as planned in CLAUDE.md, when the
   other modes come), naive oracle in the tests, tests, example, log.

## 8. Questions for review

- **Q1. Events of `G` that `H` does not mention** (`E_G \ E_H`). (a) The spec forbids them:
  `K = L(G) ∩ L(H)` with `H` over its own alphabet (product); an uncontrollable event outside
  `E_H` makes its states bad. (b) The spec does not constrain them: `K = L(G) ∩ P_H⁻¹ L(H)`
  (parallel; `H` self-loops them). Proposal: (b), since specs usually describe only the events
  they are about (B2 mentions 3 of the plant's 8 events); (a) is then the special case
  `E_H = E_G`. Only step 1 of §2 changes: under (b), `Hc` self-loops the events of
  `E_G \ E_H` at every state and sends only the missing `E_H` events to `d`.
  **Answered (user, 2026-11-10): (b), unconstrained.** §2 step 1 uses the self-loop form.
- **Q2. Determinism.** Require deterministic `G` and `H` (raise `ValueError` otherwise), or
  determinize `H` first (subset construction, a new verified operation)? Proposal: require it
  now; determinize later if needed.
  **Answered (user, 2026-11-10): require it.**
- **Q3. Which implementations.** The fast one (§2) is the verified `supervisor`. The naive one:
  (a) only as a test oracle and benchmark, in the tests; (b) also public, `method="naive"`.
  Proposal: (a).
  **Answered (user, 2026-11-10): (b), also public** as `method="naive"`, documented as
  unverified (Python over `G × H`); `method="fast"` (verified) is the default. The tests still
  compare the two.
- **Q4. Where it lives.** In `ops_aut/basic_ops.py` now, or a new package `sup/` (CLAUDE.md
  plans one) from the start? Proposal: `sup/` from the start, since three modes are coming.
  **Answered (user, 2026-11-10): `sup/`** (`src/sup/`, added to `python-packages`).

## 9. As implemented (2026-11-11)

Done with the user away ("proceed with implementation based on your recommended actions").

**One change from §2–§3: no completion of `H`.** Verifying `complete` in Verus means proving a
block merge (H's transitions interleaved with the added ones, kept sorted), the costliest kind
of builder proof. The implementation works on `P0 = G ‖ H` directly (the verified parallel
composition) and detects the plant's moves that `P0` lacks, at the pair's plant state:

    Bad0 = { x | ∃ e ∈ Euc: e is enabled in G at p1[x], and not in P0 at x }   (an "escape")
    Bad  = coreach over the uncontrollable transitions of P0, from Bad0
    S    = Ac(P0 without Bad)

This is the user's linear propagation exactly (Bad0 is `X_bad,0`). It requires `E_H ⊆ E_G`
(else `G ‖ H` would let `H` move alone); `supervisor` raises `ValueError` otherwise. Under
Q1 (b), `H` does not constrain the plant's other events, which is what `‖` does.

**Lean** (`DESopsProof/Supervisor.lean`, no `sorry`, standard axioms only):
- `PrefixClosed`, `Controllable`, `supC` (union of prefix-closed controllable sublanguages),
  `supC_le`, `le_supC`, `supC_prefixClosed`, `supC_controllable`, `controllable_iter`;
- `supcon_strict_sub`: the refinement form of §2 (strict subautomaton `I`, `Bad` =
  coreach_uc of `X \ I`), and `supervisor_L` for the two deletions; plus `supC_empty`;
- `supcon_escape`: the escape form, `L(P0|¬Bad) = L(P0)↑C` w.r.t. a prefix-closed plant
  language `Lp` with `L(P0) ⊆ Lp` and `hen` (after `s ∈ L(P0)` reaching `x`:
  `s e ∈ Lp ↔ en(x, e)`); `supervisor_escape_L` for the automata the library builds;
- `IsDeletion.L_eq`, `gen_restrict_reach`, `IsDeletion.L_accessible`: languages of deletions.

**Verus** (`certisc-lib/rust/verified/src/sup/supcon.rs`; crate 180 verified, 0 errors):
`enabled` (binary search), `bad0` (`r[i] ↔ i ∈ esc_set`), `keep_events` (builder: valid, and
`y ∈ f_H(x, e) ↔ y ∈ f_G(x, e) ∧ keep[e]`), `in_flags`, and `supervisor_pc`, the whole chain,
whose contract is the list of hypotheses of `supervisor_escape_L` (`D1 = coreach(uc_part(P0),
esc_set)`, the two `is_deletion`s, `old = old1 ∘ old2`).

**Not yet proved (deferred):** the link from `G ‖ H` to `supervisor_escape_L`'s plant
hypotheses: `Lp = L(G)`, `L(P0) = L(G) ∩ P_H⁻¹ L(H) ⊆ Lp` (from `par_L`, with `E_H ⊆ E_G`),
and `hen` (from `IsComposition`'s step facts and `G` deterministic). These are statements about
the verified composition, and are checked by the tests meanwhile. Also the hand check of the
Rust views against the Lean definitions (as for the other operations).

**Python** (`src/sup/`): `supervisor(G, H, mode="prefix_closed", method="fast",
backend="rust")`; `method="naive"` is the textbook iteration in plain Python (Q3). Other modes
raise `NotImplementedError`. Tests: `tests/sup/test_supervisor.py` (fast = naive on 1900 random
pairs, the K↑C properties word by word, the small factory, errors, empty results).

## 10. The refinement and subautomaton constructions (2026-11-11)

User (2026-11-11): keep the escape routine, implement `complete(H)`, and offer both strict-
subautomaton options, each with `method="fast"` and `method="naive"`. Public parameter
`construction` ("escape" default, "refine", "subautomaton"); all three give the same
automaton (tested).

**Verus** (crate 180 -> **204 verified, 0 errors**, two runs, no trigger notes in `sup/`):
- `sup/complete.rs`: `complete(h, extra, euc_x, euo_x)`: valid, `n + 1` states, `m_H + extra`
  events (H's flags, then the extra events in E with the given flags), H's initial and marked
  states (the dump state neither), and `y ∈ f_Hc(x, e) ↔ comp(h, m, x, e, y)`: H's moves on
  `E_H`, `x --e--> d` when H has none, self-loops on the extra events, `d` loops on every
  event. Built block by block (`build_block` walks the events in order with a pointer into H's
  sorted block; `build_dump`); a mutation check (the missing-event move sent to `x` instead of
  `d`) was rejected by Verus.
- `sup/supcon.rs`: the common tail `sup_tail(p, s0)` (contract `tail_ok`: deleted set =
  `coreach(uc_part(P), set_of(s0))`, the two `is_deletion`s, `old`), now used by
  `supervisor_pc` (escape) and the new `supervisor_sub(p, inside)` (refinement form: start set
  `X \ I`; the deletion hypotheses of Lean `supervisor_L`); `not_label(p2, d)` (inside = the
  Hc label is not `d`); `same_aut(a, b)` (`r → a@ = b@`).

**Python** (`sup/supervisor.py`, trusted glue):
- "refine": `Hc = complete(H, the G events H does not mention, with G's flags)`, then
  `P = G × Hc` (verified `compose`, product, in G's event numbering; the verified agreement
  check), then `supervisor_sub` with I = the states whose Hc label is not `d`.
- "subautomaton": H's states are matched to G's by name, H is re-encoded in G's event
  numbering with its states in G's order (trusted), and the verified check `restricts` (verified
  `delete_states` of G, then `same_aut`) must accept it: H is exactly G with the other states
  deleted; then `supervisor_sub` on G. A wrong match or re-encoding can only make the check
  fail (ValueError), never give a wrong supervisor.
- naive: the same textbook iteration for all three (on G ‖ H with escapes, on G × Hc with the
  dump states outside, on G with H's states inside; the last checks H against G by names).

**Measured** (line plant of the §9 benchmark, fast): n = 16 000: escape 4.6 ms, refine 5.4 ms,
subautomaton 29.5 ms; n = 64 000: 18.9 / 24.5 / 131 ms (subautomaton: mostly the Python
re-encoding of H). A first run took 10 s / 147 s for subautomaton: `ValidAutomaton.init` and
`.marked` build a new set at each access, and the glue read them once per state (fixed: read
once).

**Lean:** the refinement form is `supcon_strict_sub` / `supervisor_L` (§9). Still to prove for
"refine": `L(G × Hc) = L(G)` and `L((G × Hc)|I) = L(G) ∩ P_H⁻¹ L(H)` (completion lemmas, from
`comp` and `prod_L`); for "subautomaton": `L(H) = L(G|I)` is `IsDeletion.L_eq` (proved),
given that `same_aut` makes H equal to the verified deletion.

**Update 2026-11-11 (later): faster subautomaton glue.** The Python re-encoding of H is gone.
If H already has G's event table and its states in G's order (as from `delete_states(G, ...)`),
H's Rust copy goes to `restricts` as is; otherwise the binding re-encodes it in Rust
(`reencode`, trusted: events renumbered, states reordered, blocks re-sorted) and
`restricts_mapped` compares it with the verified deletion. Either way a wrong re-encoding can
only make the check fail. Name matching uses C-level built-ins (one dict, `map`).
Measured on the same strict subautomaton H = G minus its last state (best of 3):

| n | subautomaton (H in G's order) | subautomaton (re-encoded) | escape | refine |
|---|---|---|---|---|
| 64 000 | 18 ms | 23 ms | 20 ms | 32 ms |
| 1 000 000 | 502 ms | 536 ms | 394 ms | 613 ms |

(Before: 131 ms and 3.4 s for subautomaton.) At 1M about 200 ms is still name matching in
Python; the Rust part (check + supervisor) is about 130 ms.

**Update 2026-11-11 (later): H as state indices.** For `construction="subautomaton"`, H may also
be the indices of the states of G to keep (any iterable of ints). The specification is then G
restricted to them by definition: no names to match and nothing to check; `inside` goes
straight to the verified `supervisor_sub` (Lean `supervisor_L`; `L(G|I)` is the specification
language). Result names are built with `map`/`zip` for every construction. Measured (best of
3, line plant; this run's machine timings were about 1.5× the previous run's for the same
calls):

| n | indices | (Rust alone) | H automaton | escape | refine |
|---|---|---|---|---|---|
| 64 000 | 15 ms | 5 ms | 22 ms | 22 ms | 34 ms |
| 1 000 000 | 274 ms | 102 ms | 750 ms | 463 ms | 906 ms |

**Update 2026-11-11 (later): forbidden states.** User: a further strict-subautomaton case, where
the states to delete are given instead of H. `supervisor(G, forbidden=[...])` (H omitted): the
specification is G without those states, i.e. the index form of "subautomaton" with
`inside[x] = x ∉ forbidden` (same verified `supervisor_sub`, Lean `supervisor_L`). H is now
optional; H together with `forbidden`, neither of them, or `forbidden` with a construction
other than "subautomaton" raise ValueError. Works with both methods.
