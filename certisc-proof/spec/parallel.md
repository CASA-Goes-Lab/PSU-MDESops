# Spec: parallel composition and product

Status: **draft 2026-10-29, fresh start; reviewed by the user 2026-10-29** (answers in §9).
Nothing implemented yet.
This replaces the draft of 2026-10-20 (in git history, `git show HEAD:certisc-proof/spec/parallel.md`).
That draft predates `ValidAutomaton`, the per-automaton event numbering, and the
"trusted builder + verified checker" pattern (indices, `delete_states`); see "What changed".

## 1. Definitions (math)

Inputs: two valid automata `G1 = (X1, E1, Euc1, Euo1, f1, X01, Xm1)` and `G2 = (X2, ...)`.

Both operations run on pairs of states and differ only in what an event does. Per event `e`, a
**mode**:

| mode | `f((x1, x2), e)` | parallel `‖` | product `×` |
|---|---|---|---|
| `both` | `f1(x1, e) × f2(x2, e)` | `e ∈ E1 ∩ E2` | `e ∈ E1 ∩ E2` |
| `left` | `f1(x1, e) × {x2}` | `e ∈ E1 \ E2` | never |
| `right` | `{x1} × f2(x2, e)` | `e ∈ E2 \ E1` | never |
| `none` | `∅` | otherwise | otherwise |

Common to both:

| part | definition |
|---|---|
| initial | `X01 × X02` |
| marked | `(x1, x2)` marked ⟺ `x1 ∈ Xm1` and `x2 ∈ Xm2` |
| states kept | only the pairs **reachable** from `X01 × X02` (the builder searches forward) |
| `Euc`, `Euo` | unions of the inputs' sets, restricted to the output's events |

Output events: `E1 ∪ E2` for both (question 2: union). In the product, private events stay in
the alphabet but are never enabled (mode `none`).

Languages (projection `Pi` erases events outside `Ei`):

    L(G1 ‖ G2) = P1⁻¹ L(G1) ∩ P2⁻¹ L(G2)  over (E1 ∪ E2)*,   same for Lm
    L(G1 × G2) = L(G1) ∩ L(G2),                               same for Lm

## 2. Lean

**Done 2026-10-29** (`lake build` passes, no `sorry`; the results use only `propext`,
`Classical.choice`, `Quot.sound`). As built: `Mode`, `syncF`, `comp`, `parMode`, `prodMode`,
`parF_eq_syncF`, `par_eq_comp`, `prod`, `run_prodF`, `mem_prod_L`, `mem_prod_Lm`, `prod_det`;
`IsComposition` (fields `step_sound`, `step_complete`, `init_sound`, `init_complete`, `marked`,
`E`, `Euc`, `Euo`) with `image_f`, `image_X0`, `L`, `Lm`, `det`, `par_L`, `par_Lm`, `prod_L`,
`prod_Lm`, `par_det`, `prod_det`. Per-mode membership lemmas for the hand check:
`mem_syncF_both`, `mem_syncF_left`, `mem_syncF_right`, `syncF_none`. The old `output` section
(tied to the 2026-10-20 Nagini plan) was replaced by `IsComposition`; `H` is now any
`Automaton` (W1–W3 come from the validity pass).

Plan as drafted:

`DESopsProof/Parallel.lean` (2026-10-20) already proves the parallel case: `parF`, `par`,
`mem_par_L`, `mem_par_Lm`, `par_det`, and the generic bridge (`gen_eq_of_labels`,
`mkd_eq_of_labels`, `det_of_labels`, `output`). The math has not changed; the plan is to keep
it and generalize:

- **(L1) by modes:** `syncF mode f1 f2`, with `parF` and a new `prodF` as two choices of `mode`.
  `par` and `prod` are transition systems over `Fin n1 × Fin n2`.
- **(L2) languages:** `mem_par_L`/`Lm` (exist); new `mem_prod_L`/`Lm`
  (`s ∈ L(G1 × G2) ⟺ s ∈ L(G1) ∧ s ∈ L(G2)`; the run is the pair of runs, no projection).
- **(L3) bridge (exists):** if `φ(X0H) = X0`, `φ(fH(i, e)) = f(φ(i), e)` and `mH(i) = m(φ(i))`,
  then `L(H) = L(T)` and `Lm(H) = Lm(T)`. Needs neither injectivity of `φ` nor reachability.
- **(L4) the checker's facts give (L3)'s hypotheses.** A new statement in the form Nagini checks
  (witness arrays, below), as `IsDeletion` was for `delete_states`: `IsComposition`.
- **(L5) determinism (exists, `det_of_labels`):** needs `φ` injective. See question 4.

Event identity: Lean has one alphabet `α`; the two inputs share it. The Python side has one
event numbering per automaton, so the mapping between numberings is part of the trusted
boundary (§4, question 3).

## 3. Python: mechanism

**Decision (user, 2026-10-29): a verified search, not a checker.** The forward search over pairs is
itself the verified code: at each new state, the transitions it adds are proved good (loop
invariants), and the lists it writes are already the grouped encoding (block `i` is written while
`i` is processed). The Lean target is unchanged (`IsComposition`). Reasons: no extra checking
pass at runtime (in delete the check costs about 3.5× the build); the lessons of `reach.py` (a
verified search that writes its output, 20 s) address what timed out on 2026-10-20 (re-proving
the facts about earlier entries after each append). If the in-search proofs fail, we look at the
options then (the user: "not going with the checker yet").

Plan:
1. **Experiment first:** the predicate "every transition so far is a correct move" and the
   methods that append one state and one transition while keeping it (the step that timed out on
   2026-10-20). Measure.
2. If it verifies quickly: the full search (initial pairs, one method per output state, the
   pair lookup, completeness per finished state).
3. Pair lookup (proposal, to confirm): a trusted dict `(x1, x2) → i`; a "found j" answer is
   checked in the verified code (`p1[j] = x1`, `p2[j] = x2`); a wrong "new" answer can only add
   a duplicate state (languages still right, `IsComposition` needs no distinct labels). A
   bound of `n1·n2` new states gives termination.

The table and lists below are from the draft (a trusted builder + checker); the lists
(`p1`, `p2`, `src1`, `src2`, completeness witnesses) carry over as the search's outputs.


Same pattern as `delete_states`: trusted code builds, verified code checks, the result is
returned only if the check passes.

| step | where | trusted / verified |
|---|---|---|
| events: output table, maps `m1`, `m2` (input number → output number), modes | `ops_aut/basic_ops.py` | trusted (by names) |
| agreement of `Euc`/`Euo` on shared events (reject if not) | checker | verified (question 1) |
| build: forward search over pairs, dict `(x1, x2) → i` | `core_aut/trusted/compose.py` | trusted |
| check: the output is exactly the reachable composition | `ops_aut/verified_ops/compose.py` | verified |
| validity of the output | `validate_encoded` (as delete) | verified (the extra pass; see §6) |
| names: `(name1, name2)` pairs | wrapper | trusted |

No fuel bound and no pigeonhole argument are needed any more: the search is trusted code; only
its finished output is checked.

### Builder output (lists)

| array | size | meaning |
|---|---|---|
| `p1`, `p2` | n | output state `i` is the pair `(p1[i], p2[i])` (the label `φ(i)`) |
| `start`, `evt`, `dst` | n+1, T, T | the output's transition blocks (output event numbers) |
| `init`, `marked` | n | flags |
| `src1`, `src2` | T | witness: the input transitions that output transition `k` uses (`-1`: that side stays) |
| completeness witnesses | see §4 | question 5 |

## 4. Verified checker: facts

`φ(i) = (p1[i], p2[i])`, `mode[e]`, `m1`, `m2` as above.

| fact | math | gives |
|---|---|---|
| labels in range | `p1[i] ∈ X1`, `p2[i] ∈ X2` | |
| events | `m1`, `m2` injective, into `[0, m)`; `mode[e]` matches the definition of §1 for `‖` or `×` | the mode table is the right one |
| agreement | for `e` shared: `in_Euc1[e1] = in_Euc2[e2]`, same for `Euo` | question 1 |
| initial, sound | `init[i] → p1[i] ∈ X01 ∧ p2[i] ∈ X02` | `φ(X0H) ⊆ X01 × X02` |
| initial, complete | every `(x1, x2) ∈ X01 × X02` has an initial `i` with `φ(i) = (x1, x2)` (witness) | `⊇` |
| marked | `marked[i] ⟺ marked1[p1[i]] ∧ marked2[p2[i]]` (two implications, as the delete flags) | `mH = m ∘ φ` |
| step, sound | for `k` in block `i`: by `mode[evt[k]]`, `src1[k]` / `src2[k]` are transitions out of `p1[i]` / `p2[i]` on that event (or `-1` and that side stays), and `φ(dst[k])` is their targets | `φ(fH(i, e)) ⊆ f(φ(i), e)` |
| step, complete | every move of `φ(i)` (§1 table) is some output transition of `i` | `⊇` (question 5) |

With these, (L4) gives (L3)'s hypotheses, so `L(H) = L(G1 ‖ G2)` and `Lm(H) = Lm(G1 ‖ G2)`
(same for `×`).

**Reachability** of every output state is not in the table: the languages don't need it (L3),
and the builder only creates reached pairs (question 6: not checked; confirmed empirically in
tests later).

## 5. Completeness: the hard part

The 2026-10-20 attempt proved soundness (65 s) but the completeness walk timed out. Two
options, to prototype and pick by verification time:

- **(a) canonical order:** the builder writes block `i` in a fixed order (by output event; for a
  `both` event, pairs `(k1, k2)` in order of `k1` then `k2`). The checker walks the input blocks
  of `p1[i]`, `p2[i]` and the output block together. One pass, no extra arrays. Risk: the walk is
  what timed out before; and the order needs both input blocks sorted the same way as the output
  numbering (true for `m1` if output numbers extend G1's in order, not in general for `m2`).
- **(b) witness arrays** (as `pos2` in delete, which verified quickly): for each output state
  `i` and each input transition the move uses, the position of the output transition. For a
  `left`/`right` event it is one array indexed by `(i, k1)`; for `both` events, by `(i, k1, k2)`
  with `k1`, `k2` on the same event, offsets per output state. Sizes are linear in the output.
  Risk: the offsets for `both` pairs need per-event sub-blocks of the inputs (the active-event
  index has the event ranges).

Decision (question 5): (b), because the patterns are already verified (`keep_ok` + `pos2_ok` in
`delete.py`).

## 6. Cost (to measure)

Same structure as delete: builder + exactness check + validity pass. The validity pass is the
largest cost in delete; the deferred plan (spec `delete_states.md`, "Planned (deferred)") applies
here too, and is recorded as a priority once the tool is more complete.

## 7. Public API (proposal)

    parallel_2aut(G1, G2) -> ValidAutomaton
    product_2aut(G1, G2)  -> ValidAutomaton

(Names, question 7: two inputs, named so; a general version for several automata later.
`product_2aut` follows the same naming, assumed.)

- `G1`, `G2`: `Automaton` or `ValidAutomaton` (plain ones validated first, as now).
- State names: `(name1, name2)`.
- Empty result (no initial pair; only if an input has no states): the empty automaton with
  `EmptyAutomatonWarning`, as delete.
- Several automata: later (question 7).
- DFA in ⇒ DFA out: decided by the validity pass (question 4).

## 8. What changed from the 2026-10-20 draft

| old | new |
|---|---|
| verified core doing the search, with fuel | trusted builder + verified checker |
| N5 distinct pairs proved in the core (key `x1·n2 + x2`) | not needed for languages; question 4 |
| one shared event table built from both automata | each `ValidAutomaton` has its own numbering; maps `m1`, `m2` |
| parallel only | parallel and product, one checker by modes |
| `parallel.py`, `parallel_check.py` in `verified_ops/` | new files; old ones: question 8 |

## 9. Questions for review

1. **Agreement:** a shared event controllable in one input and uncontrollable in the other (or
   observable / unobservable). Old decision: reject with `InvalidAutomatonError`. Keep?
   (Alternative: union, i.e. uncontrollable if uncontrollable in either.)
   **Answered (user, 2026-10-29): reject.**
2. **Product events:** `E1 ∩ E2` (the textbook: the product only knows common events) or
   `E1 ∪ E2` (private events kept in the alphabet, never enabled)? Proposal: `E1 ∩ E2`.
   **Answered (user, 2026-10-29): union, `E1 ∪ E2`.**
3. **Event mapping:** trusted by names (`m1`, `m2` built from the two event tables by Python
   `==`/hash), as the encoding already is. The checker verifies only what follows from the maps
   (injective, modes consistent). OK?
   **Answered (user, 2026-10-29): yes.**
4. **DFA in ⇒ DFA out:** (a) prove it: check that the labels `φ(i)` are distinct (an array over
   all `n1·n2` pairs is too large, so this needs another witness, e.g. a sorted copy), then
   `det_of_labels`; or (b) let the validity pass decide whether the output is deterministic (it
   already checks determinism; no new proof). Proposal: (b).
   **Answered (user, 2026-10-29): (b) for now. The user notes that scalability will likely need
   (a): add to the deferred priorities (with deletion keeps validity, `delete_states.md`).**
5. **Completeness:** option (b) witness arrays (proposal) or (a) canonical order?
   **Answered (user, 2026-10-29): (b).**
6. **Reachability:** not checked (proposal), or checked (the reach certificate on the output)?
   **Answered (user, 2026-10-29): not checked; true by construction. Check empirically later
   to confirm.**
7. **Several automata:** `parallel(G1, ..., Gk)` as a left fold of the pair version (names
   become nested pairs), or only two inputs for now? Proposal: two for now.
   **Answered (user, 2026-10-29): two for now, as `parallel_2aut`; generalize later.**
8. **Old files** (`verified_ops/parallel.py`, `parallel_check.py`, `doc/wip/parallel/`): delete
   once the new version works, or keep as reference? (`Parallel.lean` is kept and extended.)
   **Answered (user, 2026-10-29): delete** (when the new version replaces them).

## 10. Order of work (after review)

1. Lean: `syncF` by modes, `prod`, `mem_prod_L`/`Lm`, `IsComposition` and its link to the bridge.
2. Nagini: checker facts one method each (lesson from delete), completeness last; run the full
   file twice.
3. Trusted builder, public `parallel` / `product`, tests (against a direct construction; every
   single-entry mutation of the builder's output rejected; languages on random pairs).
4. Speed measurements (builder, check, validity pass); log.
