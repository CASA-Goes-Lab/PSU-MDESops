# Spec: parallel composition

Status: **draft 2026-10-20, for review.** Lean side (§3–§4) **proved** 2026-10-20 (`DESopsProof/Parallel.lean`). Nagini side: see §5. Builds on [automaton.md](automaton.md) (definitions, §3–§4)
and [wrapper.md](wrapper.md) (encoding, verified checker). Code: `certisc-lib/src/ops_aut/verified_ops/parallel.py`.

## 1. Decisions

| # | Question | Decision |
|---|---|---|
| 1 | A shared event is controllable in one input and uncontrollable in the other (or observable in one, unobservable in the other) | **Reject**: `InvalidAutomatonError`. The check is verified (§5, N0). |
| 2 | Lean state type | `run`, `gen`, `mkd`, `reach` are generalized from `Fin n` to any state type `σ` with `DecidableEq`. `Automaton` keeps `Fin n`. The product's states are pairs `Fin n1 × Fin n2`. |
| 3 | Division of work | Nagini proves **local** facts about each output state (§5). Lean proves the product's languages (§3) and a generic bridge from local facts to languages (§4). |
| 4 | DFA in ⇒ DFA out | **Required** (user, 2026-10-20). Needs distinct pairs: N5 in Nagini, L5 in Lean. |
| 5 | Where N2a/N2b are proved | **Proposed (Claude, 2026-10-20), for review:** by a verified *checker* run on the core's output, not inside the core (§5a). |

## 2. Definition

Inputs: `G1 = (n1, E1, Euc1, Euo1, f1, X01, Xm1)` and `G2 = (n2, …)`, both well formed (W1–W3).

**Agreement:** for every `e ∈ E1 ∩ E2`, `e ∈ Euc1 ⟺ e ∈ Euc2` and `e ∈ Euo1 ⟺ e ∈ Euo2`.
Composition is defined only for agreeing inputs (decision 1).

**Product** `G1 ‖ G2`, over the states `X1 × X2` (pairs):

| Part | Definition |
|---|---|
| events | `E = E1 ∪ E2`, `Euc = Euc1 ∪ Euc2`, `Euo = Euo1 ∪ Euo2` |
| transitions | `f∥((x1, x2), e)` = see below |
| initial | `X0 = X01 × X02` |
| marked | `(x1, x2)` marked ⟺ `x1 ∈ Xm1` and `x2 ∈ Xm2` |

    f∥((x1, x2), e) = f1(x1, e) × f2(x2, e)     if e ∈ E1 ∩ E2   (both move)
                    = f1(x1, e) × {x2}          if e ∈ E1 \ E2   (G1 alone)
                    = {x1} × f2(x2, e)          if e ∈ E2 \ E1   (G2 alone)
                    = ∅                         otherwise

A shared event blocks wherever one side can't execute it (`f1(x1, e) = ∅` gives `∅`), including
events in `E1` that label no transition of `G1` (automaton.md §3).

## 3. Lean: the product and its languages

New module `DESopsProof/Parallel.lean`.

- **(L0) Refactor:** `step`, `run`, `gen`, `mkd`, `reach` and their lemmas work for any `σ` (decision 2).
  A *transition system* `TS σ α` is `(f : σ → α → Finset σ, X0 : Finset σ, marked : σ → Bool)`,
  without well-formedness. An `Automaton` gives one with `σ = Fin n`.
- **(L1) Definition:** `par G1 G2 : TS (Fin G1.n × Fin G2.n) α`, as in §2.
- **(L2) Languages.** With `P_i(s)` = `s` with every event outside `E_i` erased (`List.filter`):

      s ∈ L(G1 ‖ G2)  ⟺  s ∈ (E1 ∪ E2)*  ∧  P1(s) ∈ L(G1)   ∧  P2(s) ∈ L(G2)
      s ∈ Lm(G1 ‖ G2) ⟺  s ∈ (E1 ∪ E2)*  ∧  P1(s) ∈ Lm(G1)  ∧  P2(s) ∈ Lm(G2)

  Key lemma: from a product of sets the run stays a product, for `s ∈ (E1 ∪ E2)*`:

      run∥(S1 × S2, s) = run1(S1, P1(s)) × run2(S2, P2(s))

- **(L2') Determinism:** `G1`, `G2` deterministic ⟹ `|X0| ≤ 1` and `|f∥(x, e)| ≤ 1`.

## 4. Lean: from local facts to languages (generic)

Used by `parallel` now, and later by every operation whose verified core builds an automaton
state by state (observer, supervisor synthesis, ...).

**Setting.** `H` has states `0 … k−1`, transitions `fH`, initial `X0H`, marking `mH`. `T` is a transition
system over `σ`. `φ : Fin k → σ` labels each state of `H` with a state of `T`. For a set `S` of
`H`-states, `φ(S) = {φ(i) | i ∈ S}`.

**(L3) Bridge theorem.** If

| | hypothesis |
|---|---|
| start | `φ(X0H) = X0_T` |
| step | for every `i` and `e`: `φ(fH(i, e)) = f_T(φ(i), e)` |
| marking | for every `i`: `mH(i) = marked_T(φ(i))` |

then `L(H) = L(T)` and `Lm(H) = Lm(T)`.

**Proof:** by induction on `s`, `φ(run_H(X0H, s)) = run_T(X0_T, s)`. The base case is *start*;
each event uses *step* (the image of a union is the union of the images). A set is nonempty iff
its image is, which gives `L`. *Marking* gives `Lm`.

Not needed for the languages: injectivity of `φ` (two states with one label behave identically)
and reachability of `H`'s states (the induction never uses it). Injectivity is needed for
determinism (L5).

**(L4) The output is a well-formed automaton.** For `T = G1 ‖ G2` and the hypotheses of (L3), `H`
with events `E1 ∪ E2` satisfies W1–W3:
- W1 comes from *step* and §2;
- W2 holds by definition;
- W3: if `k > 0`, the pair type is nonempty, so `n1, n2 > 0`, so `X01 × X02 ≠ ∅`, so `X0H ≠ ∅` by *start*.

**(L5) DFA in ⇒ DFA out.** If moreover `φ` is injective (distinct labels) and `T` is deterministic
(`|X0_T| ≤ 1`, `|f_T(x, e)| ≤ 1`), then `H` is deterministic: `|X0H| = |φ(X0H)| = |X0_T| ≤ 1` and
`|fH(i, e)| = |φ(fH(i, e))| = |f_T(φ(i), e)| ≤ 1` (an injective map keeps sizes). With (L2') this gives:
`G1`, `G2` deterministic ⟹ `H` deterministic.

**Composition:** (L3) + (L2) give `L(H) = P1⁻¹ L(G1) ∩ P2⁻¹ L(G2) ∩ (E1 ∪ E2)*`, and the same for `Lm`.

## 5. Nagini: postconditions of the core

The encoding is from wrapper.md §4: transitions grouped by state, events numbered `0 … m−1`. Output
state `i` is the pair `(p1[i], p2[i])`. Its transitions are positions `ostart[i] … ostart[i+1]−1` of
`oevt` / `odst`.

`has1(x, e, y)` means "some position `j` of state `x`'s block in G1 has `evt1[j] = e` and `dst1[j] = y`"; likewise `has2`.

**Synchronous move** `sync(x1, x2, e, y1, y2)`, the list form of `f∥`:

    in_E1[e] and in_E2[e]:      has1(x1, e, y1) and has2(x2, e, y2)
    in_E1[e] and not in_E2[e]:  has1(x1, e, y1) and y2 == x2
    not in_E1[e] and in_E2[e]:  y1 == x1 and has2(x2, e, y2)

| # | Postcondition (on success) | Gives (L3) | Status |
|---|---|---|---|
| N0 | Separate verified function `check_agree` returns True ⟺ agreement (§2) | decision 1 | to do |
| N1 | Every output state is a pair of input states; blocks well formed; every target is an output state | φ well defined | **proved** (core) |
| N2a | *Sound:* each position `k` in block `i` satisfies `sync(p1[i], p2[i], oevt[k], p1[odst[k]], p2[odst[k]])` | step ⊆ | **proved** (checker `check_sound`, §5a) |
| N2b | *Complete:* for each input move `sync(p1[i], p2[i], e, y1, y2)` there is a position `k` in block `i` with `oevt[k] = e`, `p1[odst[k]] = y1`, `p2[odst[k]] = y2` | step ⊇ | in progress (checker `check_complete`, §5a) |
| N3 | `oinit[i] == (init1[p1[i]] and init2[p2[i]])`, and every pair of initial states is some output state | start | to do |
| N4 | `omarked[i] == (marked1[p1[i]] and marked2[p2[i]])`; `in_E`, `in_Euc`, `in_Euo` of the output are the element-wise `or` | marking, events | to do |
| N5 | *Distinct:* `i != j` ⟹ `(p1[i], p2[i]) != (p1[j], p2[j])` | φ injective (L5) | **proved** (core) |

N2b and N3 contain "there is". In Nagini these are easiest with **witness lists** returned by the
core. For example, each input position records the output position it produced, and the postcondition
states that the record is correct. That is an implementation choice, made when the code is written.

The core gains the inputs `marked1/2`, `in_Euc1/2`, `in_Euo1/2` and the outputs `oinit`, `omarked`, and
the output event lists.

**Dropped from the earlier plan** (formal-verification log, 2026-10-18): reachability witnesses (old P4)
and separate closure (old P3; N2b includes it). (L3) needs neither.

**N5 and the pair key (done).** Distinct pairs need lookups that never miss an existing pair, i.e.
injectivity of the key `x1 * n2 + x2`. Keying the map by the tuple `(x1, x2)` does not work in
Nagini: dictionary keys are compared by object identity, so even `(a, b) in index` right after
`index[(a, b)] = 5` cannot be proved. Instead the key is a `@Pure` function `key`, its injectivity
is a lemma (`key_injective`), and the only nonlinear fact, `c >= 0, n2 >= 0 ⟹ c * n2 >= 0`, is a
pure inductive lemma (`mul_nonneg`). No quantifier mentions the multiplication. The map
invariant `map_ok` states both directions (each state's key maps to it; each key maps to a state
with that key), and `distinct` follows.

## 5a. Where the proofs live (decision 5, proposed)

**What was tried.** Proving N2a inside the core, with the facts carried through the BFS as loop
invariants. Every variant timed out in Z3 (more than 10 minutes), even for a straight-line method
(`move`) that adds one state and one transition. The cause is that the soundness facts read the
pair lists and the output lists at indices taken from other lists, and every `get_or_add` and
`emit` changes those lists, so Z3 has to re-prove the whole quantifier after each step. Without
the soundness postcondition, the same method verifies in 22 s.

**What works.** A separate, verified function `check_sound` (`src/ops_aut/verified_ops/parallel_check.py`)
walks the finished output in the order the core emits it, and checks each output transition
against the next expected synchronous move. It records witnesses: `ostate[k]` (the state that
transition `k` leaves), `osrc1[k]`, `osrc2[k]` (the input transitions used, `-1` for a side that
stays). Proved (Nagini, about 65 s): if it returns True, every output transition is a synchronous
move, in the witness form:

    ostart[i] <= k < ostart[i + 1]  for i = ostate[k]                (k is in the block of i)
    osrc1[k] >= 0:  osrc1[k] in the block of p1[i] in G1, evt1[osrc1[k]] == oevt[k],
                    dst1[osrc1[k]] == p1[odst[k]]
    osrc1[k] <  0:  p1[odst[k]] == p1[i] and oevt[k] not in E1
    (likewise for G2)

With W1 of the inputs this is `sync(p1[i], p2[i], oevt[k], p1[odst[k]], p2[odst[k]])` (§5). The
library will raise if the check fails; so every result it returns is proved sound. The tests show
it never fails on the core's output (300 random pairs), and that it rejects corrupted outputs.

**Completeness (N2b), in progress.** A second pass over the now fixed lists, `check_complete`,
checks that each synchronous move of each state is some output transition of that state. The
predicates and a lemma verify; the walk's loop invariants still time out. Drafts and notes:
`doc/wip/parallel/` (outer repository).

**Why this is sound.** The guarantee is about what the library returns: a checker that is proved
to return True only for correct outputs certifies each result. What it does not prove is that
the core never makes the check fail; that is covered by tests, like the fuel bound.

## 6. Matching the two sides (checked by hand)

| Lean | Nagini | Same because |
|---|---|---|
| `f∥` (§2) | `sync` (§5) | the three cases are identical; `has1(x, e, y)` ⟺ `y ∈ f1(x, e)` by the encoding (wrapper.md §4) |
| *step*, `⊆` and `⊇` | N2a, N2b | with `φ(i) = (p1[i], p2[i])` and `fH(i, e)` = the set of `odst[k]` for `k` in block `i` with `oevt[k] = e` |
| *start* | N3 | `X0H` = the set of `i` with `oinit[i]` |
| *marking* | N4 | `mH(i) = omarked[i]` |
| `φ` injective | N5 | literal |
| `Agree` | N0 | literal |

## 7. Trusted, not proved

- **Encoding and decoding** (wrapper.md §3–§4).
- **The hand check of §6.**
- **Stripping contract statements before running.** An AST pass that drops only statement-level contract calls (to be added to the library).
- **Fuel.** The core returns 1 ("fuel exhausted") only if it found more than n1 · n2 distinct pairs, which is impossible; proving that would need a pigeonhole argument. The wrapper raises if it happens, and the guarantees hold for result 0.
- **The checker never fails on the core's output** (decision 5). Tested, not proved; the wrapper raises if it does.

## 8. Not covered (yet)

- **Every state of H is reachable.** True by the search order, but it affects size only, not the languages.
- **Speed.**

## 9. Order of work

1. Review of this spec.
2. Lean: L0 (refactor), L1, L2, L2', L3, L4, L5; `lake build` with no `sorry`.
3. Nagini:
   - N0 (`check_agree`);
   - the extended core signature;
   - N3 and N4;
   - N2a;
   - N2b;
   - N5 (tuple-keyed map).
4. Library:
   - contract stripping at import;
   - a public `parallel(G1, G2)` (validate, check agreement, encode, run, decode);
   - tests.
