# What is verified in certisc, and why it works

This note covers the two verified pieces that exist so far:
- **`check_automaton`**: is an automaton well formed?
- **`next_states`**: which states can one event reach from a set of states?

Other operations will get their own sections as they are verified. Design history and
measurements are in `doc/logs/`; the spec notes are in `certisc-proof/spec/`.

## 1. How the guarantee is built

```
  Lean 4 (certisc-proof/)            Nagini (certisc-lib/src/*/verified_*/)        Python
  ─────────────────────────          ───────────────────────────────────          ──────
  mathematical definitions     ◄──►  postconditions of the function       ◄──►    the code
  and theorems about them            (Requires / Ensures)
        (proved by Lean)              (hand check, written down in spec/)    (proved by Nagini)
```

- **Lean** says what the objects *are* (automaton, well-formedness, one step, languages). It proves
  the mathematical facts about them: L is prefix-closed, Lm ⊆ L, a deterministic automaton is in
  at most one state, and so on.
- **Nagini** proves that the Python code meets its contract, for **every** input that satisfies
  the preconditions, not just tested ones. The contract is written in `Requires` / `Ensures`
  inside the code.
- **The hand check** links the two: each Nagini postcondition says the same thing as the Lean
  definition, once the encoding below is taken into account. It is written out in `certisc-proof/spec/`.

The proofs are checked by machines: Lean's kernel for Lean, and Viper/Z3 behind Nagini for
Python. What is *not* proved is listed in §6.

## 2. What the verified code sees: the encoding

Users work with `Automaton` objects (`core_aut/automaton.py`). Before verified code runs, the
trusted function `encode` (`core_aut/trusted/encoding.py`) copies the automaton into plain lists:

| List | Meaning |
|---|---|
| `n`, `m` | states are `0 … n−1`, events are numbered `0 … m−1` |
| `in_E[e]`, `in_Euc[e]`, `in_Euo[e]` | event e is in E, in Euc, in Euo |
| `init[x]`, `marked[x]` | state x is initial, marked |
| `start`, `evt`, `dst` | the transitions, grouped by source state |

State x owns the positions `block(x) = [start[x], start[x+1])`. Position k is the transition
`x --evt[k]--> dst[k]`. Within each block the transitions are **sorted by event**, so the
transitions of one state on one event are consecutive.

`encode` does the sorting, and `encode` is trusted. But the sorting is not *trusted*: the verified
checker re-checks it (condition 8 in §3), so a sorting bug in `encode` would be reported as an
invalid automaton, never passed on to the verified operations.

Notation used below: `x --e-->_k y` means "position k is in `block(x)`, `evt[k] = e`,
`dst[k] = y`", i.e. the transition `x --e--> y`.

## 3. `check_automaton`: is the automaton well formed?

**Where:** `core_aut/verified_core/check.py` (Nagini, about 18 s). Called by the public
`check_or_raise(G, deterministic=False)`.

### What "well formed" means

These are the conditions of `certisc-proof/spec/automaton.md` §3, plus two conditions about the
encoding itself.

| Code | Condition (math) | In Lean (`DESopsProof/Automaton.lean`) |
|---|---|---|
| 1 | sizes: `n ≥ 0`, `m ≥ 0`, `|marked| = n` | built into the type (`Fin n`, `marked : Fin n → Bool`) |
| 2 | blocks tile the transitions: `|start| = n+1`, `start[0] = 0`, `start[n] = T`, `0 ≤ start[x] ≤ start[x+1] ≤ T` | encoding only (Lean uses a function `f`) |
| 8 | each block sorted by event: `∀ x, ∀ j < i in block(x): evt[j] ≤ evt[i]` | encoding only |
| 3 | every transition's event is an event of E, and its target is a state: `∀ k: evt[k] ∈ [0,m) ∧ in_E[evt[k]] ∧ dst[k] ∈ [0,n)` | **(W1)** `wf_E : ∀ x e, (f x e).Nonempty → e ∈ E` |
| 4 | `Euc ⊆ E` and `Euo ⊆ E` | **(W2)** `wf_Euc`, `wf_Euo` |
| 5 | an initial state exists exactly when states exist | **(W3)** `wf_X0 : X0.Nonempty ↔ 0 < n` |
| 6 | (deterministic) at most one initial state | `IsDeterministic`, first part: `X0.card ≤ 1` |
| 7 | (deterministic) no state has two transitions on the same event | `IsDeterministic`, second part: `∀ x e, (f x e).card ≤ 1` |

Together these define `valid_automaton(…, deterministic)` in `check.py`.

### What Nagini proves

| Guarantee (in `Ensures`) | Math |
|---|---|
| exactness | `check_automaton(...) = 0  ⟺  valid_automaton(...)` |
| error codes are honest | code c is returned only when condition c fails (e.g. code 3 ⟹ ¬transitions_ok) |
| no side effects | the input lists are unchanged |
| termination | every loop ends (`MustTerminate`) |

### Why it matters

Every verified operation takes "the automaton is valid" as a **precondition**. `validate(G)`
establishes it once and returns a read-only **`ValidAutomaton`** (`core_aut/valid.py`): the
checked encoding, stored as tuples so it cannot change afterwards. Operations take it and do not
check again, and "valid" cannot go stale. The readers (`io_aut.read_aut`, `read_fsm`) return a
`ValidAutomaton` too: they are trusted code that only builds the automaton, and validity always
comes from the verified checker. So no verified operation ever runs on malformed input. And once an automaton
passes, the Lean theorems about well-formed automata apply to it:
- L is prefix-closed (`L_of_isPrefix`);
- Lm ⊆ L (`Lm_le_L`);
- L ⊆ E* (`mem_E_of_mem_L`);
- L = ∅ ⟺ there are no states (`L_empty_iff`);
- a deterministic automaton is in at most one state after any word
  (`IsDeterministic.card_run_le_one`);
- changing unreachable parts does not change L or Lm (`L_congr_Ac`, `Lm_congr_Ac`).

### Why the proof works (in short)

Each condition has a `@Pure` definition (the spec) and a checker loop (the code). The loop
invariant says "the condition holds for the part scanned so far". When the loop ends, the
scanned part is everything, and the invariant is the definition.

Sortedness is defined **pairwise**, but checked on **neighbours only**, so it runs in linear
time. The invariant step "everything before is ≤ `evt[k−1]` ≤ `evt[k]`" extends the pairwise
fact by one position.

## 4. `next_states`: one step from a set of states

**Where:** `ops_aut/verified_ops/basic_ops.py` (Nagini, about 25–31 s). Called by the public
`ops_aut.next_states(G, states, event, witnesses=False)`.

### The mathematics (Lean)

    δ(S, e) = ⋃_{x ∈ S} f(x, e)                     Lean: step f S e
    y ∈ step f S e  ⟺  ∃ x ∈ S, y ∈ f x e          Lean: mem_step

`step` is the building block of everything Lean says about behaviour:
- `run` is `step` repeated over a word;
- the generated and marked languages L and Lm are defined with `run`;
- the reachable states `Ac` too.

**Nothing new had to be proved in Lean.** The Python function only has to compute `step` exactly.

### The contract

**Preconditions** (what the caller must guarantee):
- the automaton is valid: `input_ok`, i.e. blocks, sortedness and transitions from §3 (`check_or_raise` gives it);
- `e ∈ [0, m)`: the event is in range;
- `∀ j: S[j] ∈ [0, n)`: the states are in range (repeats allowed);
- `out`, `src`, `via` (lists) and `pos` (dict) start empty.

**Postconditions** (what the function guarantees):

| Guarantee | Math |
|---|---|
| in range | `∀ i: out[i] ∈ [0, n)` |
| no duplicates; `pos` gives positions | `∀ i: pos[out[i]] = i`, and `∀ y ∈ keys(pos): out[pos[y]] = y` |
| sound (with witnesses) | `∀ i: S[src[i]] --e-->_{via[i]} out[i]` |
| complete | `∀ j, ∀ k: S[j] --e-->_k y → y ∈ keys(pos)` |
| termination | `MustTerminate` |

### Why this is exactly `step`

With the encoding, `y ∈ f(x, e)` holds exactly when some k has `x --e-->_k y`.
- **sound** gives ⊆: every `out[i]` has an x = `S[src[i]]` in S and a k = `via[i]` with
  `x --e-->_k out[i]`, so `out[i] ∈ f(x, e)`.
- **complete** gives ⊇: every `y ∈ f(x, e)` with x in S is a key of `pos`, and the keys of `pos`
  are exactly the entries of `out` (by the `pos` guarantee).

So **the entries of `out` are exactly `step f S e`**, each listed once.

### Why the proof works (in short)

- **Binary search.** Each block is sorted, so two binary searches (`lower_bound`, `upper_bound`)
  give the range `[a, b)` holding exactly the e-transitions of x. They are proved from the pairwise
  sortedness. The loop visits only `[a, b)`.
- **Witnesses instead of "there exists".** Soundness would naturally say "there is an x in S
  with…". The code stores the x and the transition (`src`, `via`), so every fact is about a
  specific position. Nagini handles that easily; "there exists" over a growing list it does not.
- **Positions instead of a set.** `pos[y]` names where y is in `out`. That gives "no duplicates"
  (two equal entries would have one position) and lets completeness be stated without "there exists".
- **Loop invariants.**
  - `pos_ok`: `pos` and `out` agree;
  - `sound`: everything added so far is justified;
  - `complete_upto(j, k)`: every e-move of S[0 … j−1], and of S[j] before position k, is already in `pos`.

  At the end, `complete_upto(|S|, 0)` is completeness.
- **Small proof steps.** Each write happens in a small method (`visit`), and each "nothing to do"
  range in a lemma (`skip_range`, `next_j`). Each one states its effect on the invariants and
  asserts it explicitly. Nagini proves small steps quickly; the same facts inside one big loop
  time out.

### Consequences

- `next_states` can be used inside other verified code (reachability, observer, …). Nagini then
  uses only its contract, never its body. Since the contract *is* Lean's `step`, a loop that
  repeats it computes `run` / `reach`, and Lean's theorems about those apply.
- A faster implementation (e.g. a NumPy backend) can replace the body, as long as it satisfies
  the same contract: re-verified if it is Nagini code, or tested against this contract if it is not.

## 5. Reading the code

Every Nagini line in `basic_ops.py` carries two comments:
- **Math:** the formula the line states;
- **Why:** why the line is needed.

Each verified file opens with a glossary of the notation (`Requires`, `Ensures`, `Invariant`,
`Assert`, `Acc`, `MustTerminate`, `ToSeq`, `Old`, `Forall` and triggers). Lines marked
"Why (hint)" are proof hints: facts Nagini can prove but would not find by itself.

## 6. What is trusted (not proved)

| Piece | Why it is trusted | How it is checked instead |
|---|---|---|
| `encode` / `decode` (`core_aut/trusted/encoding.py`) | plain copying between `Automaton` and lists | round-trip tests; sortedness test |
| `_strip.py` | removes contracts and lemma calls before running | only removes statements with no runtime effect; tests compare results |
| the public layer (`validate`, `check_or_raise`, `ops_aut.next_states`) | glue: validate, encode, call, translate back | tests against direct computation |
| `ValidAutomaton` (`core_aut/valid.py`) | read-only by construction (tuples, no setters); made only by `validate` and the readers | tests that it cannot be modified or created directly |
| the readers (`io_aut`) | parse files and build an `Automaton` | validity is decided by the verified checker afterwards; round-trip and format-error tests |
| the hand check Lean ↔ Nagini | definitions in two languages | written out in `certisc-proof/spec/`, reviewed by a person |
| Nagini, Viper, Z3 | the verifier itself | standard tools |
| the Lean kernel and Mathlib | the proof checker | standard tools |

## 7. Reproducing the checks

From `certisc-lib/`, with the `verify` extra (Python ≥ 3.12, Java):

    nagini src/core_aut/verified_core/check.py         # Verification successful, ~18 s
    nagini src/ops_aut/verified_ops/basic_ops.py       # Verification successful, ~25–31 s
    pytest                                             # 38 passed

From `certisc-proof/`:

    lake build                                         # no errors, no `sorry`
