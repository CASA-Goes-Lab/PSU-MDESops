# Spec: automaton (general and deterministic)

Status: **agreed 2026-10-16** (decisions 1–8). §3–§4 are formalized in Lean (§7). The wrapper and the Nagini precondition are in [wrapper.md](wrapper.md).

Target class: the new `Automaton` (`legacy/DESops-lib/DESops/core/automaton.py`). The old
`DFA`/`NFA` classes are not covered.

**Moved 2026-10-20:** that class is now in `legacy/DESops-lib/`. The standalone package
`certisc` (`certisc-lib/src/core_aut/automaton.py`) has an `Automaton` with the same fields
(`states`, `events`, `Euc`, `Euo`, `init`, `State.marked`, `State.out`). The definitions below
apply to it unchanged. The `_valid` flag (decision 7) exists only in the legacy class.

## 1. Decisions

| # | Question | Decision |
|---|---|---|
| 1 | Empty automaton, initial states | No initial state **iff** no states. With states: at least one initial state; exactly one if deterministic. |
| 2 | Well-formedness: who checks | Precondition, checked by the wrapper before the verified code runs. Plus a "validated" flag so automata already checked (and not modified since) are not re-checked; see §5. |
| 3 | `Euc`, `Euo` | Part of the tuple, with `Euc, Euo ⊆ E`. |
| 4 | Marking | Must be `bool`. |
| 5 | Events | Any hashable value, compared with Python `==`. The wrapper numbers them; see §5. |
| 6 | DFA vs NFA | One general type; *deterministic* is a property of it. |
| 7 | Validated flag | (A1): cleared by `Automaton`'s methods only; direct edits of `init`, `events`, `Euc`, `Euo`, `marked`, `out` after validation are unsupported (see §8). |
| 8 | (W3) while building | Not enforced by the class (construction and `remove_states` pass through "states but no initial state"); checked by validation, so such an automaton is never valid input to a verified operation. |
| 9 | Unvalidated input to a verified operation | Validated automatically (one check); raises if invalid. |

## 2. What the class does today

| | `Automaton` |
|---|---|
| states | indices `0..n-1` (`states` list) |
| initial states | `init: set[int]`, a public attribute that is edited directly (e.g. `out.init.add(...)` in `_parallel_pair`) |
| transitions | `State.out: dict[event, list[target]]`; lists are never empty (`remove_transition` deletes empty ones) and have no duplicates (`add_transition` refuses them) |
| deterministic | `is_deterministic`: `len(init) <= 1` and no `out` list longer than 1 (a counter kept by the methods) |
| marking | `State.marked`, declared `bool`, not enforced |
| alphabet | `events`; `add_transition` adds the event; `__init__` adds `Euc ∪ Euo`; later edits to `Euc`/`Euo` don't |
| range checks | `add_transition` checks `source` and `target` are states (the `source` check was added 2026-10-16) |

**Gaps between the class and §3.** The class allows all of these; §3 rules them out:
- states but empty `init`, which is normal while an automaton is being built;
- `Euc`/`Euo` not inside `events`;
- non-`bool` marking.

The verified layer therefore checks well-formedness at its entry (§5) instead of relying on the class.

## 3. Definition

An **automaton** over a set of events `Σ` (any set with decidable equality) is a tuple

    G = (n, E, Euc, Euo, f, X0, Xm)

| Part | Meaning |
|---|---|
| `n ∈ ℕ` | number of states; the state set is `X = {0, …, n−1}` |
| `E ⊆ Σ`, finite | the alphabet |
| `Euc, Euo ⊆ Σ`, finite | uncontrollable and unobservable events |
| `f : X × Σ → 2^X` | the transition function |
| `X0 ⊆ X` | initial states |
| `Xm ⊆ X` | marked states |

It must be **well-formed**:

- **(W1)** If `f(x, e) ≠ ∅` then `e ∈ E`. Transitions use only alphabet events.
- **(W2)** `Euc ⊆ E` and `Euo ⊆ E`.
- **(W3)** `X0 = ∅ ⟺ n = 0`. There is an initial state exactly when there are states.

`G` is **deterministic** if `|X0| ≤ 1` and `|f(x, e)| ≤ 1` for every `x` and `e`. With (W3), a
deterministic automaton with states has exactly one initial state. For a deterministic `G`, `f` is
the partial function of the textbook DFA: `f(x, e) = {y}` or `∅` (undefined).

`E` may contain events that label no transition. This matters for `parallel`: an event of `E1`
blocks in `G1 ‖ G2` wherever `G1` cannot execute it.

## 4. Languages

**Successor set** `f* : 2^X × E* → 2^X`. It is the set of states reachable from a set of states by a word:

    f*(S, ε)   = S
    f*(S, s·e) = ⋃ { f(x, e) | x ∈ f*(S, s) }

**Generated and marked languages:**

    L(G)  = { s ∈ Σ* | f*(X0, s) ≠ ∅ }
    Lm(G) = { s ∈ Σ* | f*(X0, s) ∩ Xm ≠ ∅ }

**Reachable states:** `Ac(G) = ⋃ { f*(X0, s) | s ∈ Σ* }`.

For a deterministic `G`, `f*(X0, s)` is `∅` or a single state `{y}`. The textbook `f(x0, s)` is that `y`.

**Sanity lemmas,** to be proved in Lean before any operation:

1. `L(G)` is prefix-closed.
2. `Lm(G) ⊆ L(G)`.
3. `L(G) = ∅ ⟺ n = 0`, and `ε ∈ L(G) ⟺ n > 0` (by W3).
4. `L(G) ⊆ E*` (by W1).
5. If `G` is deterministic, `|f*(X0, s)| ≤ 1` for every `s`.
6. Changing transitions or marking of states outside `Ac(G)` leaves `L` and `Lm` unchanged (the version with removal and renumbering is deferred to trim).

## 5. Mapping from the class

**Mapping from `Automaton`:**

| Spec | From the class |
|---|---|
| `n` | `len(states)` |
| `E`, `Euc`, `Euo` | `events`, `Euc`, `Euo` |
| `f(x, e)` | `set(states[x].out.get(e, []))` |
| `X0` | `init` |
| `Xm` | `{ x | states[x].marked }` |

**Validation, event numbering, encoding and the verified checker** are in [wrapper.md](wrapper.md).

## 6. Python encoding for the verified core

Moved to [wrapper.md](wrapper.md) §4–§5: grouped by state (`start` / `evt` / `dst`) instead of the flat
`src` / `evt` / `dst` lists proposed earlier. Flat lists made the determinism check quadratic in the
number of transitions.

## 7. Lean encoding: `DESopsProof/Automaton.lean`

**Formalized 2026-10-16.** `lake build` succeeds with no `sorry`. `#print axioms` on every lemma below
lists only Lean's standard `propext`, `Classical.choice`, `Quot.sound`.

| Spec | Lean |
|---|---|
| `f*(S, s)` | `run f S s` (with `step f S e = S.biUnion (f · e)`) |
| `L`, `Lm`, `Ac` | `Automaton.L`, `.Lm`, `.Ac`, built on `gen f X0`, `mkd f X0 m`, `reach f X0` for any `f` |
| (W1)–(W3) | structure fields `wf_E`, `wf_Euc`, `wf_Euo`, `wf_X0` |
| deterministic | `Automaton.IsDeterministic` |

| §4 lemma | Lean theorem | Note |
|---|---|---|
| 1. prefix-closed | `L_of_append`, `L_of_isPrefix` | |
| 2. `Lm ⊆ L` | `Lm_le_L` | `≤` is `⊆` on Mathlib's `Language` |
| 3. `L = ∅ ⟺ n = 0`; `ε ∈ L ⟺ n > 0` | `L_empty_iff`, `nil_mem_L` | stated as `(∀ s, s ∉ G.L) ↔ G.n = 0` |
| 4. `L ⊆ E*` | `mem_E_of_mem_L` | |
| 5. deterministic ⇒ `\|f*(X0, s)\| ≤ 1` | `IsDeterministic.card_run_le_one` | |
| 6. only reachable states matter | `L_congr_Ac`, `Lm_congr_Ac` | see below |

**Lemma 6 is stated without renumbering.** For any `f'` that agrees with `f` on every reachable
state, and any `m'` that agrees with the marking there, the languages are the same. That covers
deleting, redirecting or re-marking anything unreachable. The version that removes states and
renumbers the rest (`Fin n → Fin k`) is deferred to the operation that does it (trim / accessible
part), where it's needed.

**The structure has no `[DecidableEq α]`.** Nothing here needs it; operations that intersect alphabets
(`parallel`) add it.

## 8. Decided design notes

**A. The validated flag: decided, A1.** Kept here for the record of what A1 does not cover.

The flag: `Automaton` would get a private flag `_valid`, set by `validate()` and
cleared by every mutation. Results of verified operations come out already valid, because the
postcondition proves it, so chained operations (`parallel(parallel(G1, G2), G3)`) validate only their
original inputs.

The difficulty is that not every mutation goes through a method:
- `init`, `events`, `Euc`, `Euo` are public sets edited directly (`out.init.add(...)` in `_parallel_pair`);
- `states[i].marked` is a plain attribute;
- `states[i].out` is documented as "use the methods", but nothing stops a direct edit.

Two options:
- **(A1) Methods only.** The methods clear the flag; direct edits of the attributes above are declared
  unsupported, the same contract `is_deterministic` already relies on (its counter misses direct
  `out` edits too). Small change. The gap: `g.init.add(5)` after validation leaves a stale "valid",
  and the verified code then runs on input outside its precondition.
- **(A2) Close the gaps.**
  - `init`, `events`, `Euc` and `Euo` become set subclasses that clear the owner's flag on any change
    (and properties, so assigning a new set also clears it).
  - `State.marked` becomes a property that does the same; each `State` then needs a reference to its
    `Automaton`.
  - `out` stays methods-only, as documented.

  More code; the only remaining gap is a direct `out` edit.

A third option is no flag at all: always validate. Measured above at 3–8 % of one `parallel`.

**B. Empty `init` while building: decided** (decision 8): checked at validation, not enforced by the class.
