# Spec: basic operations

Status: **`next_states` verified 2026-10-21** (`certisc-lib/src/ops_aut/verified_ops/basic_ops.py`, Nagini, about 31 s; binary-search version, layout B). Encoding: [wrapper.md](wrapper.md) §4. Definitions: [automaton.md](automaton.md) §4.

## 1. `next_states`: one step from a set of states

**Math / Lean.** `δ_f(S, e) = ⋃_{x ∈ S} f(x, e)`. In Lean this is `step f S e`, with `mem_step`:

    y ∈ step f S e  ⟺  ∃ x ∈ S, y ∈ f x e

**Lean: nothing new to prove.** `step` and `mem_step` are already in `DESopsProof/Automaton.lean`.
The facts that use them (runs, languages, prefix closure, determinism) are proved there too. The
Python function only has to compute `step` exactly, and that is the Nagini part.

**Python** (revised 2026-10-21; this is the third version).

    next_states(n, m, start, evt, dst, in_E, S, e, out, src, via, pos)

| Input | Meaning | Precondition |
|---|---|---|
| `start, evt, dst, in_E` | the transitions, grouped by state, **each block sorted by event** (layout B) | `input_ok`: blocks tile the transitions; blocks sorted (`sorted_ok`); every event is a number in E; every target is a state. All guaranteed by `check_automaton` |
| `S` | the set, as a list of state indices (repeats allowed) | `∀ j: S[j] ∈ [0,n)`: in range |
| `e` | the event | `0 ≤ e < m`: in range |
| `out`, `src`, `via`, `pos` | outputs: three empty lists and one empty dict, new for each call | all empty |

The result:
- `out`: the reached states, each once;
- `src[i]`, `via[i]`: witnesses, `out[i]` is reached from `S[src[i]]` by transition `via[i]`;
- `pos[y]`: the position of y in `out`; `y in pos` means y is reached.

Nothing is kept between calls. The public interface (later, over `Automaton` objects) decides
what to return: `out` only, or with the witnesses.

| Postcondition | Math |
|---|---|
| in range | `∀ i ∈ [0,|out|): out[i] ∈ [0,n)` |
| no duplicates, `pos` = positions (`pos_ok`) | `∀ i: pos[out[i]] = i`, and `∀ y ∈ keys(pos): out[pos[y]] = y` |
| sound | `∀ i: S[src[i]] --e-->_{via[i]} out[i]` |
| complete | `∀ j ∈ [0,|S|), ∀ k: S[j] --e-->_k y → y ∈ keys(pos)` |
| terminates | `MustTerminate` |

**Design history** (all three versions are verified):
1. **S as n booleans:** every call costs n (85 ms for 10 states at 1 M states).
2. **S as a list, plus a caller-owned `mark` array and `clear_marks`:** fast, but the caller must manage `mark`.
3. **S as a list, plus a per-call `dict`** (this version): the caller manages nothing.

A plain `set` cannot replace the dict. Completeness would then need "∃ i: out[i] = y", the form
Nagini handles badly; `pos[y]` names the i.

**Cost.** Proportional to the transitions of the states in S plus the result, independent of n.

Measured at 1 M states (10 events, 3 transitions per state), contracts stripped:

| \|S\| | this version | plain Python with a `set`, no witnesses |
|---:|---:|---:|
| 10 | 0.3 ms | 0.2 ms |
| 500,000 | 471 ms | 284 ms |

For large S the overhead is the witness lists, plus the empty lemma calls (`skip`, `next_j`,
`block_of`, `target_of`), which still run as no-op calls after stripping. A stripping step that
also removes those calls would recover part of it.

**Replaceable.** Callers rely only on the contract above. A faster body with the same contract
can replace this one and be re-verified on its own.

**Match with Lean** (checked by hand). With the encoding, `y ∈ f(x, e)` ⟺ some `k` in the block of `x` has
`evt[k] == e` and `dst[k] == y` (wrapper.md §4), and the Finset `S` is the set of entries of the list `S`. So:
- *sound* is the ⟹ direction of `mem_step`, with the witness `x = S[src[i]]`;
- *complete* is the ⟸ direction (y ∈ keys(pos), and keys(pos) = entries of `out` by `pos_ok`).

Together, the set of entries of `out` = `step f S e`.

**How it finds the e-transitions** (layout B, adopted 2026-10-21). Each state's block is sorted by
event. Two binary searches give the range:
- `lower_bound`: `a` with `evt[k] < e` on `[lo, a)` and `≥ e` on `[a, hi)`;
- `upper_bound`: `b` with `evt[k] ≤ e` on `[a, b)` and `> e` on `[b, hi)`.

So `[a, b)` holds exactly the e-transitions of x, and only those are visited.

**Proof structure** (for whoever extends it). The loop invariants are `pos_ok`, `sound` and
`complete_upto(j, k)` ("every move from S[j'] with j' < j, or from S[j] before position k, has its
target in `pos`"). Small methods carry them across one step:
- `visit` adds one target if it is new;
- `skip_range(j, K1, K2)` passes a range with no e-move of S[j] (used for `[0, a)` and `[b, hi)`);
- `next_j` moves to the next entry of S.

The two searches use `block_sorted` (pairwise order in a block). `block_of` gets it from
`sorted_ok`. Each step method asserts the quantified body of its postcondition explicitly: Nagini
does not re-establish a quantified function over a list that was just written (see
`doc/wip/parallel/README.md`, lessons 4–6).
