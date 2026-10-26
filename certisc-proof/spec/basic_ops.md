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
| no duplicates **as objects** (see the caveat below), `pos` = positions (`pos_ok`) | `∀ i: pos[out[i]] = i`, and `∀ y ∈ keys(pos): out[pos[y]] = y` |
| sound | `∀ i: S[src[i]] --e-->_{via[i]} out[i]` |
| complete | `∀ j ∈ [0,|S|), ∀ k: S[j] --e-->_k y → y ∈ keys(pos)` |
| terminates | `MustTerminate` |

**Caveat (found 2026-10-26): "no duplicates" for `next_states` holds for objects, not values.**
Nagini models a dict as a map from *objects* to objects (`dict_acc : Map[Ref, Ref]`), while `==`
on integers compares values. Nothing in its model says two integer objects with the same value
are the same object. So `pos_ok` proves that no two positions of `out` hold the **same object**,
not that they hold different **numbers**. Soundness, completeness and range are unaffected (each
is proved for a specific object, then read as its value). Distinct values hold at runtime (Python
dicts compare by value) and are tested, but they are **not proved**. `active_events` does not have
this gap: its marks are a list indexed by value (§2).

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

## 2. `active_events`: the events enabled at a set of states

Status: **verified 2026-10-23** (same file, Nagini; the whole file takes about 25–27 s).

**Math / Lean.**

    Σ_f(S) = { e | δ_f(S, e) ≠ ∅ }                          Lean: active f S   (Automaton.lean)
    e ∈ active f S  ⟺  ∃ x ∈ S, f(x, e) ≠ ∅                 Lean: mem_active
    active G.f S ⊆ E   (for a valid automaton, by W1)        Lean: Automaton.active_subset_E

New in Lean: the definition and these two lemmas, about 20 lines. `lake build` passes, with only
the standard axioms.

**Python.**

    active_events(n, m, start, evt, dst, in_E, S, emark, out, src, via)

| Input | Meaning | Precondition |
|---|---|---|
| automaton | as for `next_states` | `input_ok` (blocks, sorted, transitions) |
| `S` | list of state indices (repeats allowed) | `∀ j: S[j] ∈ [0,n)` |
| `emark` | one entry per **event** number | `|emark| = m`, all −1 |
| `out`, `src`, `via` | outputs | empty |

`emark` is a list over events, not a dict. Nagini compares dict keys as objects, so it cannot
prove `evt[t] in pos` from `evt[t] == e` and `e in pos`; list indices compare by value. Its cost
is m, the size of the alphabet, per call, independent of n. The public `ops_aut.active_events`
allocates it.

| Postcondition | Math |
|---|---|
| in range, no duplicates (`marks_ok`) | `∀ i: out[i] ∈ [0,m) ∧ emark[out[i]] = i`; `∀ e: emark[e] ≠ −1 → out[emark[e]] = e` |
| sound | `∀ i: ev_at(src[i], via[i], out[i])`: `via[i] ∈ block(S[src[i]])` and `evt[via[i]] = out[i]` |
| complete | `∀ j ∈ [0,|S|), ∀ k ∈ block(S[j]): emark[evt[k]] ≥ 0` |

**Match with Lean** (checked by hand). With the encoding, `f(x, e) ≠ ∅` ⟺ some `k ∈ block(x)`
has `evt[k] = e`:
- *sound* gives ⊆ (witness `x = S[src[i]]`);
- *complete* gives ⊇ (`emark[e] ≥ 0` ⟺ e is an entry of `out`, by `marks_ok`).

So the entries of `out` are exactly `active f S`.

**Algorithm** (the scalability choices of `next_states`). For each state of S, the block is
sorted by event. The loop reads the first transition of each run of one event, adds the event if
new (`visit_event`), and jumps past the run with the verified `upper_bound`.

**Proof structure.**
- Outer loop (`active_events`): calls `ev_scan(j)` for each state, then `ev_next_j`.
- `ev_scan(j)` covers one block, with the invariants `marks_ok`, `ev_sound`, and
  `ev_complete_upto(j, k)` ("the event of every transition of S[0 … j−1], and of S[j] before k,
  is marked").
- Lemmas:
  - `block_events` (the block is valid and sorted, and its events are `< m`);
  - `ev_enter` (positions before the block are not S[j]'s);
  - `ev_run` (a run found by `upper_bound` has a single event, now marked);
  - `ev_next_j`.

**What it took** (recorded in `doc/logs/formal-verification.md`):
- the dict → event-list change;
- `ev_at`, a single function for "transition k of S[j] is on event e", to match terms;
- splitting the inner loop into `ev_scan`;
- `block_events`, so the inner loop does not carry `input_ok`: the slim version cut `ev_scan`
  from 201 s to a few seconds.

**Speed** (contracts stripped, 100,000 states, 20 events, ms per call):

| deg | \|S\| | plain Python (set comprehension) | verified |
|---:|---:|---:|---:|
| 3 | 1,000 | 0.14 | 1.0 |
| 3 | 50,000 | 7.1 | 54 |
| 30 | 1,000 | 0.71 | 7.0 |
| 30 | 50,000 | 35 | 340 |

7–10× slower than a C-level set comprehension: each run costs a call to `visit_event` and
`upper_bound` (Python loops). Typical use is small sets (one state, a supervisor's estimate),
where both take about a millisecond or less.

## 3. The active-event index, and `active_events` over it

Status: **checker verified 2026-10-26** (`core_aut/verified_core/active_index.py`, whole file
54–93 s); `active_events_idx` **verified 2026-10-26** (`basic_ops.py`, whole file 163–307 s).

**What it is.** A representation of the automaton, not new mathematics, so Lean needs nothing
new. For each state x, blocks are sorted by event, so each event of x is one *run* of
consecutive transitions. The index lists where each run starts:

    A[x] .. A[x+1]-1     the positions in H of the run heads of x      (|A| = n+1, A[0] = 0, A[n] = |H|)
    H[i]                 a head: the first transition of a run; its event is evt[H[i]]
    nxt(i)               the end of head i's run: H[i+1], or start[x+1] for the last head of x

So the active events of x are `evt[H[A[x]]], …, evt[H[A[x+1]-1]]`, strictly increasing.

**Certified, not verified, construction.** A trusted builder (`core_aut/trusted/active_index.py`)
computes (A, H) in one scan. The verified `check_index` accepts it only if it is correct, so a
bug in the builder can only make the build fail. A `ValidAutomaton` builds and checks the index
on first use and keeps it (a private slot; it depends only on the frozen encoding). A
`ValidAutomaton` read from JSON is the same: nothing is stored in the file.

**Correctness (`index_ok`)**, stated in full in the contracts (see the note in
`active_index.py`):

| Part | Math |
|---|---|
| shape | `n ≥ 0 ∧ |A| = |start| = n+1 ∧ A[0] = 0 ∧ A[n] = |H|` |
| per state | `∀ x ∈ [0,n): 0 ≤ A[x] ≤ A[x+1] ≤ |H| ∧ seg_ok(start[x], start[x+1], A[x], A[x+1])` |
| `seg_ok(s0,s1,a0,a1)` | `(a0 = a1 ⟺ s0 = s1) ∧ (a0 < a1 → H[a0] = s0) ∧ ∀ i ∈ [a0,a1): run_ok(i) ∧ ∀ i1 < i2: evt[H[i1]] < evt[H[i2]]` |
| `run_ok(i)` | `s0 ≤ H[i] < nxt(i) ≤ s1 ∧ ∀ t ∈ [H[i], nxt(i)): evt[t] = evt[H[i]] ∧ (i+1 < a1 → evt[H[i]] ≠ evt[H[i+1]])` |

`check_index(n, start, evt, A, H)` requires `blocks_ok ∧ sorted_ok` (from `check_automaton`)
and ensures `Result → index_ok`.

**`active_events_idx`** has the same contract as `active_events` (§2), plus the index and
`index_ok` as a precondition. The only change in the algorithm: the end of each run is `nxt(i)`,
read from the index, instead of a binary search (`upper_bound`).

**Proof structure.**
- The outer loop reads the block and the heads of `S[j]` (`lo, hi, a0, a1`) and applies the lemma
  `seg_runs`, which turns `seg_ok` into `runs_ok` (only the per-head `run_ok` facts) and
  `H[a0] = lo`.
- `ev_scan_idx` loops over the heads with `runs_ok` in its invariant, and `ev_run_idx` (instead of
  `ev_run`) covers one run, using `run_ok` instead of sortedness.
- With `seg_ok` itself in `ev_scan_idx`, the proof ran over 15 minutes: its pairwise part
  (`Forall2`, no trigger) was unfolded into every step. With `runs_ok`, `ev_scan_idx` takes
  23–31 s.
- `b = nxt(i)` is written as an inline `if` (with a hint `b = nxt(i)`), not a call to `nxt`. The
  call verifies faster (whole file 44–50 s) but costs a Python function call per run, which
  cancelled the speed-up.

**Public API.** `active_events(V, S)` on a `ValidAutomaton` uses the index. On a plain
`Automaton` it uses §2, because the automaton is validated on every call and building the index
each time would cost more than it saves. `active_events_at(G, x)` is `active_events(G, [x])`.

**Speed** (contracts stripped, random automata, best of 3; S = all states; final code):

| n | m | T | binary search (§2) | index | speed-up | index build + check (once) |
|---:|---:|---:|---:|---:|---:|---:|
| 100,000 | 10 | 500,000 | 0.140 s | 0.095 s | 1.5× | 0.20 s |
| 100,000 | 50 | 2,000,000 | 1.138 s | 0.315 s | 3.6× | 1.00 s |
| 20,000 | 5 | 1,000,000 | 0.054 s | 0.022 s | 2.4× | 0.11 s |

The 1.138 s is noisy: the same case measured 0.72–0.73 s in other runs, which gives 2.3×. The build
costs about one to three all-state calls, and is paid once per `ValidAutomaton`.
