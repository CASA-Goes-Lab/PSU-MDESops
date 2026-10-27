# Spec: reachable states

Status: **verified 2026-10-27.**
- Lean: `Automaton.lean`, section "Reachability certificates" (`lake build` passes, standard axioms
  only).
- Nagini: `ops_aut/verified_ops/reach.py`, whole file about 20 s (two runs: 19.6 s, 19.4 s).
- Public: `ops_aut.reachable`.

User decisions (2026-10-26):
1. any start states (default: the initial states);
2. witnesses as in the other operations (`witnesses=False` by default); each parent is a
   (state, event) pair, so a path reads as a word;
3. this step is only the reachable set (no `accessible(G)` yet).

## Math / Lean

Already in `Automaton.lean` before this step:

    Ac(f, X0) = { y | ∃ s ∈ Σ*, y ∈ f*(X0, s) }                 Lean: reach f X0
    Lemma 6: changing f or the marking outside Ac leaves L, Lm unchanged   (L_congr_Ac, Lm_congr_Ac)

The definition quantifies over all words, which a program cannot check directly. New Lean lemmas
connect it to facts that the code can prove locally (about 90 lines with comments; one new
definition, `Closed`):

| Lemma | Statement | Used for |
|---|---|---|
| R1 (closure, least) | if X0 ⊆ R and R is closed (`∀ x ∈ R, ∀ e, f x e ⊆ R`), then `reach f X0 ⊆ R` | **complete**: everything reachable is in the result |
| R2 (witness order) | if the states are listed `out[0], out[1], …` and each `out[i]` is in X0 or has a transition from some `out[p]`, `p < i`, then every `out[i] ∈ reach f X0` | **sound**: everything in the result is reachable |

Also `mem_reach_of_mem` (X0 ⊆ reach), `mem_reach_of_step` (reach is closed), and the combination:

    reach_eq_of_certificate:  contains X0 ∧ closed ∧ witnesses  →  reach f X0 = {out_i | i < N}

R2 is proved by induction on i. That way Nagini never needs that induction; it only proves local
facts (one transition, one index comparison).

## Python (verified core)

    reachable(n, start, dst, S, mark, out, par, via)

| Input | Meaning | Precondition |
|---|---|---|
| automaton | `start`, `dst` of the encoding (events are not read) | `blocks_ok(n, start, |dst|)`, `targets_ok(n, dst)` (both implied by `check_automaton`) |
| `S` | start states (the caller passes the initial states by default) | `∀ j: S[j] ∈ [0,n)`, repeats allowed |
| `mark` | one entry per **state** | `|mark| = n`, all −1 |
| `out`, `par`, `via` | outputs | empty |

`mark` is a list over states (n entries), indexed by value, not a dict: the lesson from
`active_events`. Its cost, n, is the same order as the operation's, so this is fine here, unlike
in `next_states`.

| Postcondition | Math |
|---|---|
| in range, no duplicates (`marks_ok`) | `∀ i: out[i] ∈ [0,n) ∧ mark[out[i]] = i`; `∀ y: mark[y] ≠ −1 → out[mark[y]] = y` |
| contains S | `∀ j: mark[S[j]] ≥ 0` |
| closed | `∀ i, ∀ k ∈ block(out[i]): mark[dst[k]] ≥ 0` |
| witnesses (sound) | `∀ i: (par[i] = −1 → S[via[i]] = out[i]) ∧ (par[i] ≠ −1 → 0 ≤ par[i] < i ∧ via[i] ∈ block(out[par[i]]) ∧ dst[via[i]] = out[i])` |
| size | `|out| ≤ n` |

**Match with Lean** (checked by hand, as before):
- "contains S" + "closed" + R1 give ⊇ `reach`;
- "witnesses" + R2 give ⊆ `reach`.

So the entries of `out` are exactly `reach f S`.

**Algorithm.** Breadth-first: `out` is also the queue.

    for x in S: if not marked, mark it and append it (par = −1)
    h = 0
    while h < |out|:
        x = out[h]
        for k in block(x):                    # all transitions of x, any event
            if dst[k] is not marked: mark it, append it (par = h, via = k)
        h += 1

- Cost: O(n + T) time; memory: the mark list (n) and three outputs (each at most n).
- No sorting or binary search is needed (all transitions of a block are visited).
- Breadth-first gives shortest witness paths (useful for counterexamples).
- Termination: each append marks a new state, so `|out| ≤ n`, and h goes up to `|out|`. The measure
  is `(n − |out|) + (|out| − h)`.

**Proof structure** (as verified):
- `reachable`: phase 1 marks the start states (`add_state` with par = −1, via = index in S);
  phase 2 is the breadth-first loop, calling `rc_scan(h)` for each entry.
- `rc_scan(h)` follows block(out[h]), calling `add_state` for each unmarked target. The invariant
  `closed_upto(mk, h, k)` says every transition of an entry before h, or of out[h] before position
  k, goes to a marked state. Lemmas: `closed_enter`, `closed_step`, `closed_next`, then
  `closed_final` (h = |out| gives `closed_all`).
- `add_state` only writes (append to out, par, via; mark y). Each invariant is carried across the
  update by its own lemma: `keep_marks`, `keep_wit`, `keep_contains`, `keep_closed`, plus
  `count_mark` for the count.
- Termination: `nmarked(mk, n)`, the number of marked states (recursive `@Pure`), equals |out|.
  The recursive lemmas `count_clear` and `count_mark` (proofs by induction) give |out| ≤ n, so
  the queue loop has the measure 2n − h + 6.

**What it took:**
- **Counting** with a loop failed: Nagini treats ints as objects, so unfolding
  `nmarked(mk, ni)` gives `nmarked(mk, ni − 1)`, which it does not identify with
  `nmarked(mk, i)`. Recursive lemmas avoid this, since their call `count_mark(…, i − 1)` builds
  the same term as the function's definition. `_strip.py` was extended to remove recursive lemmas
  (a function that does nothing except call lemmas under simple conditions).
- **Matching loop:** with the trigger `o[i]`, the witness predicate (whose body reads `o[p[i]]`)
  instantiated itself along the parent chain, and `add_state` timed out. Fix: trigger on `v[i]`.
- **Framing:** with list arguments, Nagini could not show that `S` was unchanged by the appends to
  `out` (it cannot rule out that two list arguments are the same list). Fix: `add_state` and the
  predicates take the inputs as sequence values (`ToSeq(start)`, `ToSeq(dst)`, `ToSeq(S)`). At
  runtime `ToSeq` returns `None`; the strip now replaces it with `None`.
- **Separate lemmas** for each invariant: `add_state` with all of them inline timed out. Split, each
  lemma takes 8–11 s alone.

**Speed** (contracts stripped, start = state 0, random automata with 10 events, best of 3):

| n | T | reached | verified `reachable` | plain Python BFS (same encoding) | loop over `next_states` |
|---:|---:|---:|---:|---:|---:|
| 100,000 | 300,000 | 94,106 | 0.073 s | 0.042 s | 0.53 s |
| 200,000 | 1,000,000 | 198,581 | 0.33 s | 0.20 s | 2.83 s |
| 1,000,000 | 3,000,000 | 940,488 | 1.46–1.64 s | 0.96 s | — |

So it runs at 1.5–1.7× the hand-written BFS (the call to `add_state` per new state), and 7–9× faster
than the user-level loop over `next_states`. Linear in n + T, as expected.

## Public API

    reachable(G, states=None, *, witnesses=False) -> List[int]   # or (states, parents)

- `states=None` means the initial states.
- With `witnesses=True` it also returns `parents`: for each reached state, `(predecessor, event)`,
  or `None` for a start state. Following `parents` back gives a shortest word reaching the state.

## Later (not in this step)

- `accessible(G)`: the automaton restricted to `reach` (Ac(G)), renumbered. L and Lm are unchanged
  by Lemma 6 plus a renumbering lemma. Build: trusted; check: verified.
- Coreachability (states that can reach a marked state) needs the reverse transitions: a reverse
  index, built and checked like the active-event index. Then `trim`.
