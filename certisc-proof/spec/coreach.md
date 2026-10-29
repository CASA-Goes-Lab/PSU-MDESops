# Spec: coreachable states

Status: **implemented and verified 2026-10-27; all four questions answered by the user
(2026-10-27): implemented as proposed** (the user approved going ahead after the Lean write-up and was away, so the
proposed defaults were implemented; each is easy to change).
- Lean: `Automaton.lean`, section "Coreachability certificates" (`lake build` passes, standard
  axioms only).
- Nagini: `core_aut/verified_core/reverse_index.py` (about 15 s),
  `ops_aut/verified_ops/coreach.py` (about 16–19 s for the whole file, which re-verifies the
  imported `reach.py` and `check.py`).
- Public: `ops_aut.coreachable` (in `ops_aut/basic_ops.py`).

Layout (user, 2026-10-27): the public function goes in `ops_aut/basic_ops.py`; the verified code
goes in a new file `ops_aut/verified_ops/coreach.py`.

## Math / Lean

A state is coreachable if some word leads from it to a target state (default: the marked
states):

    CoAc(f, Xm) = { x | ∃ s ∈ Σ*, f*({x}, s) ∩ Xm ≠ ∅ }            Lean (new): coreach f Xm

The same shape as reachability, with the transitions read backwards. New Lean lemmas, mirroring
R1/R2 (about the same size):

| Lemma | Statement | Used for |
|---|---|---|
| C1 (closure, least) | if Xm ⊆ R and R is backward closed (`y ∈ f x e ∧ y ∈ R → x ∈ R`), then `coreach f Xm ⊆ R` | **complete** |
| C2 (witness order) | if each `out[i]` is in Xm or has a transition **to** some `out[p]`, `p < i`, then every `out[i] ∈ coreach f Xm` | **sound** |

plus `coreach_eq_of_certificate`. No reversed automaton is needed in Lean; the lemmas talk about
f directly.

## The missing piece: reverse transitions

The encoding stores the transitions grouped by **source** (block(x)). Going backwards needs them
grouped by **target**. Without that, the only option is to repeat forward passes until nothing
changes: O(n·T) in the worst case. With it, backward breadth-first search is O(n + T).

**Proposal: a reverse index, built like the active-event index** (trusted builder, verified
checker, cached lazily on `ValidAutomaton`):

| Array | Size | Meaning |
|---|---|---|
| `rstart` | n+1 | rblock(y) = [rstart[y], rstart[y+1]): the transitions **into** y |
| `rk` | T | rk[j] = a forward transition position k (with dst[k] = y for j ∈ rblock(y)) |
| `rsrc` | T | rsrc[j] = the source state of transition rk[j] |
| `pos` | T | pos[k] = where transition k sits in rk (the inverse) |

Checker (verified, one linear pass, no sorting):
- **sound:** `blocks_ok(n, rstart, T)`; for j ∈ rblock(y): `rk[j] ∈ block(rsrc[j])` and `dst[rk[j]] = y`;
- **complete:** for each x and k ∈ block(x): `pos[k] ∈ rblock(dst[k])`, `rk[pos[k]] = k`,
  `rsrc[pos[k]] = x`.

Storing `pos` avoids a counting argument (no "|rk| = T, no repeats, so every k appears"). This is
the same lesson as in `reach.py`, where counting was the hardest part.

- Files: builder `core_aut/trusted/reverse_index.py`; checker
  `core_aut/verified_core/reverse_index.py`; a `_reverse` slot on `ValidAutomaton`, as `_active`.
- Cost: 4 arrays (n+1 + 3T ints), built once per `ValidAutomaton`. For a plain `Automaton` it is
  built and checked on every call, like the validation itself.
- Reuse: later operations that go backwards (supervisor synthesis, trim) use the same index.

## Python (verified core)

    coreachable(n, start, dst, rstart, rk, rsrc, pos, Xm, mark, out, nxt, via)

**Proposal: reuse the verified `reach.reachable`** on the reverse index: the reverse encoding is
(`rstart`, `rsrc`), and "reachable backwards from Xm" is coreachable. `coreach.py` then only
translates the results back to forward terms, using the checker's facts. The breadth-first proof
is not repeated.

| Postcondition | Math |
|---|---|
| in range, no duplicates | as `marks_ok` |
| contains Xm | `∀ j: mark[Xm[j]] ≥ 0` |
| backward closed | `∀ x, k ∈ block(x): mark[dst[k]] ≥ 0 → mark[x] ≥ 0` |
| witnesses (sound) | `∀ i: (nxt[i] = −1 → Xm[via[i]] = out[i]) ∧ (nxt[i] ≠ −1 → 0 ≤ nxt[i] < i ∧ via[i] ∈ block(out[i]) ∧ dst[via[i]] = out[nxt[i]])` |
| size | `|out| ≤ n` |

Match with Lean: contains Xm + backward closed + C1 give ⊇; witnesses + C2 give ⊆.

Witnesses now point **forward**: `nxt[i]` is the next state on a shortest path from `out[i]` to
a target state, and `via[i]` the transition taken. Following them gives a shortest word from
each state to a marked state (useful to explain why a state is not blocking).

## Public API (in `ops_aut/basic_ops.py`)

    coreachable(G, states=None, *, witnesses=False, backend="verified")

- `states=None` means the marked states; any target states can be given (as for `reachable`).
- With `witnesses=True` it also returns `nexts`: for each state, `(event, next_state)`, or `None`
  for a target state. Following them gives a shortest word to a target.

## As implemented

Differences from the draft above:
- `in_blk` (k ∈ block(x)) moved to a new module `core_aut/verified_core/blocks.py` (adding it
  to `check.py` made `check_blocks` fail to verify), shared by `reach.py`, `reverse_index.py` and
  `coreach.py`, so facts from the three files use the same function (the trigger of the nested
  quantifiers). `reach.py` re-verified (19–30 s).
- `ops_aut/py.typed` added (and listed in `pyproject.toml`), so Nagini can read the import of
  `reach.py` from `coreach.py`.
- The witness via[i] is a **reverse** position; the forward transition is `rk[via[i]]`. The
  postcondition says so (`out[i] --_{rk[via[i]]}--> out[nxt[i]]`); the public layer reads the
  event as `evt[rk[via[i]]]`. No extra loop to convert.
- `coreachable` takes 3/4 permission of `rstart`, `rsrc`, `Xm` (the search takes 1/2): keeping a
  share is what lets Nagini know they are unchanged after the call.
- At runtime, the stripped `coreach.py` would call the *unstripped* `reach.reachable` through its
  import; `basic_ops.py` rebinds it to the stripped one (one trusted line, listed in
  VERIFICATION.md §6).

**Proof structure:**
- `check_reverse` = `check_blocks` on rstart + four checkers, one per fact (`check_src`,
  `check_tgt`, `check_pos`, `check_own`). The nested ones (tgt, own) use "done up to (y, j)"
  invariants, like `closed_upto` in reach.py, but simpler: the order is by state number, so no
  lemmas were needed.
- `coreachable` = one call to `reach.reachable` + two lemmas: `co_closed_from` (pos_ok + own_ok
  turn the reversed `closed_all` into `co_closed`) and `co_wit_from` (src_ok + tgt_ok turn the
  reversed `wit_ok` into `co_wit_ok`). Each lemma is one quantified `Assert` that writes out the
  intermediate terms (`pos[k]`, `in_blk(rst, dst[k], pos[k])`, `rsrc[v[i]]`) so the triggers fire.

**What it took:** only the known lessons. Invariants must read `ToSeq(l)[i]` (not `l[i]`) when the
predicate they must match uses sequences; and in an `Assert` of `blocks_ok`'s facts, the trigger
term `start[x + 1]` must come first. One full run of `coreach.py` hung (killed after 15 min); the
three methods alone took 10–13 s each, and every later full run took 16–19 s. Not explained;
recorded here in case it recurs.

**Speed** (contracts stripped, random automata with 10 events, 0.1% of states marked, best of 3):

| n | T | coreachable | first call (builds + checks index) | index cached | plain backward BFS (with predecessor lists) | `reachable` |
|---:|---:|---:|---:|---:|---:|---:|
| 200,000 | 1,000,000 | 198,599 | 1.96 s | 0.30 s | 0.31 s | 0.31 s |
| 1,000,000 | 3,000,000 | 940,486 | 9.01 s | 1.45 s | 2.60 s | 1.44 s |

Index alone: build 0.38 s / 1.60 s; build + verified check 1.67 s / 7.30 s. So with the index
cached, `coreachable` costs the same as `reachable` and no more than a plain backward search
(which must build its predecessor lists every time). The first call on a `ValidAutomaton`, and
every call on a plain `Automaton`, pays for the index, and mostly for its checker (about 3.5× the
build). Not optimised yet; the nested checkers (`check_tgt`, `check_own`) are the likely cost.

## Questions for review

Implemented as proposed in each case.

1. Targets: any states, defaulting to the marked states (as `reachable` defaults to the initial
   states)? **Answered (user, 2026-10-27): yes; any targets, the default is always the marked
   states.**
2. Witnesses as above: `(event, next_state)` toward the target? **Answered (user, 2026-10-27):
   yes, as in reach.**
3. Approach: reverse index (cached and checked, like the active-event index) plus reuse of the
   verified `reachable`? The alternative is a separate backward search proof in `coreach.py`,
   which would repeat most of `reach.py`. **Answered (user, 2026-10-27): keep the reuse of
   reach.**
4. Only the coreachable set in this step (`trim` later)? **Answered (user, 2026-10-27): yes;
   next step is the accessible and coreachable part of an automaton (trim).**
