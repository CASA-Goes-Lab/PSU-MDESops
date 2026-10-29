# Spec: deleting states; accessible, coreachable and trim parts

Status: **reviewed by the user and implemented 2026-10-27** (answers at the end).
- Lean: `Automaton.lean`, `Automaton.IsDeletion` and `IsDeletion.exists_init` (`lake build`
  passes).
- Nagini: `ops_aut/verified_ops/delete.py` (a verified checker; see "As implemented").
- Trusted builder: `core_aut/trusted/delete_states.py`.
- Public (in `ops_aut/basic_ops.py`): `delete_states`, `accessible`, `coaccessible`, `trim`,
  `EmptyAutomatonWarning`.

User plan (2026-10-27): one verified operation, `delete_states`. The three parts (accessible,
coreachable, trim) are built from `reachable` / `coreachable` + `delete_states`, without their own
proofs.

## Math / Lean

Deleting a set D of states keeps K = X \ D and restricts everything to K:

    G \ D = (K, E, f_K, X0 ∩ K, Xm ∩ K),   f_K(x, e) = f(x, e) ∩ K   for x ∈ K

Lean (new, small): `restrict f K` and the automaton `G.deleteStates D`. Nothing else is needed for
the plan. Optional (cheap, a few lines each, if wanted later):
- if K ⊇ Ac(G), then L(G \ D) = L(G) and Lm(G \ D) = Lm(G);
- Ac(G \ D) ⊆ Ac(G).

These would turn "the accessible part keeps the language" from a textbook fact into a proved one.

## Python (verified core, new file `ops_aut/verified_ops/delete.py`)

(Draft: implemented as a verified checker of these lists, not a writer; see "As implemented".)

    delete_states(n, start, evt, dst, init, marked, dele,
                  new_of, old_of, start2, evt2, dst2, init2, marked2, src2)

Inputs: the encoding, and `dele[x]` (bool per state). Outputs (filled lists):

| Array | Size | Meaning |
|---|---|---|
| `new_of` | n | new number of x, or −1 if x is deleted |
| `old_of` | n' | old number of new state i |
| `start2`, `evt2`, `dst2` | n'+1, T', T' | the new transition blocks |
| `init2`, `marked2` | n' | flags copied from the old state |
| `src2` | T' | the old position each new transition came from (witness) |

Postconditions (exact, so `G \ D` is what the lists say):

| Postcondition | Math |
|---|---|
| renumbering | `new_of[x] = −1 ⟺ dele[x]`; `new_of[old_of[i]] = i`; `old_of` increasing (kept states keep their order) |
| flags | `init2[i] = init[old_of[i]]`, `marked2[i] = marked[old_of[i]]` |
| blocks | `blocks_ok(n', start2, T')` |
| sound | for k' ∈ block2(i): `src2[k'] ∈ block(old_of[i])`, `evt2[k'] = evt[src2[k']]`, `dst2[k'] = new_of[dst[src2[k']]] ≥ 0` |
| complete | for k ∈ block(x), x and dst[k] kept: some k' ∈ block2(new_of[x]) has `src2[k'] = k` (given by a second witness array, as `pos` in the reverse index, to avoid counting) |
| order | `src2` increasing within each block (keeps each block sorted by event) |

Cost O(n + T), one pass. Events, Euc, Euo are unchanged (the alphabet stays, even for events with
no transitions left).

## The result must be valid: initial states (W3)

(W3) says: an automaton has an initial state exactly when it has states. Deleting every initial
state while other states remain breaks this, so the result could not be a `ValidAutomaton`.
**Question 2** below.

How the result becomes a `ValidAutomaton` (**question 3**):
- **(a) run the verified checker on the result** (recommended to start): no new proof, costs
  one more check pass, O(n' + T');
- (b) prove that `delete_states` keeps validity (ranges, blocks, sorted, deterministic): no extra
  pass, but proving "sorted" is kept needs a proof by induction (the hard kind in `reach.py`).

(a) first; (b) later if the extra pass matters.

## Public API (in `ops_aut/basic_ops.py`)

    delete_states(G, states)  -> ValidAutomaton
    accessible(G)             = delete_states(G, X \ reachable(G))
    coaccessible(G)           = delete_states(G, X \ coreachable(G))
    trim(G)                   = delete_states(G, X \ (reachable(G) ∩ coreachable(G)))

(Names as answered in question 4; the draft had `accessible_part`, `coreachable_part`.)

- `G`: an `Automaton` or a `ValidAutomaton` (validated inside the call when plain, as now).
- State names are kept; states are renumbered in their old order.
- Trim needs one deletion, not two: from a reachable state, every path stays among reachable
  states, so "coreachable in Ac(G)" = "coreachable in G" for those states.
- Correct by composition: the verified postconditions of `reachable`/`coreachable` give the
  set, and those of `delete_states` give the restriction. The glue (forming X \ R) is a few trusted
  lines.

## Memory (the user's concern)

`ValidAutomaton` is read-only (so "valid" can never go stale, and its cached indexes stay right),
so deleting gives a new object. Options:

| Option | Memory | Cost |
|---|---|---|
| **(A) new ValidAutomaton** (recommended) | during the call: old + new; after `V = delete_states(V, S)` the old one is freed at once (Python frees an object when its last reference goes), with its cached indexes | none extra |
| (B) delete in place in a plain `Automaton` | no second copy | the result must be validated again before any verified operation; renumbering is O(n + T) anyway |
| (C) a "deleted" mask over the same encoding (a view, no copy) | n bools | every operation (verified ones included) must learn to skip masked states: a large change |

With (A), memory only grows if the program keeps the old automata in variables. Repeated
deletions can also be merged into one call: `delete_states(V, S1 | S2 | S3)` copies once.

## As implemented

Differences from the draft above:
- **A verified checker, not a verified writer.** Trusted code builds the result lists
  (`build_delete`) and the verified `check_delete` accepts them only if the postconditions above
  hold; otherwise the call raises. The guarantee is the same (a wrong result is rejected, never
  returned), and it follows the pattern of the two indices. Why: the checker proofs reuse the
  patterns of `verified_core/reverse_index.py` (read-only lists, "done up to (x, k)" invariants),
  while a writer needs facts about growing lists, the hard part of `reach.py`.
- **Lean:** `IsDeletion G D G' old` states the result for any renumbering `old` (strictly
  increasing, onto the kept states; `y ∈ f'(i, e) ↔ old y ∈ f(old i, e)`; the flags; the events
  unchanged). `IsDeletion.exists_init`: if `G'` has a state, some initial state of `G` is kept,
  so deleting every initial state can only give the empty automaton (why question 2's answer is
  forced by (W3)).
- **The facts checked** (`delete.py`; its docstring shows by hand how they give `IsDeletion`):
  `renum_ok` (new_of/old_of inverse on the kept states), `order_ok` (old_of increasing),
  the flag fact (for init and marked), `trans_ok` (each new transition copies `src2[k']`, with its
  event and its renamed target; `pos2[src2[k']] = k'`), the own2 fact (it copies a transition out of
  `old_of[i]`), `pos2_ok` (pos2 points back), `keep_ok` (every old transition between kept
  states is copied, into the block of its source); plus `blocks_ok` for `start2`. The "order"
  postcondition of the draft was dropped: the validity check of the result checks that blocks are
  sorted.
- **Empty result:** decided by trusted code before building: if no initial state is kept, the
  result is the empty automaton (0 states, same events) and an `EmptyAutomatonWarning` is issued
  (user, question 2). Otherwise the copied flags (verified) keep an initial state, and the
  validity check confirms (W3).
- **Validation of the result:** `validate_encoded` (trusted wrapper, new) runs the verified
  `check_automaton`, deterministic check first: one pass if the result is deterministic, two if not
  (as `validate(G)`, which always runs two). Recorded cost below (user: keep a record of this
  pass; if it matters, prove that deletion keeps validity instead).

**What it took (Nagini lessons, 2026-10-27):**
- bools: `==` between two bool reads, and a pure function whose quantifier reads bool lists, did
  not verify (Nagini boxes bools as objects). The flag fact is stated as two implications
  (`f2[i] → f[od[i]]`, `f[od[i]] → f2[i]`), over the lists, triggered on the int read `od[i]`
  (a bool read as trigger failed), and written out in full in the contracts (no pure function);
- the own2 fact could not be folded into a pure function either (the formula verified, the
  function application did not; its conclusion applies `in_blk`): written out in full too;
- a nested loop whose outer termination measure reads a list length (`len(old_of) - i + 2`)
  failed the termination check; a variable (`n2 = len(old_of)`) fixed it;
- moving an inner loop into its own method, with a postcondition at a fixed `i`
  (`in_blk(st2, i, l)`), did not match the caller's `in_blk(st2, z, l)` with `z = i` (ints are
  objects); stating it with a free `z` and `z == i` matched, but verified only sometimes for
  `check_own2`, so `check_own2` keeps the two nested loops in one method, shaped like
  `check_own` in `reverse_index.py`;
- `order_ok`'s trigger `od[i+1]` also matches the body's `od[i]` one index lower (a matching
  loop); it is triggered on the pair `od[i], od[i+1]`.

## Questions for review

1. Memory: option (A), a new `ValidAutomaton` each time? **Answered (user, 2026-10-27): yes.**
2. Deleting all initial states while other states remain: (a) raise `ValueError`; (b) return the
   empty automaton (0 states; its languages are ∅ anyway, since no state is reachable). For
   `coreachable_part`, this happens when the initial state is blocking; textbooks then call
   CoAc(G) empty. Proposal: (b) for `coreachable_part` and `trim`; (a) for a direct
   `delete_states`. **Answered (user, 2026-10-27): return the empty automaton, with a warning
   that the procedure returned an empty automaton** (for all four functions).
3. Validity of the result: (a) run the verified checker on it (no new proof)? **Answered (user,
   2026-10-27): yes, and keep a record of this extra pass; if scalability is an issue, look at the
   proof (b).**
4. Names: `coreachable(G)` already returns the list of states, so the automata versions need other
   names. Proposal: `accessible_part`, `coreachable_part`, `trim`. Alternatives: `ac`, `coac`,
   `trim` (textbook) or `accessible`, `coaccessible`, `trim`. **Answered (user, 2026-10-27):
   `accessible`, `coaccessible`, `trim`.**
5. Should `delete_states` also return the renumbering (`new_of`) on request
   (`return_map=True`), so the caller can move results computed on G to the new automaton?
   **Answered (user, 2026-10-27): no.** (One deletion for trim: fine.)

## Planned (deferred): prove that deletion keeps validity

Status: **draft, deferred** (user, 2026-10-29). Not to be worked on now. It is a **priority once
the tool is more complete** (parallel, product, supervisor, ...). This is option (b) of
question 3.

### The scalability issue

The verified `delete_states` costs about 14–17× plain deletion, and the gap stays a fixed multiple
as the size grows (both are O(n + T)). Most of it is the validity pass on the result. Measured
2026-10-27 (random, 10 events, 0.1% marked; the total is the sum of the parts, measured
separately):

| | n=200k, T=1M | n=1M, T=3M |
|---|---:|---:|
| plain deletion, no checks | 0.29 s | 1.19 s |
| builder (trusted) | 0.32 s | 1.28 s |
| exactness check (`check_delete`) | 1.17 s | 4.18 s |
| validity check of the result (2 passes: nondeterministic) | 3.37 s | 11.21 s |
| verified `delete_states`, total | ≈ 4.9 s (17×) | ≈ 16.7 s (14×) |

`trim` pays the same validity pass (19.85 s total at n=1M with the reverse index cached).

### The idea

The builder already writes a valid automaton (kept states in order, each block copied in its
order). It is trusted, though, so that is not known. Validity of the result does not need a
second pass: it follows from the validity of G (G is a `ValidAutomaton`) and the facts
`check_delete` already checks, plus one more.

| Condition of `valid_automaton` (`check.py`) | Where it comes from |
|---|---|
| `blocks_ok(n', start2, T')` | already checked by `check_delete` |
| `transitions_ok`: `evt2[k']` an event of E | `evt2[k'] = evt[src2[k']]` (`trans_ok`) and `transitions_ok` for G |
| `transitions_ok`: `dst2[k']` a state of G' | `dst2[k'] = new_of[dst[src2[k']]] ≥ 0` (`trans_ok`) and `renum_ok` (a kept state's new number is < n') |
| `events_ok` | E, Euc, Euo unchanged |
| `sorted_ok` | **new fact** (below) and `sorted_ok` for G |
| `det_ok` (if G is deterministic) | the new fact with strict order, and `det_ok` for G |
| `init_ok` | the flag fact (`init2[i] ⟺ init[old_of[i]]`); deterministic G has at most one initial state |
| (W3) | empty result decided up front; otherwise the flag fact keeps an initial state (`IsDeletion.exists_init`) |

**New fact (the "order" postcondition dropped from the draft):** within each new block,
`src2` increases:

    ∀ i ∈ [0, n'), ∀ k' with start2[i] ≤ k' < k'+1 < start2[i+1]:  src2[k'] < src2[k'+1]

Checked on neighbours only (one linear pass, like `check_block_sorted`).

### What it would take

1. `check_order2` in `verified_ops/delete.py`: the neighbour check above, with a loop invariant
   turning it into the pairwise statement (pattern: `check_block_sorted` in `check.py`).
2. A lemma `delete_keeps_valid`: `valid_automaton(G)` ∧ exactness facts ∧ order of `src2` ⟹
   `valid_automaton(G')`, one sub-lemma per condition of the table (lesson from `reach.py`:
   one lemma per invariant).
3. **The hard part:** `sorted_ok` / `det_ok`. From "`src2` increases in block i" and "all
   `src2[k']` of block i lie in block `old_of[i]`" (own2), conclude
   `evt[src2[j]] ≤ evt[src2[k]]` for j < k in block i, using G's `block_sorted` at
   `old_of[i]`. Watch for matching loops (`src2[k']` against `src2[k'+1]`, as `order_ok`).
4. `delete_states` then skips `validate_encoded`; it would cost about 4.6× plain
   (≈ 1.28 + 4.18 s at n=1M).

### Open point for later

If G is nondeterministic, the result may become deterministic (only the duplicates deleted).
Validity still holds (nondeterministic stays allowed). Options: keep G's flag (no extra cost), or
compute it with one strict-order pass per block (cheap). To decide when this is picked up.

### Related deferred item (user, 2026-10-29)

Same priority list: **parallel / product, DFA in ⇒ DFA out proved** (`parallel.md`, question 4,
option (a): distinct labels + `det_of_labels`), so the validity pass on a composition can skip
its determinism check. For now the validity pass decides it (option (b)); the user expects (a)
to be needed for scalability.
