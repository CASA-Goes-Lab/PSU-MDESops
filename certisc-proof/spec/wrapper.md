# Spec: the wrapper around verified code

**Layout B (2026-10-21):** `encode` writes each state's transitions sorted by event number (ties by target). `check_automaton` verifies it (`sorted_ok`, error code 8, checked right after code 2), so a validated automaton guarantees it.

Status: **implemented 2026-10-16** in `legacy/DESops-lib/DESops/verified/`. The checker verifies with Nagini (`nagini DESops/verified/check.py`, about 15 s).

**Moved 2026-10-20:** the verified code now lives in the standalone package `certisc` (`certisc-lib/src/`, top-level packages `core_aut` (checker, encoding, wrapper) and `ops_aut` (parallel)). It no longer depends on the old library. The old library, including its own copy of `DESops/verified/` and `Automaton.validate()`, is in `legacy/DESops-lib/`. In `certisc`, the entry point is `check_or_raise(G, deterministic=False)`, applied to `certisc.Automaton`, a plain data container with the same fields as the old class. It has no `_valid` flag. Section 8 lists the current files. The rest of this note describes the design as it was implemented in the old library.

Every verified operation (`validate`, later `parallel`, ...) runs inside the same wrapper. The
wrapper moves an `Automaton` into plain lists that Nagini can reason about, calls the verified
code, and moves the result back. This document describes the wrapper, which parts of it are trusted
(not proved), and the verified validity checker.

Related: [automaton.md](automaton.md) (the definition of a valid automaton, decisions 1–9).

## 1. Trust boundary

```
Automaton (class, unchanged)
   │
   ├─ event table            trusted   §3
   ├─ encoding               trusted   §4
   │
   ├─ validity checker       VERIFIED (Nagini)   §5
   ├─ operation core         VERIFIED (Nagini)   e.g. parallel, later
   │
   ├─ decoding               trusted   §4
   ▼
Automaton (result)
```

- **Verified:** Nagini proves the code meets its contract for every input that satisfies the
  precondition.
- **Trusted:** short code we rely on without proof, kept to plain copying with no logic, and tested
  instead (§7).

The `Automaton` class does not change. You keep building automata by hand or by reading files. The
encoding exists only while verified code runs.

## 2. When it runs

An automaton is **validated** when its flag `_valid` is set. That happens in one of three ways:

| Source | How it becomes valid | Check runs? |
|---|---|---|
| Built by hand, or read by today's readers (`.fsm`, CIF) | `G.validate()` runs the verified checker (§5) and sets the flag if `G` passes | once |
| A verified reader (future) | its proof guarantees a valid result; it sets the flag | no |
| Output of a verified operation | its postcondition guarantees a valid result (and a DFA when the inputs were DFAs); the flag is set | no |

**Rules:**
- **Methods clear the flag.** Any mutating method of `Automaton` clears it (decision 7, A1). Direct edits
  of `init`, `events`, `Euc`, `Euo`, `marked` or `out` after validation are unsupported.
- **Unvalidated input is validated automatically.** A verified operation that receives an automaton
  without the flag validates it first and raises if it is invalid (decision 9).

**Example, `parallel(G1, G2)`:**
1. Validate `G1` and `G2` if their flags aren't set; raise if invalid.
2. Build one event table for both (§3), and encode both (§4).
3. Run the verified `parallel` core on the encodings.
4. Decode the result into a new `Automaton`, and set its flag.

## 3. Event numbering (trusted)

The verified code works on integers `0..m−1`. The wrapper builds one `dict` for **all** inputs of the
operation together:

```python
table = {}
for G in inputs:
    for e in G.events | G.Euc | G.Euo | {e for st in G.states for e in st.out}:
        table.setdefault(e, len(table))
event_of = list(table)        # number -> event, for decoding
```

- **Events used in transitions are included.** A transition whose event is missing from
  `G.events` (a W1 violation) then reaches the verified checker, which rejects it. Without this, it
  would fail with a `KeyError` in the wrapper.
- **"Same event" keeps today's meaning.** Two events get the same number exactly when Python treats
  them as the same `dict` key (`==`, and equal hashes). That is the test the unverified code uses too
  (`shared = G1.events & G2.events`):
  - `"a"` and `Event("a")` are different events.
  - `Event("a")` and `Event("a", foo=1)` are different, because `Event.__eq__` compares attributes.
  - `1`, `1.0` and `True` are the same event.
- **The numbering order doesn't matter.** The result is decoded with the same table, and the proofs
  only use "same number ⟺ same event".

## 4. Encoding and decoding (trusted)

**Grouped by state.** Each state's transitions are stored side by side, and `start` says where each
state's block begins:

| Field | Type | Meaning |
|---|---|---|
| `n` | `int` | number of states |
| `m` | `int` | number of events in the table |
| `in_E`, `in_Euc`, `in_Euo` | `List[bool]`, length `m` | `in_E[e]` iff event `e` ∈ `E`, and so on |
| `init` | `List[bool]`, length `n` | `init[x]` iff `x ∈ X0` |
| `marked` | `List[bool]`, length `n` | `marked[x]` iff `x ∈ Xm` |
| `start` | `List[int]`, length `n + 1` | state `x` owns positions `start[x] … start[x+1] − 1` |
| `evt`, `dst` | `List[int]`, one entry per transition | position `k` is the transition `x —evt[k]→ dst[k]` |

**Example** (produced by running the code below on a real `Automaton`):

```
->  0 x0: {'a': [1], 'b': [2]}          table: a → 0, b → 1
    1 x1: {'a': [0]}
  * 2 x2: {}
```

| position | belongs to | `evt` | `dst` | meaning |
|---|---|---|---|---|
| 0 | x0 | 0 | 1 | x0 —a→ x1 |
| 1 | x0 | 1 | 2 | x0 —b→ x2 |
| 2 | x1 | 0 | 0 | x1 —a→ x0 |

```
start  = [0, 2, 3, 3]      x0: positions 0–1, x1: position 2, x2: none (3 to 3)
evt    = [0, 1, 0]
dst    = [1, 2, 0]
init   = [True, False, False]
marked = [False, False, True]
```

**Encoding code:**

```python
start, evt, dst = [0], [], []
for state in G.states:                          # in index order
    for event, targets in state.out.items():
        for t in targets:
            evt.append(table[event])
            dst.append(t)
    start.append(len(evt))                      # this state's block ends here
```

**Two checks happen here,** because the lists cannot represent the violation:
- **`marked` must be `bool`** (decision 4). The encoder raises if `type(state.marked) is not bool`.
- **`init` indices must be states.** The encoder raises if an index in `G.init` is outside `0..n−1`.

**Decoding** is the same loop in reverse: for each state `x` and each position `k` in its block,
`add_transition(x, event_of[evt[k]], dst[k])`. States, marking and `init` are copied back the same way.
Names are rebuilt by the operation's wrapper (e.g. `(name1, name2)` for `parallel`).

## 5. The validity checker (verified)

**Contract:** `check(...)` returns `True` **exactly when** the encoding satisfies
`valid_automaton(...)`, or `valid_dfa(...)` when a DFA is required. Both predicates are written in
Nagini's specification language, and are the list form of (W1)–(W3) and determinism from
`automaton.md` §3.

| Condition | `valid_automaton` | `valid_dfa` adds |
|---|---|---|
| Lengths | `len(in_E) = len(in_Euc) = len(in_Euo) = m`; `len(init) = len(marked) = n`; `len(start) = n + 1`; `len(evt) = len(dst)` | |
| Block layout | `start[0] = 0`; `start[x] ≤ start[x+1]`; `start[n] = len(evt)` | |
| Ranges | `0 ≤ evt[k] < m`, `0 ≤ dst[k] < n` | |
| (W1) | `in_E[evt[k]]` for every `k` | |
| (W2) | `in_Euc[e] ⇒ in_E[e]`, `in_Euo[e] ⇒ in_E[e]` | |
| (W3) | some `init[x]` ⟺ `n > 0` | at most one `init[x]` |
| Determinism | | no event twice in one state's block |

Every condition except determinism is a direct single pass over a list.

Duplicate transitions are allowed in `valid_automaton`, since `f(x, e)` is a set and a repeat
changes nothing. The class refuses them anyway. In `valid_dfa` they are caught as "event twice in
one block".

### Determinism: scan each block

**Question:** within one state's block, does any event number appear twice?

```python
for x in range(n):                       # check_det
    lo, hi = start[x], start[x + 1]
    for k in range(lo, hi):              # check_block
        for j in range(lo, k):           # compare with the earlier positions of the same block
            if evt[j] == evt[k]:
                return False             # state x has event evt[k] twice
return True
```

**Trace: the example above** (`start = [0, 2, 3, 3]`, `evt = [0, 1, 0]`):

| x | block | k | compared with | result |
|---|---|---|---|---|
| 0 | positions 0–1 | 0 | (nothing) | ok |
| 0 | | 1 | position 0: `1 ≠ 0` | ok |
| 1 | position 2 | 2 | (nothing; position 0 is in x0's block) | ok |
| 2 | empty | | | |

Result: `True`. Event `a` occurs in x0 and x1, which is allowed: blocks are never compared with each other.

**Trace: nondeterministic variant,** x0 = `{'a': [1, 2], 'b': [2]}`, so `start = [0, 3, 4, 4]` and `evt = [0, 0, 1, 0]`:

| x | k | compared with | result |
|---|---|---|---|
| 0 | 0 | (nothing) | ok |
| 0 | 1 | position 0: `0 = 0` | **return False** |

**Cost.** It looks quadratic but isn't in practice. A block with no repeated event has at most one
entry per event, and the scan stops at the first repeat, so it never goes past `m + 1` positions
of a block. The total is at most `transitions × min(largest out-degree, m + 1)` comparisons.
Automata usually have small out-degrees.

**Why not the `last[e]` list** (one pass, the version agreed first): its proof did not go through.
It needs facts that chain `pos[evt[j]]` and `evt[pos[e]]`, and Z3 did not finish within 4–8 minutes
in five reformulations (explicit triggers, a per-block helper, an invariant without nesting, a
single verifier thread). The block scan verified in about 10 s on the first try. Details in
`doc/logs/formal-verification.md`.

**What is proved,** with the contracts in `check.py`:
- `check_block(evt, lo, hi)` returns `True` exactly when `block_det(lo, hi, evt)`: no two
  positions in `lo … hi−1` carry the same event.
- `check_det` returns `True` exactly when `det_ok`: `block_det` holds for every state's block.

### Cost of the whole check

Measured 2026-10-16 (Python 3.13, random DFAs with 5 events and density 0.6, best of 3). Columns:
- `encode`: the trusted copy into lists;
- `check` / `check DFA`: `check_automaton` without / with determinism;
- `validate DFA`: `Automaton.validate(deterministic=True)`, i.e. encode plus check;
- `parallel`: the cheapest possible `parallel`, against a 2-state automaton.

| states | transitions | encode | check | check DFA | validate DFA | parallel |
|---:|---:|---:|---:|---:|---:|---:|
| 1,000 | 3,058 | 0.4 ms | 2.6 ms | 7.1 ms | 7.5 ms | 4 ms |
| 10,000 | 30,108 | 3.7 ms | 25.5 ms | 71.2 ms | 74.9 ms | 52 ms |
| 100,000 | 300,228 | 39.2 ms | 260.1 ms | 748.8 ms | 764.7 ms | 1,080 ms |

**Most of this is the contract calls themselves.** `Invariant(...)` and the rest are no-ops, but
Python still calls them, and builds their `lambda` arguments, on every loop iteration. The same
`check_automaton` with the contract statements removed (an AST transform; same results on these inputs):

| states | with contracts | contracts removed |
|---:|---:|---:|
| 1,000 | 7.2 ms | 0.8 ms |
| 10,000 | 71.5 ms | 8.1 ms |
| 100,000 | 715.0 ms | 79.9 ms |

Removing them at import time would add a small trusted step: an AST pass that deletes statements
of the form `Requires(...)`, `Ensures(...)`, `Invariant(...)`, `Assert(...)`. **Open decision.**
The validated flag already means the check runs at most once per automaton.

## 6. Where each condition is checked

| Condition | Where | Why there |
|---|---|---|
| `marked` is `bool` | encoder (trusted) | the `bool` list can't hold anything else |
| `init` indices in range | encoder (trusted) | `init` becomes a `bool` list indexed by state |
| everything in §5 | checker (verified) | |
| `source` of a transition in range | the class (`add_transition`) | the encoding has no `source` field; position in `start` says it |

**Result codes** of `check_automaton`, proved: `0` iff valid, and each nonzero code only when its
condition fails.

| code | condition | message raised by `validate()` |
|---|---|---|
| 1 | sizes (`len(marked) ≠ n`, negative sizes) | sizes |
| 2 | blocks (`start`) | internal encoding error (cannot come from the encoder) |
| 3 | transitions: event range, (W1), target range | W1 |
| 4 | (W2) | W2 |
| 5 | (W3) | W3 |
| 6 | more than one initial state (DFA only) | more than one initial state |
| 7 | an event twice in one block (DFA only) | two transitions with the same event |

## 7. Keeping the trusted parts honest

- **Plain copying only.** The event table, encoder and decoder contain no decisions beyond the two
  checks in §4.
- **Round-trip tests:** `decode(encode(G))` equals `G` (states, `init`, marking, transitions, events,
  `Euc`, `Euo`). Run on all test automata and on random ones. This is a test, not a proof, which is
  the right tool for a pure copy.
- **Rejection tests:** one case per condition in §5 and §6, each built so that exactly that condition fails.

## 8. Files

```
certisc-lib/src/
├── core_aut/                  public layer
│   ├── __init__.py            exports Automaton, State, InvalidAutomatonError, check_or_raise
│   ├── automaton.py           trusted: Automaton / State, a plain data container (no checks)
│   ├── valid.py               ValidAutomaton: read-only, made by validate() after the check
│   ├── py.typed               marker so Nagini (via mypy) reads core_aut when imported
│   ├── trusted/               trusted helpers
│   │   ├── encoding.py        event table, encode (blocks sorted by event), decode
│   │   ├── error.py           InvalidAutomatonError
│   │   ├── wrapper.py         encode, run check_automaton, raise InvalidAutomatonError
│   │   └── _strip.py          removes contracts and lemma calls before running
│   └── verified_core/         internal
│       ├── __init__.py        installs the contract fallbacks first
│       ├── _contracts.py      runtime only: no-op stand-ins if Nagini is not installed, and a
│       │                      no-op `Ensures` if it is (the real one raises when called)
│       └── check.py           VERIFIED: *_ok predicates (the spec) and the checkers
├── io_aut/                    trusted readers/writers: read_aut, write_aut (JSON), read_fsm
└── ops_aut/                   public layer: next_states (basic_ops.py)
    └── verified_ops/          internal
        ├── basic_ops.py       VERIFIED: next_states
        ├── parallel.py        VERIFIED (in progress): parallel composition core
        └── parallel_check.py  VERIFIED: checker for the parallel output (soundness)
```

- **Tests:** `certisc-lib/tests/core_aut/test_check.py`, 16 tests:
  - one rejection per condition;
  - the encoding example of section 4;
  - 200 random round trips;
  - 500 random automata compared with an independent reading of the spec;
  - a run without Nagini.
- The old library's version, with `Automaton.validate()`, the `_valid` flag and its tests
  (`tests/test_verified.py`, 24 tests), is in `legacy/DESops-lib/`.
