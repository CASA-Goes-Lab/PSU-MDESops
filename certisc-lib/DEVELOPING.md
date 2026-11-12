# Developing certisc

For using the library, see [README.md](README.md). This file covers how certisc is built: the
Python packages, the verified Rust core, tests, and proofs. The algorithms themselves are proved
in Lean, in [`../certisc-proof/`](../certisc-proof/). The earlier Python implementation,
verified with [Nagini](https://github.com/marcoeilers/nagini), is kept for reference in
`../legacy/nagini/`.

## Layout

    src/core_aut/                public: Automaton, ValidAutomaton, validate, check_or_raise;
                                 efsm.py: EfsmSystem, Efsm, Edge, Variable, expressions (EFSM
                                 syntax, plain Python; meaning in certisc-proof Efsm.lean)
        trusted/                 trusted helpers: encoding, wrapper, error
    src/rust_core/               internal: only the compiled Rust core, _rs.abi3.so (built by
                                 pip install from rust/; not in git), class RsAut
    src/io_aut/                  public: read_aut, write_aut (JSON), read_fsm (DESUMA import),
                                 read_cif, parse_cif (cif.py: CIF -> EfsmSystem)
    src/ops_aut/                 public (basic_ops.py): next_states, active_events,
                                 active_events_at, reachable, coreachable, delete_states,
                                 accessible, coaccessible, trim, parallel_2aut,
                                 product_2aut
    src/sup/                     public: supervisor (supervisor.py)
    src/viz_aut/                 public: to_dot, write_dot, write_svg, svg (dot.py; Graphviz;
                                 plain Python, not verified)
    tests/                       one folder per package (helper: tests/random_automata.py)
    rust/
        Cargo.toml               workspace (verified, binding)
        verified/                crate certisc_verified: the Verus-verified core, no Python
            src/core_aut/        aut.rs (the automaton and its view, as in Lean), check.rs
            src/ops_aut/         basic_ops.rs, reach.rs, delete.rs, parallel.rs, compose.rs
            src/sup/             supcon.rs (supervisory control), complete.rs (completion)
        binding/                 crate certisc_binding: PyO3 glue (trusted), the extension
                                 rust_core._rs (class RsAut)

## How Python and Rust fit together

`validate` encodes an `Automaton` (`core_aut/trusted/encoding.py`) and hands it to Rust
(`RsAut.from_lists`), whose verified checker (`check_code`) accepts or rejects it. A
`ValidAutomaton` then holds the `RsAut` (`_rs`): the automaton stays in Rust, and the public
functions in `ops_aut/basic_ops.py` call it without checking or encoding again. The Python
encoding is copied back from Rust only when a view needs it (`states[i].out`, `init`, ...).
The public functions keep a `backend=` parameter whose only value is `"rust"`; there is no
pure-Python fallback.

The Rust modules follow the Python packages they serve, but the verified code is one crate:
Verus checks a crate as a whole, and the proofs use each other across modules (deletion uses
the reachability lemmas, the composition uses validity).

Each contract states the Lean definition itself, over the view `g@` (an `AutView`, like Lean's
`Automaton`). The flat storage (`start`, `evt`, `dst`) is the encoding of
`core_aut/trusted/encoding.py`. Every verified file starts with a glossary, and every contract,
invariant and line has a **Math:** / **Why:** comment.

## Build

From the repository root (Python 3.11+, Rust from https://rustup.rs; Verus is not needed):

    python3 -m venv .venv
    .venv/bin/pip install -e "certisc-lib[dev]"

The build backend is [maturin](https://www.maturin.rs). It compiles `binding/` (and
`verified/`, with the proofs erased) and puts `src/rust_core/_rs.abi3.so` in place; the first
build takes about 30 s. Python edits take effect at once; after editing Rust, run the
`pip install -e` line again (or `maturin develop --release` from `certisc-lib/`). The extension
uses the stable ABI (abi3): one wheel per platform for every Python >= 3.11. A released wheel
will need neither Rust nor Verus.

If your shell exports `VIRTUAL_ENV`, maturin installs into that environment: set it to the
venv you mean.

## Test

From the repository root or from `certisc-lib/`:

    .venv/bin/python -m pytest        # 177 passed (Graphviz tests skipped without `dot`)

From the root, `pytest.ini` limits the run to `certisc-lib/tests` (`legacy/` is skipped). CI:
`.github/workflows/tests.yml` (installs Rust, then `pip install` and `pytest`).

## Verify

Needs Verus 0.2026.11.02.8bf68ee (https://github.com/verus-lang/verus/releases) and the Rust
toolchain it asks for (1.99.1). From `certisc-lib/rust/verified/`:

    verus --crate-type=lib src/lib.rs        # 204 verified, 0 errors (about 7 s)

The versions of `vstd`, `verus_builtin` and `verus_builtin_macros` in `verified/Cargo.toml` are
pinned to that release; update them together with Verus. CI: `.github/workflows/verus.yml`.

## What is proved

| Python (ops_aut / core_aut) | Rust function | Contract (Lean definition, over the view `g@`) |
|---|---|---|
| `validate`, `check_or_raise` | `check_code` | 0 exactly when `wf(g)` (and `is_det(g)` if asked); each other code only when its condition fails |
| `next_states` | `next_states` | the result is `step(S, e)`, no repeats, with witnesses |
| `active_events` | `active_events` | the result is `active(S)`, no repeats, with witnesses |
| `reachable` | `reachable` | the result is `reach(S)`, no repeats, each entry with a correct witness |
| `coreachable` | `coreachable` (+ `reverse_index`) | the result is `coreach(S)`, no repeats, with witnesses |
| `delete_states` | `delete_states` | the result is valid and `IsDeletion(g, D, h, old)` (or the empty automaton when no initial state is kept) |
| `accessible`, `coaccessible`, `trim` | same names | `IsDeletion` of the states outside `Ac`, `CoAc`, `Ac ∩ CoAc` |
| `parallel_2aut`, `product_2aut` | `compose_aut` | the result is valid and `IsComposition(par, g1, g2, map2, h, p1, p2)` (`parMode` / `prodMode`) |
| (their agreement check) | `check_agree` | 0 exactly when every shared event has the same controllability and observability in both inputs; else a shared event that differs. `lemma_agree_keeps_flags`: then the output's Euc/Euo equal each input's on that input's events |

| `sup.supervisor` (`method="fast"`) | `supervisor_pc` (+ `bad0`, `keep_events`, `enabled`) | the deleted set is `coreach(uc_part(P0), esc_set)`; then two `is_deletion`s: exactly the hypotheses of Lean's `supervisor_escape_L`, which gives `L(S) = L(P0)↑C` |
| `supervisor(..., construction="refine")` | `complete`, `compose_aut`, `not_label`, `supervisor_sub` | `Hc` is the completion (`comp`); then the deletion hypotheses of Lean's `supervisor_L` with I = the states whose Hc label is not the dump state |
| `supervisor(..., construction="subautomaton")` | `delete_states`, `same_aut`, `supervisor_sub` | H equals G with the states outside I deleted; then the deletion hypotheses of `supervisor_L` |

Not proved: the breadth-first order of `reachable` / `coreachable` (so the witness words are
shortest); it is tested (`tests/ops_aut/test_reach.py`, `test_coreach.py`). For the supervisor:
the link from `G ‖ H` to the plant hypotheses of `supervisor_escape_L` (`L(P0) ⊆ L(G)` and the
enabled-event condition), stated in `certisc-proof/spec/supervisor.md` §9 and tested; for
`construction="refine"`, the completion lemmas `L(G × Hc) = L(G)` and
`L((G × Hc)|I) = L(G) ∩ P_H⁻¹ L(H)` (§10); and
`method="naive"`, which is plain Python.

## Trusted (not proved)

- `rust/binding/src/lib.rs`: the conversion between Python lists and `Aut`, and the checks that
  establish each verified function's `requires` (state indices in range, one flag per state,
  `n1 * n2` fits in 64 bits).
- The Python wrappers (`core_aut/trusted/`, `ops_aut/basic_ops.py`) and the readers and writers
  (`io_aut/`): encoding, event names, state names, and matching the two event tables by name
  for a composition (`map2`; Rust re-checks its shape with the verified `check_map`).
- `reencode` in the binding (the subautomaton construction): H renumbered into G's events and
  state order; its result is only compared with the verified deletion (`same_aut`), so an
  error can only reject H. Readers never decide validity: they build an
  `Automaton` and call `validate`.
- `core_aut/efsm.py` and `io_aut/cif.py`: the EFSM syntax and its check, and the translation
  of CIF into it (which CIF construct means which EFSM). Plain Python; the meaning of an
  `EfsmSystem` is the Lean `sem` in `certisc-proof/DESopsProof/Efsm.lean` (no Rust unfolder
  yet).
- Verus, Z3, and the Rust compiler.

## Adding a package

1. Create `src/<name>/__init__.py`; its verified code goes into `rust/verified/src/<name>/`
   (a module of the same crate), and its binding into `rust/binding/src/lib.rs`.
2. Add `"<name>"` to `python-packages` in `pyproject.toml` (`[tool.maturin]`).
3. Add `tests/<name>/`, then run `pip install -e "certisc-lib[dev]"` again.

Don't use standard-library names such as `io` or `_random`, for packages or test helpers; they
would shadow Python's own modules.
