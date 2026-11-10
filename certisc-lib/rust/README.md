# certisc's Rust core

    rust/
        Cargo.toml          workspace (verified, binding)
        verified/           crate certisc_verified: the Verus-verified core, no Python
            src/core_aut/   aut.rs (the automaton and its view, as in Lean), check.rs
            src/ops_aut/    basic_ops.rs, reach.rs, delete.rs, parallel.rs, compose.rs
        binding/            crate certisc_binding: PyO3 glue (trusted), the extension
                            core_aut._rs (class RsAut)

The modules follow the Python packages they serve, but the verified code is one crate: Verus
checks a crate as a whole, and the proofs use each other across modules (deletion uses the
reachability lemmas, the composition uses validity).

Each contract states the Lean definition itself, over the view `g@` (an `AutView`, like Lean's
`Automaton`). The flat storage (`start`, `evt`, `dst`) is the encoding of
`core_aut/trusted/encoding.py`. Every file starts with a glossary, and every contract, invariant
and line has a **Math:** / **Why:** comment.

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
| (not public yet) | `compose_aut` | the result is valid and `IsComposition(par, g1, g2, map2, h, p1, p2)` |

Not proved: the breadth-first order of `reachable` / `coreachable` (so the witness words are
shortest); it is tested (`tests/ops_aut/test_reach.py`, `test_coreach.py`).

## Build (no Verus needed)

`pip install -e "certisc-lib[dev]"` (from the inner repository root) runs maturin: it compiles
`binding/` (and `verified/`, with the proofs erased) and puts `src/core_aut/_rs.abi3.so` in place.
After changing Rust, run the same command again (or `maturin develop --release` from
certisc-lib/). Needs a Rust toolchain (https://rustup.rs).

## Verify

Needs Verus 0.2026.11.02.8bf68ee (https://github.com/verus-lang/verus/releases) and the Rust
toolchain it asks for (1.99.1). From `rust/verified/`:

    verus --crate-type=lib src/lib.rs        # 164 verified, 0 errors (about 3 s)

The versions of `vstd`, `verus_builtin` and `verus_builtin_macros` in `verified/Cargo.toml` are
pinned to that release; update them together with Verus. CI: `.github/workflows/verus.yml`.

## Trusted (not proved)

- `binding/src/lib.rs`: the conversion between Python lists and `Aut`, and the checks that
  establish each verified function's `requires` (state indices in range, one flag per state,
  `n1 * n2` fits in 64 bits).
- The Python wrappers (`core_aut/trusted/`, `ops_aut/basic_ops.py`): encoding, event names,
  state names.
- Verus, Z3, and the Rust compiler.
