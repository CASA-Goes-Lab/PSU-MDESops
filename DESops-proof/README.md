# DESops-proof

Lean 4 proofs of the algorithms implemented in [`DESops-lib`](../DESops-lib/).

## Setup

1. Install [elan](https://github.com/leanprover/elan), the Lean version manager. It puts `lean` and `lake` in `~/.elan/bin`; add that to `PATH`.
2. From this folder: `lake exe cache get` (downloads prebuilt Mathlib, about 7 GB in `.lake/`), then `lake build`.

The Lean and Mathlib versions are pinned in `lean-toolchain` and `lakefile.toml` (currently v4.35.0 for both).
CI: `.github/workflows/proof.yml` at the repository root.

## Layout

    DESops-proof/
    ├── lakefile.toml, lean-toolchain   Lean project (depends on Mathlib)
    ├── DESopsProof.lean                imports every module below
    ├── DESopsProof/                    one module per topic: Automaton.lean (definitions + sanity lemmas), Parallel.lean next
    └── spec/                           automaton.md (definitions), wrapper.md (encoding + verified checker), then one note per operation: the Lean definition side by side with
                                        the Nagini postcondition of its Python implementation

How the two layers fit together:
- The Lean proof shows that the algorithm is correct. For example, the language of the parallel
  composition equals the intersection of the inverse projections.
- The Nagini proof in `DESops-lib/DESops/verified/` shows that the Python code computes exactly the
  construction defined in Lean.
- The note in `spec/` records that the two definitions match. For now a person checks this by hand.
