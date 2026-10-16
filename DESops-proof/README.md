# DESops-proof

Lean 4 proofs of the algorithms implemented in [`DESops-lib`](../DESops-lib/). Not set up yet.

Planned layout:

    DESops-proof/
    ├── lakefile.toml, lean-toolchain   Lean project (depends on Mathlib)
    ├── DESopsProof/                    one module per operation, e.g. Parallel.lean
    └── spec/                           one note per operation: the Lean definition side by side with
                                        the Nagini postcondition of its Python implementation

How the two layers fit together:
- The Lean proof shows that the algorithm is correct. For example, the language of the parallel
  composition equals the intersection of the inverse projections.
- The Nagini proof in `DESops-lib/DESops/verified/` shows that the Python code computes exactly the
  construction defined in Lean.
- The note in `spec/` records that the two definitions match. For now a person checks this by hand.
