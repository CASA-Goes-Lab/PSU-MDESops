# certisc-proof

Lean 4 proofs of the algorithms implemented in [`certisc`](../certisc-lib/).

## Install

1. Install [elan](https://github.com/leanprover/elan), the Lean version manager:

       $ curl https://elan.lean-lang.org/elan-init.sh -sSf | sh

   It puts `lean` and `lake` in `~/.elan/bin`; add that to `PATH`. elan picks the Lean version
   from `lean-toolchain`.
2. From this folder:

       $ lake exe cache get    # prebuilt Mathlib, about 7 GB in .lake/
       $ lake build

Lean and Mathlib are pinned in `lean-toolchain` and `lakefile.toml` (both v4.35.0). In VS Code,
install the `lean4` extension and open this folder. CI: `.github/workflows/proof.yml`.

This is a Lean project, not a Python package. `lakefile.toml` plays the role that
`pyproject.toml` plays for Python, and there is nothing to `pip install`.

## Layout

    certisc-proof/
    ├── lakefile.toml, lean-toolchain   Lean project (depends on Mathlib)
    ├── DESopsProof.lean                imports every module below
    ├── DESopsProof/                    one module per topic: Automaton.lean (definitions + lemmas)
    └── spec/                           automaton.md, wrapper.md, then one note per operation:
                                        the Lean definition next to the Nagini postcondition

How the two layers fit together:
- The Lean proof shows that the algorithm is correct.
- The Nagini proof in `certisc-lib/src/` (`core_aut`, `ops_aut`) shows that the Python code computes exactly the
  construction defined in Lean.
- The note in `spec/` records that the two definitions match (checked by hand for now).
