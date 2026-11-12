# certisc-proof

Lean 4 proofs of the algorithms implemented in [`certisc`](../certisc-lib/).

## Install

1. Install [elan](https://github.com/leanprover/elan), the Lean version manager:

       $ curl https://elan.lean-lang.org/elan-init.sh -sSf | sh

   It puts `lean` and `lake` in `~/.elan/bin`; add that to `PATH`. elan picks the Lean version
   from `lean-toolchain`.
2. From this folder:

       $ lake exe cache get    # prebuilt Mathlib, about 7 GB in .lake/
       $ lake build            # the proofs and the tutorial

Lean and Mathlib are pinned in `lean-toolchain` and `lakefile.toml` (both v4.35.0). In VS Code,
install the `lean4` extension and open this folder. CI: `.github/workflows/proof.yml`.

This is a Lean project, not a Python package. `lakefile.toml` plays the role that
`pyproject.toml` plays for Python, and there is nothing to `pip install`.

## Layout

    certisc-proof/
    ├── Tutorial/                       Lean for beginners: one automaton, its words and languages,
    │                                   math first then Lean step by step (Tutorial/README.md)
    ├── lakefile.toml, lean-toolchain   Lean project (depends on Mathlib)
    ├── DESopsProof.lean                imports every module below
    ├── DESopsProof/                    one module per topic: Automaton.lean (definitions + lemmas),
    │                                   Parallel.lean (composition), Supervisor.lean (supervisory control),
    │                                   Efsm.lean (EFSM syntax and meaning)
    └── spec/                           automaton.md, wrapper.md, then one note per operation:
                                        the Lean definition next to the code's contract (written
                                        for Nagini; the Verus contracts state the same definitions)

How the two layers fit together:
- The Lean proof shows that the algorithm is correct.
- The Verus proof in `certisc-lib/rust/verified/` shows that the Rust code computes exactly the
  construction defined in Lean (its contracts state the Lean definitions; see
  `certisc-lib/DEVELOPING.md`). The earlier Nagini proofs of the Python code are kept, for
  reference only, in `legacy/nagini/`.
- The note in `spec/` records that the two definitions match (checked by hand for now).
