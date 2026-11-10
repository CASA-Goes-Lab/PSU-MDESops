# Nagini-verified certisc (archived 2026-11-10)

The first verified implementation of certisc: Python code verified with
[Nagini](https://github.com/marcoeilers/nagini), as it was in `certisc-lib/` until 2026-11-10.
It was replaced by the Rust core verified with Verus (`certisc-lib/rust/`), which proves the
same operations against the Lean definitions directly. Kept for reference only: nothing in
certisc imports it, and its tests are not run.

The files keep their paths under `certisc-lib/`:

- `src/core_aut/verified_core/`: checker (`check.py`), index checkers, `_contracts.py`
- `src/core_aut/trusted/`: `_strip.py` (contracts off before running), the trusted builders
  (`active_index.py`, `reverse_index.py`, `delete_states.py`), and the last versions of
  `wrapper.py` and `../valid.py` that used them (with both backends)
- `src/ops_aut/verified_ops/`: `basic_ops.py`, `reach.py`, `coreach.py`, `delete.py`,
  `parallel.py`, `parallel_check.py`, `compose.py` (the work in progress on the composition,
  including changes that were not committed when it was archived); `src/ops_aut/basic_ops.py`
  is the last public version with `backend="nagini"`
- `tests/`: the tests of the Nagini code, and the Rust-vs-Nagini comparison (`test_backends.py`)
- `VERIFICATION.md`: what the Nagini code proves, and how

To run it again, copy the files back into `certisc-lib/` (same paths), install the `verify`
extra (`nagini>=1.3.1`, Python >= 3.12, Java), and verify with e.g.
`nagini src/core_aut/verified_core/check.py` from `certisc-lib/`. The spec notes in
`certisc-proof/spec/` still describe the Nagini postconditions.
