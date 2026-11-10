"""
Trusted (not verified) helpers of core_aut: the code the guarantees rely on without a proof.
Kept small and plain, and tested (tests/core_aut/). The rest of the trusted code is the PyO3
glue, certisc-lib/rust/binding/.

- encoding.py  Automaton <-> plain lists (blocks sorted by event), event numbering
- wrapper.py   validate, check_or_raise: encode, run the verified checker (Rust), raise on
               failure
- error.py     InvalidAutomatonError
"""
