"""
Nagini-verified operations (internal; users call ops_aut's public functions).

- basic_ops.py       verified: next_states (states reached from a list of states by one event)
- parallel.py        verified (in progress): the parallel composition core
- parallel_check.py  verified: checker for the parallel core's output (soundness)

All work on core_aut's encoding (core_aut/encoding.py). Verify, from certisc-lib/
(Python >= 3.12, `verify` extra, Java):

    nagini src/ops_aut/verified_ops/basic_ops.py
    nagini src/ops_aut/verified_ops/parallel.py
    nagini src/ops_aut/verified_ops/parallel_check.py
"""

import core_aut.verified_core  # noqa: F401  (installs the contract stand-ins first)
