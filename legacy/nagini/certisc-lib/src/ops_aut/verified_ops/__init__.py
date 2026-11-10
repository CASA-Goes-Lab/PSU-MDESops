"""
Nagini-verified operations (internal; users call ops_aut's public functions).

- basic_ops.py       verified: next_states, active_events (and over the active-event index)
- reach.py           verified: reachable (states reachable from a list of start states)
- coreach.py         verified: coreachable (states that can reach a list of targets; runs
                     reach.reachable on the reverse index)
- delete.py          verified: checker for deleting states (the result is exactly G without
                     the deleted states)
- parallel.py        verified (in progress): the parallel composition core
- parallel_check.py  verified: checker for the parallel core's output (soundness)

All work on core_aut's encoding (core_aut/trusted/encoding.py). Verify, from certisc-lib/
(Python >= 3.12, `verify` extra, Java):

    nagini src/ops_aut/verified_ops/basic_ops.py
    nagini src/ops_aut/verified_ops/reach.py
    nagini src/ops_aut/verified_ops/coreach.py
    nagini src/ops_aut/verified_ops/delete.py
    nagini src/ops_aut/verified_ops/parallel.py
    nagini src/ops_aut/verified_ops/parallel_check.py
"""

import core_aut.verified_core  # noqa: F401  (installs the contract stand-ins first)
