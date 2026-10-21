"""
Nagini-verified core (internal; users call core_aut's public functions).

- _contracts.py  runtime no-op stand-ins for Nagini's contract functions; installed here, before
                 any verified module is imported
- check.py       verified: the validity checker (check_automaton)

Verify, from certisc-lib/ (Python >= 3.12, `verify` extra, Java):

    nagini src/core_aut/verified_core/check.py
"""

from core_aut.verified_core import _contracts  # noqa: F401  (must run before check is imported)
