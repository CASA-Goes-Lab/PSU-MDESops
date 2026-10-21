"""
Nagini-verified cores and their trusted wrapper.

Design and trust boundary: DESops-proof/spec/wrapper.md. Definitions: DESops-proof/spec/automaton.md.

- check.py      verified: the validity checker
- encoding.py   trusted: event numbering, Automaton <-> plain lists
- wrapper.py    trusted: encode, run the checker, raise InvalidAutomatonError

Verify, from DESops-lib/ (Python >= 3.12, `verify` extra, Java):

    nagini DESops/verified/check.py

Expected: "Verification successful" in about 15-25 s.
"""

from DESops.verified import _contracts  # noqa: F401  (must run before check is imported)
