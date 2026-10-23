"""
Trusted (not verified) helpers of core_aut: the code the guarantees rely on without a proof.
Kept small and plain, and tested (certisc-lib/VERIFICATION.md, section 6).

- encoding.py  Automaton <-> plain lists (blocks sorted by event), event numbering
- wrapper.py   check_or_raise: encode, run the verified checker, raise on failure
- _strip.py    removes contracts and lemma calls from verified modules before they run
- error.py     InvalidAutomatonError

(core_aut/py.typed stays at the top of the package: Nagini, through mypy, only reads
imported packages that carry the marker there.)
"""
