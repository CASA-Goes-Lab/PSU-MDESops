"""
Core automaton (part of the certisc distribution). Public API:

- Automaton, State      the automaton type (automaton.py)
- InvalidAutomatonError
- check_or_raise(G, deterministic=False)
                        validates G with the Nagini-verified checker; raises if invalid

Layout:
- automaton.py, error.py  the user-facing type
- encoding.py             trusted bridge: Automaton <-> plain lists (shared by all backends)
- wrapper.py              public functions, calling an implementation
- verified_core/          Nagini-verified implementations (internal)
- (later: numpy_core/)

Design and trust boundary: certisc-proof/spec/wrapper.md. Definitions: certisc-proof/spec/automaton.md.
"""

import core_aut.verified_core  # noqa: F401  (contract stand-ins, before any verified module)
from core_aut.automaton import Automaton, State
from core_aut.error import InvalidAutomatonError
from core_aut.wrapper import check_or_raise

__all__ = ["Automaton", "State", "InvalidAutomatonError", "check_or_raise"]
