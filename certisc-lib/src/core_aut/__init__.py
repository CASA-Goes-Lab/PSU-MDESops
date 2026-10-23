"""
Core automaton (part of the certisc distribution). Public API:

- Automaton, State      the automaton type (automaton.py)
- InvalidAutomatonError
- validate(G, deterministic=False) -> ValidAutomaton
                        validates G once with the Nagini-verified checker and returns a
                        read-only ValidAutomaton (raises InvalidAutomatonError if invalid)
- ValidAutomaton        the read-only, validated automaton (valid.py); operations use it
                        without checking or encoding again
- check_or_raise(G, deterministic=False)
                        the same check, without building a ValidAutomaton

Layout:
- automaton.py            the user-facing, editable type
- valid.py                ValidAutomaton, the read-only validated type
- trusted/                trusted helpers: encoding (Automaton <-> lists), wrapper
                          (check_or_raise), _strip (contracts off before running), error
- verified_core/          Nagini-verified implementations (internal)
- py.typed                marker that lets Nagini (via mypy) read core_aut when another
                          package imports it; must stay at the top of the package
- (later: numpy_core/)

Design and trust boundary: certisc-proof/spec/wrapper.md. Definitions: certisc-proof/spec/automaton.md.
"""

import core_aut.verified_core  # noqa: F401  (contract stand-ins, before any verified module)
from core_aut.automaton import Automaton, State
from core_aut.trusted.error import InvalidAutomatonError
from core_aut.trusted.wrapper import check_or_raise, validate
from core_aut.valid import ValidAutomaton

__all__ = ["Automaton", "State", "InvalidAutomatonError", "ValidAutomaton", "check_or_raise",
           "validate"]
