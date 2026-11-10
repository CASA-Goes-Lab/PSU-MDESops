"""
Core automaton (part of the certisc distribution). Public API:

- Automaton, State      the automaton type (automaton.py)
- InvalidAutomatonError
- validate(G, deterministic=False) -> ValidAutomaton
                        validates G once with the verified checker (Rust, Verus) and returns
                        a read-only ValidAutomaton (raises InvalidAutomatonError if invalid)
- ValidAutomaton        the read-only, validated automaton (valid.py); operations use it
                        without checking or encoding again
- check_or_raise(G, deterministic=False)
                        the same check, without building a ValidAutomaton

Layout:
- automaton.py            the user-facing, editable type
- valid.py                ValidAutomaton, the read-only validated type (holds the automaton
                          in Rust)
- _rs.*.so                the compiled extension: the Verus-verified Rust core
                          (certisc-lib/rust/verified/) behind the PyO3 glue (rust/binding/);
                          built by `pip install` (maturin)
- trusted/                trusted helpers: encoding (Automaton <-> lists), wrapper
                          (validate, check_or_raise), error
- py.typed                marker: the package has type hints (PEP 561)
- (later: numpy_core/)

Design and trust boundary: certisc-proof/spec/wrapper.md. Definitions: certisc-proof/spec/automaton.md.
"""

from core_aut.automaton import Automaton, State
from core_aut.trusted.error import InvalidAutomatonError
from core_aut.trusted.wrapper import check_or_raise, validate
from core_aut.valid import ValidAutomaton

__all__ = ["Automaton", "State", "InvalidAutomatonError", "ValidAutomaton", "check_or_raise",
           "validate"]
