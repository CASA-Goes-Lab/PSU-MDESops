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
- EfsmSystem, Efsm, Edge, Variable, EfsmError
                        EFSMs (efsm.py): the syntax of extended finite-state machines sharing
                        variables; expressions Lit, Var, AtLoc, Un, Bin, Ite (spec:
                        certisc-proof/spec/efsm.md). read_cif (io_aut) builds one.

Layout:
- automaton.py            the user-facing, editable type
- efsm.py                 EFSM syntax and its well-formedness check (plain Python; the
                          meaning is in certisc-proof/DESopsProof/Efsm.lean)
- valid.py                ValidAutomaton, the read-only validated type (holds the automaton
                          in Rust)
- (the compiled Rust core is not here: it is its own package, rust_core, built from
  certisc-lib/rust/ by `pip install` (maturin) and reached through trusted/wrapper.py)
- trusted/                trusted helpers: encoding (Automaton <-> lists), wrapper
                          (validate, check_or_raise), error
- py.typed                marker: the package has type hints (PEP 561)
- (later: numpy_core/)

Design and trust boundary: certisc-proof/spec/wrapper.md. Definitions: certisc-proof/spec/automaton.md.
"""

from core_aut.automaton import Automaton, State
from core_aut.efsm import (
    AtLoc,
    Bin,
    Edge,
    Efsm,
    EfsmError,
    EfsmSystem,
    Ite,
    Lit,
    Un,
    Var,
    Variable,
)
from core_aut.trusted.error import InvalidAutomatonError
from core_aut.trusted.wrapper import check_or_raise, validate
from core_aut.valid import ValidAutomaton

__all__ = ["Automaton", "State", "InvalidAutomatonError", "ValidAutomaton", "check_or_raise",
           "validate", "EfsmSystem", "Efsm", "Edge", "Variable", "EfsmError", "Lit", "Var",
           "AtLoc", "Un", "Bin", "Ite"]
