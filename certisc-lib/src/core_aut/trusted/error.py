class InvalidAutomatonError(Exception):
    """An Automaton fails the well-formedness conditions of certisc-proof/spec/automaton.md
    (decided by the verified checker, rust/verified/src/core_aut/check.rs)."""
