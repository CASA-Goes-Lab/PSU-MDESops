"""
Trusted wrapper: runs the verified checker on an Automaton (certisc-proof/spec/wrapper.md, section 2).

The checker is the Verus-verified `check_code` in Rust (rust/verified/src/core_aut/check.rs),
reached through the extension core_aut._rs: RsAut.from_lists runs it and keeps the automaton in
Rust. The Nagini-verified checker (verified_core/check.py, `_run_check` below) gives the same
codes; it is kept for the Nagini backend and for the tests that compare the two.
"""

from core_aut._rs import RsAut
from core_aut.trusted.error import InvalidAutomatonError
from core_aut.verified_core.check import check_automaton
from core_aut.trusted.encoding import encode, event_table

# Meaning of the checker's result codes. The proofs guarantee: 0 iff valid, and each nonzero code
# only when its condition fails (check.rs, postconditions of check_code; check.py, of
# check_automaton).
MESSAGES = {
    1: "sizes: the number of markings does not match the number of states",
    2: "internal encoding error: transition blocks are inconsistent",
    3: "a transition has an unknown event, an event not in `events` (W1), or a target that is not a state",
    4: "Euc or Euo contains an event not in `events` (W2)",
    5: "initial states: there must be an initial state iff there are states (W3)",
    6: "deterministic automaton required: more than one initial state",
    7: "deterministic automaton required: a state has two transitions with the same event",
    8: "internal encoding error: a state's transitions are not sorted by event",
}


def _message(code: int) -> str:
    return MESSAGES.get(code, f"invalid automaton (code {code})")


def _run_check(enc, deterministic: bool) -> int:
    """The Nagini-verified checker on an encoding: its result code (0: valid)."""
    return check_automaton(enc.n, enc.m, enc.in_E, enc.in_Euc, enc.in_Euo, enc.init, enc.marked,
                           enc.start, enc.evt, enc.dst, deterministic)


def to_rust(enc):
    """Run the verified Rust checker on the encoding `enc`. Returns (RsAut, 0) if it is valid,
    (None, code) if not."""
    try:
        return RsAut.from_lists(enc.n, enc.m, enc.in_E, enc.in_Euc, enc.in_Euo, enc.init,
                                enc.marked, enc.start, enc.evt, enc.dst), 0
    except ValueError as err:                # from_lists raises ValueError(code) if invalid
        if err.args and isinstance(err.args[0], int):
            return None, err.args[0]
        raise


def validate(G, deterministic: bool = False):
    """Encode G once and run the verified checker; return a read-only ValidAutomaton.

    Raises InvalidAutomatonError if G is not valid (or not deterministic, when
    deterministic=True). Whether G is deterministic is also decided by the verified checker
    (`is_deterministic`, computed on first use)."""
    from core_aut.valid import ValidAutomaton
    table = event_table([G])
    rs, code = to_rust(encode(G, table))
    if code != 0:
        raise InvalidAutomatonError(_message(code))
    if deterministic and rs.det_code != 0:
        raise InvalidAutomatonError(_message(rs.det_code))
    return ValidAutomaton._make(rs, list(table), [s.name for s in G.states])


def validate_encoded(enc, event_of: list, names: list):
    """Run the verified checker on an encoding built by an operation of the Nagini backend
    (e.g. deleting states); return a ValidAutomaton, or raise InvalidAutomatonError (an internal
    error: operations build valid encodings)."""
    from core_aut.valid import ValidAutomaton
    rs, code = to_rust(enc)
    if code != 0:
        raise InvalidAutomatonError("internal error: an operation built an invalid automaton: "
                                    + _message(code))
    return ValidAutomaton._make(rs, event_of, names)


def check_or_raise(G, deterministic: bool = False) -> None:
    """Encode G and run the verified checker; raise InvalidAutomatonError if it fails."""
    rs, code = to_rust(encode(G, event_table([G])))
    if code == 0 and deterministic:
        code = rs.det_code
    if code != 0:
        raise InvalidAutomatonError(_message(code))
