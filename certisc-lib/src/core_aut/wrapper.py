"""
Trusted wrapper: runs the verified checker on an Automaton (certisc-proof/spec/wrapper.md, section 2).
"""

from core_aut.error import InvalidAutomatonError
from core_aut.verified_core.check import check_automaton
from core_aut.encoding import encode, event_table

# Meaning of check_automaton's result codes. The proof guarantees: 0 iff valid, and each nonzero
# code only when its condition fails (check.py, postconditions of check_automaton).
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


def check_or_raise(G, deterministic: bool = False) -> None:
    """Encode G and run the verified checker; raise InvalidAutomatonError if it fails."""
    enc = encode(G, event_table([G]))
    code = check_automaton(
        enc.n, enc.m, enc.in_E, enc.in_Euc, enc.in_Euo, enc.init, enc.marked,
        enc.start, enc.evt, enc.dst, deterministic,
    )
    if code != 0:
        raise InvalidAutomatonError(MESSAGES.get(code, f"invalid automaton (code {code})"))
