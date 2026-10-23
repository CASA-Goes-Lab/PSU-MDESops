"""
Public basic operations on Automaton objects. Each one calls an implementation:

- backend="verified" (default): the Nagini-verified code in verified_ops/, stripped of its
  contracts at import (core_aut/trusted/_strip.py).
- (later: backend="numpy", trusted via differential tests against the verified one.)

Each function takes a ValidAutomaton (validated once, encoding stored: nothing is checked or
encoded again) or a plain Automaton (validated and encoded on every call; fine for one-off
calls, slow in loops). Spec: certisc-proof/spec/basic_ops.md.
"""

from pathlib import Path
from typing import Any, Iterable, List, Tuple, Union

from core_aut import Automaton, ValidAutomaton, validate
from core_aut.trusted._strip import load_stripped

_verified = load_stripped(Path(__file__).parent / "verified_ops" / "basic_ops.py",
                          "ops_aut.verified_ops.basic_ops (stripped)")
_BACKENDS = ("verified",)


def next_states(G: Union[ValidAutomaton, Automaton], states: Iterable[int], event: Any, *,
                witnesses: bool = False,
                backend: str = "verified") -> Union[List[int], Tuple[List[int], List[int]]]:
    """The states reached from `states` by `event`, each once.

    With witnesses=True, also a list `sources`: states reached[i] is reached from sources[i]
    (a state of `states`) by `event`.

    Raises InvalidAutomatonError if G is not a valid automaton, ValueError for a state index
    out of range or an unknown backend."""
    if backend not in _BACKENDS:
        raise ValueError(f"unknown backend {backend!r}; available: {_BACKENDS}")
    V = G if isinstance(G, ValidAutomaton) else validate(G)
    S = list(states)
    for x in S:
        if not (isinstance(x, int) and 0 <= x < V.num_states):
            raise ValueError(f"{x!r} is not a state index of G")
    e = V._event_number(event)
    if e is None:                            # no transition uses it: nothing is reached
        return ([], []) if witnesses else []
    enc = V._encoding()
    out, src, via, pos = [], [], [], {}
    _verified.next_states(enc.n, enc.m, enc.start, enc.evt, enc.dst, enc.in_E, S, e,
                          out, src, via, pos)
    if witnesses:
        return out, [S[j] for j in src]
    return out
