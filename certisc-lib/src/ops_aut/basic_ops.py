"""
Public basic operations on Automaton objects. Each one calls an implementation:

- backend="verified" (default): the Nagini-verified code in verified_ops/, stripped of its
  contracts at import (core_aut/_strip.py).
- (later: backend="numpy", trusted via differential tests against the verified one.)

The automaton is validated first (check_or_raise, verified), then encoded (core_aut/encoding.py).
Spec: certisc-proof/spec/basic_ops.md.

Note: each call encodes the whole automaton. Caching the encoding on the Automaton (invalidated
on mutation) is still to do; until then, loops over many calls should use verified_ops directly.
"""

from pathlib import Path
from typing import Any, Iterable, List, Tuple, Union

from core_aut import Automaton, check_or_raise
from core_aut._strip import load_stripped
from core_aut.encoding import encode, event_table

_verified = load_stripped(Path(__file__).parent / "verified_ops" / "basic_ops.py",
                          "ops_aut.verified_ops.basic_ops (stripped)")
_BACKENDS = ("verified",)


def next_states(G: Automaton, states: Iterable[int], event: Any, *, witnesses: bool = False,
                backend: str = "verified") -> Union[List[int], Tuple[List[int], List[int]]]:
    """The states reached from `states` by `event`, each once.

    With witnesses=True, also a list `sources`: states reached[i] is reached from sources[i]
    (a state of `states`) by `event`.

    Raises InvalidAutomatonError if G is not a valid automaton, ValueError for a state index
    out of range or an unknown backend."""
    if backend not in _BACKENDS:
        raise ValueError(f"unknown backend {backend!r}; available: {_BACKENDS}")
    check_or_raise(G)
    S = list(states)
    for x in S:
        if not (isinstance(x, int) and 0 <= x < G.num_states):
            raise ValueError(f"{x!r} is not a state index of G")
    table = event_table([G])
    if event not in table:                   # no transition uses it: nothing is reached
        return ([], []) if witnesses else []
    enc = encode(G, table)
    out, src, via, pos = [], [], [], {}
    _verified.next_states(enc.n, enc.m, enc.start, enc.evt, enc.dst, enc.in_E, S, table[event],
                          out, src, via, pos)
    if witnesses:
        return out, [S[j] for j in src]
    return out
