"""
Public reachability on Automaton objects. It calls the Nagini-verified implementation in
verified_ops/reach.py, stripped of its contracts at import (core_aut/trusted/_strip.py).

Spec: certisc-proof/spec/reach.md. Lean: `reach f S`, and `reach_eq_of_certificate`, which turns
the verified properties (contains S, closed, witnesses) into "exactly the reachable states".
"""

from pathlib import Path
from typing import Any, Iterable, List, Optional, Tuple, Union

from core_aut import Automaton, ValidAutomaton, validate
from core_aut.trusted._strip import load_stripped

_verified = load_stripped(Path(__file__).parent / "verified_ops" / "reach.py",
                          "ops_aut.verified_ops.reach (stripped)")
_BACKENDS = ("verified",)


def reachable(G: Union[ValidAutomaton, Automaton], states: Optional[Iterable[int]] = None, *,
              witnesses: bool = False, backend: str = "verified"
              ) -> Union[List[int], Tuple[List[int], List[Optional[Tuple[int, Any]]]]]:
    """The states reachable from `states` (default: the initial states), each once, in
    breadth-first order.

    With witnesses=True, also a list `parents`: parents[i] is None if reached[i] is a start
    state, else (x, e): reached[i] is reached from the state x by the event e, and x comes
    earlier in the list. Following the parents back gives a shortest word to each state.

    Raises InvalidAutomatonError if G is not a valid automaton, ValueError for a state index
    out of range or an unknown backend."""
    if backend not in _BACKENDS:
        raise ValueError(f"unknown backend {backend!r}; available: {_BACKENDS}")
    V = G if isinstance(G, ValidAutomaton) else validate(G)
    enc = V._encoding()
    S = sorted(V.init) if states is None else list(states)
    for x in S:
        if not (isinstance(x, int) and 0 <= x < enc.n):
            raise ValueError(f"{x!r} is not a state index of G")
    mark = [-1] * enc.n                      # one entry per state
    out, par, via = [], [], []
    _verified.reachable(enc.n, enc.start, enc.dst, S, mark, out, par, via)
    if not witnesses:
        return out
    parents = [None if p == -1 else (out[p], V._event_of[enc.evt[k]])
               for p, k in zip(par, via)]
    return out, parents
