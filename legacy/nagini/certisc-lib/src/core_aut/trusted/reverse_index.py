"""
Trusted builder of the reverse index (certisc-proof/spec/coreach.md).

The encoding groups the transitions by source; the reverse index groups them by target:
    rstart[y] .. rstart[y+1]-1   the reverse positions of the transitions into y;
    rk[j]                        the transition (forward position) at reverse position j;
    rsrc[j]                      its source state;
    pos[k]                       the reverse position of transition k.
(rstart, rsrc) encodes the reversed automaton, so a forward search on it is a backward search on
the automaton.

This code is not verified. Its result is accepted only after the verified checker
(verified_core/reverse_index.py, check_reverse) proves it correct for the encoding, so a bug here
can only make the build fail, never give a wrong index.
"""

from pathlib import Path
from typing import List, Tuple

from core_aut.trusted._strip import load_stripped
from core_aut.trusted.error import InvalidAutomatonError

_verified = load_stripped(Path(__file__).parent.parent / "verified_core" / "reverse_index.py",
                          "core_aut.verified_core.reverse_index (stripped)")


def build_reverse_index(n: int, start, dst) -> Tuple[List[int], List[int], List[int], List[int]]:
    """(rstart, rk, rsrc, pos) for the encoding: a counting sort of the transitions by target."""
    T = len(dst)
    rstart = [0] * (n + 1)
    for y in dst:                            # count the transitions into each state
        rstart[y + 1] += 1
    for y in range(n):                       # prefix sums: the block boundaries
        rstart[y + 1] += rstart[y]
    fill = rstart[:n]                        # next free reverse position in each block
    rk, rsrc, pos = [0] * T, [0] * T, [0] * T
    for x in range(n):
        for k in range(start[x], start[x + 1]):
            j = fill[dst[k]]
            fill[dst[k]] = j + 1
            rk[j], rsrc[j], pos[k] = k, x, j
    return rstart, rk, rsrc, pos


def checked_reverse_index(enc) -> Tuple[Tuple[int, ...], ...]:
    """Build the reverse index and run the verified checker on it; raise if it is rejected."""
    rstart, rk, rsrc, pos = build_reverse_index(enc.n, enc.start, enc.dst)
    if not _verified.check_reverse(enc.n, list(enc.start), list(enc.dst), rstart, rk, rsrc, pos):
        raise InvalidAutomatonError("internal error: the reverse index was rejected by the "
                                    "verified checker")
    return tuple(rstart), tuple(rk), tuple(rsrc), tuple(pos)
