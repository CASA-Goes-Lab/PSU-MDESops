"""
Trusted builder of the active-event index (certisc-proof/spec/basic_ops.md §3).

For each state x, the index lists where the runs of its block start (blocks are sorted by event,
so each event of x is one run):
    A[x] .. A[x+1]-1   the positions in H of the heads of x;
    H[i]               a head: the first transition of a run, on event evt[H[i]].
So the active events of x are evt[H[A[x]]], ..., evt[H[A[x+1]-1]], increasing.

This code is not verified. Its result is accepted only after the verified checker
(verified_core/active_index.py, check_index) proves it correct for the encoding, so a bug here
can only make the build fail, never give a wrong index.
"""

from pathlib import Path
from typing import List, Tuple

from core_aut.trusted._strip import load_stripped
from core_aut.trusted.error import InvalidAutomatonError

_verified = load_stripped(Path(__file__).parent.parent / "verified_core" / "active_index.py",
                          "core_aut.verified_core.active_index (stripped)")


def build_active_index(n: int, start, evt) -> Tuple[List[int], List[int]]:
    """(A, H) for the encoding: one scan of the transitions."""
    A, H = [0], []
    for x in range(n):
        prev = None
        for k in range(start[x], start[x + 1]):
            if evt[k] != prev:               # a new run starts at k
                H.append(k)
                prev = evt[k]
        A.append(len(H))
    return A, H


def checked_active_index(enc) -> Tuple[Tuple[int, ...], Tuple[int, ...]]:
    """Build the index and run the verified checker on it; raise if it is rejected."""
    A, H = build_active_index(enc.n, enc.start, enc.evt)
    if not _verified.check_index(enc.n, list(enc.start), list(enc.evt), A, H):
        raise InvalidAutomatonError("internal error: the active-event index was rejected by the "
                                    "verified checker")
    return tuple(A), tuple(H)
