"""
Shared definition: "position k is in block x" (certisc-proof/spec/coreach.md).

Used by ops_aut/verified_ops/reach.py, ops_aut/verified_ops/coreach.py and
verified_core/reverse_index.py as the trigger of their nested quantifiers. One definition, so
facts from those files are about the same function and match each other.

It is a separate module, not part of check.py: adding it to check.py made check_blocks fail to
verify (an unrelated definition changed the solver's search; measured 2026-10-27).

Notation: [a, b) are the integers a, ..., b-1; |l| is the length of l. For the contract
notation, see verified_core/reverse_index.py.
"""

from nagini_contracts.contracts import *


@Pure
def in_blk(st: PSeq[int], x: int, k: int) -> bool:
    """Position k is in block x of the boundaries st (st = ToSeq(start), or of a reverse index)."""
    # Math: x ∈ [0,|st|-1) ∧ st[x] ≤ k < st[x+1]
    # Why: the bounds first, so st[x], st[x+1] are valid reads.
    return 0 <= x and x + 1 < len(st) and st[x] <= k and k < st[x + 1]
