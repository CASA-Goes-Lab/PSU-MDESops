"""
Trusted builder for deleting states (certisc-proof/spec/delete_states.md).

Given the encoding of an automaton and a flag per state (deleted or not), build the encoding of
the automaton with those states deleted: the kept states renumbered in their old order, with
every transition between two kept states and no other. It also returns the two witness arrays
the verified checker needs (src2: the old transition each new one copies; pos2: the new
transition each old one became, or -1).

This code is not verified. Its result is used only after the verified checker
(ops_aut/verified_ops/delete.py, check_delete) proves it exact, and the result is then run
through the verified validity checker, so a bug here can only make the call fail, never give a
wrong automaton.
"""

from typing import List, Sequence, Tuple


def build_delete(enc, dele: Sequence[bool]) -> Tuple[List[int], List[int], List[int], List[int],
                                                      List[int], List[bool], List[bool],
                                                      List[int], List[int]]:
    """(new_of, old_of, start2, evt2, dst2, init2, marked2, src2, pos2) for deleting the states x
    with dele[x] from the encoding `enc`."""
    n = enc.n
    start, evt, dst = enc.start, enc.evt, enc.dst
    new_of = [-1] * n                        # -1: deleted
    old_of = []
    for x in range(n):
        if not dele[x]:
            new_of[x] = len(old_of)
            old_of.append(x)
    init2 = [enc.init[x] for x in old_of]
    marked2 = [enc.marked[x] for x in old_of]
    start2, evt2, dst2, src2 = [0], [], [], []
    pos2 = [-1] * len(dst)                   # -1: not copied
    for x in old_of:                         # the kept states, in order: their blocks
        for k in range(start[x], start[x + 1]):
            y = new_of[dst[k]]
            if y >= 0:                       # the target is kept: copy the transition
                pos2[k] = len(src2)
                src2.append(k)
                evt2.append(evt[k])
                dst2.append(y)
        start2.append(len(src2))
    return new_of, old_of, start2, evt2, dst2, init2, marked2, src2, pos2
