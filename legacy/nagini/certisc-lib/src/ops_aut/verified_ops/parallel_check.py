"""
Verified checker for the output of the parallel core (certisc-proof/spec/parallel.md, N2a).

check_sound walks the output of parallel_core (src/ops_aut/verified_ops/parallel.py) in emission order and
checks that every output transition is the next expected synchronous move. It records, for each
output transition k, the output state it leaves (ostate[k]) and the input transitions it uses
(osrc1[k], osrc2[k]; -1 when that side does not move).

Proved (Nagini, about 70 s): if check_sound returns True, every output transition is a
synchronous move (sound_ok over all positions). Completeness (N2b) is in progress.

Verify, from certisc-lib/ (Python >= 3.12, `verify` extra, Java):

    nagini src/ops_aut/verified_ops/parallel_check.py
"""

from typing import List

from nagini_contracts.contracts import *
from nagini_contracts.obligations import MustTerminate

@Pure
def blocks_ok(n: int, start: List[int], T: int) -> bool:
    Requires(Acc(list_pred(start), 1 / 2))
    if n < 0 or len(start) != n + 1:
        return False
    if start[0] != 0 or start[n] != T:
        return False
    return Forall(int, lambda x: (
        Implies(0 <= x and x < n,
                0 <= start[x] and start[x] <= start[x + 1] and start[x + 1] <= T),
        [[start[x + 1]]]))


@Pure
def trans_ok(n: int, m: int, in_E: List[bool], evt: List[int], dst: List[int]) -> bool:
    """Every transition's event is an event number in E (W1), and its target a state."""
    Requires(Acc(list_pred(in_E), 1 / 2) and Acc(list_pred(evt), 1 / 2)
             and Acc(list_pred(dst), 1 / 2))
    if len(in_E) != m or len(evt) != len(dst):
        return False
    return Forall(int, lambda k: (Implies(
        0 <= k and k < len(evt),
        0 <= evt[k] and evt[k] < m and in_E[evt[k]] and 0 <= dst[k] and dst[k] < n),
        [[evt[k]], [dst[k]]]))


@Pure
def input_ok(n: int, m: int, start: List[int], evt: List[int], dst: List[int],
             in_E: List[bool]) -> bool:
    Requires(Acc(list_pred(start), 1 / 2) and Acc(list_pred(evt), 1 / 2)
             and Acc(list_pred(dst), 1 / 2) and Acc(list_pred(in_E), 1 / 2))
    return (m >= 0 and len(in_E) == m and blocks_ok(n, start, len(evt))
            and trans_ok(n, m, in_E, evt, dst))



@Pure
def pairs_ok(n1: int, n2: int, p1: List[int], p2: List[int]) -> bool:
    Requires(Acc(list_pred(p1), 1 / 2) and Acc(list_pred(p2), 1 / 2))
    return len(p1) == len(p2) and Forall(int, lambda i: (Implies(
        0 <= i and i < len(p1),
        0 <= p1[i] and p1[i] < n1 and 0 <= p2[i] and p2[i] < n2), [[p1[i]], [p2[i]]]))


@Pure
def targets_ok(T: int, oevt: List[int], odst: List[int]) -> bool:
    Requires(Acc(list_pred(oevt), 1 / 2) and Acc(list_pred(odst), 1 / 2))
    return len(odst) == len(oevt) and Forall(int, lambda k: (Implies(
        0 <= k and k < len(odst), 0 <= odst[k] and odst[k] < T), [[odst[k]]]))


@Pure
def move_ok(start1: List[int], evt1: List[int], dst1: List[int], in_E1: List[bool],
             start2: List[int], evt2: List[int], dst2: List[int], in_E2: List[bool],
            ostart: List[int], i: int, x1: int, x2: int, k: int, e: int, y1: int, y2: int,
            s1: int, s2: int) -> bool:
    """Output transition k, of output state i = (x1, x2), on event e to (y1, y2), is a
    synchronous move: s1 is the G1 transition used (-1: G1 stays and does not have e), likewise
    s2 for G2 (N2a). Scalar arguments, so that growing lists do not change earlier instances."""
    Requires(Acc(list_pred(start1), 1 / 2) and Acc(list_pred(evt1), 1 / 2)
             and Acc(list_pred(dst1), 1 / 2) and Acc(list_pred(in_E1), 1 / 2)
             and Acc(list_pred(start2), 1 / 2) and Acc(list_pred(evt2), 1 / 2)
             and Acc(list_pred(dst2), 1 / 2) and Acc(list_pred(in_E2), 1 / 2))
    Requires(Acc(list_pred(ostart), 1 / 2))
    return (0 <= i and i + 1 < len(ostart) and ostart[i] <= k and k < ostart[i + 1]
            and 0 <= e and e < len(in_E1) and e < len(in_E2)
            and 0 <= x1 and x1 + 1 < len(start1) and 0 <= x2 and x2 + 1 < len(start2)
            and (s1 < 0 or (start1[x1] <= s1 and s1 < start1[x1 + 1] and 0 <= s1
                            and s1 < len(evt1) and s1 < len(dst1)
                            and evt1[s1] == e and dst1[s1] == y1))
            and (s1 >= 0 or (y1 == x1 and not in_E1[e]))
            and (s2 < 0 or (start2[x2] <= s2 and s2 < start2[x2 + 1] and 0 <= s2
                            and s2 < len(evt2) and s2 < len(dst2)
                            and evt2[s2] == e and dst2[s2] == y2))
            and (s2 >= 0 or (y2 == x2 and not in_E2[e])))


@Pure
def sound_ok(start1: List[int], evt1: List[int], dst1: List[int], in_E1: List[bool],
             start2: List[int], evt2: List[int], dst2: List[int], in_E2: List[bool],
             p1: List[int], p2: List[int], ostart: List[int], oevt: List[int], odst: List[int],
             ostate: List[int], osrc1: List[int], osrc2: List[int], K: int) -> bool:
    """Output transitions 0 .. K-1 are synchronous moves (N2a)."""
    Requires(Acc(list_pred(start1), 1 / 2) and Acc(list_pred(evt1), 1 / 2)
             and Acc(list_pred(dst1), 1 / 2) and Acc(list_pred(in_E1), 1 / 2)
             and Acc(list_pred(start2), 1 / 2) and Acc(list_pred(evt2), 1 / 2)
             and Acc(list_pred(dst2), 1 / 2) and Acc(list_pred(in_E2), 1 / 2))
    Requires(Acc(list_pred(p1), 1 / 2) and Acc(list_pred(p2), 1 / 2)
             and Acc(list_pred(ostart), 1 / 2) and Acc(list_pred(oevt), 1 / 2)
             and Acc(list_pred(odst), 1 / 2) and Acc(list_pred(ostate), 1 / 2)
             and Acc(list_pred(osrc1), 1 / 2) and Acc(list_pred(osrc2), 1 / 2))
    return (0 <= K and K <= len(oevt) and len(odst) == len(oevt) and len(p2) == len(p1)
            and K <= len(ostate) and K <= len(osrc1) and K <= len(osrc2)
            and Forall(int, lambda k: (Implies(
        0 <= k and k < K,
        0 <= ToSeq(ostate)[k] and ToSeq(ostate)[k] < len(p1)
        and 0 <= odst[k] and odst[k] < len(p1)
        and move_ok(start1, evt1, dst1, in_E1, start2, evt2, dst2, in_E2, ostart,
                    ToSeq(ostate)[k], p1[ToSeq(ostate)[k]], p2[ToSeq(ostate)[k]], k, oevt[k],
                    p1[odst[k]], p2[odst[k]], ToSeq(osrc1)[k], ToSeq(osrc2)[k])),
        [[ToSeq(ostate)[k]]])))


def record(ostate: List[int], osrc1: List[int], osrc2: List[int], i: int, s1: int, s2: int) -> None:
    """Append the witnesses of one output transition; earlier entries are unchanged."""
    Requires(MustTerminate(2))
    Requires(Acc(list_pred(ostate)) and Acc(list_pred(osrc1)) and Acc(list_pred(osrc2)))
    Requires(len(osrc1) == len(ostate) and len(osrc2) == len(ostate))
    Ensures(Acc(list_pred(ostate)) and Acc(list_pred(osrc1)) and Acc(list_pred(osrc2)))
    Ensures(len(ostate) == Old(len(ostate)) + 1 and len(osrc1) == len(ostate)
            and len(osrc2) == len(ostate))
    Ensures(ToSeq(ostate)[Old(len(ostate))] == i and ToSeq(osrc1)[Old(len(ostate))] == s1
            and ToSeq(osrc2)[Old(len(ostate))] == s2)
    Ensures(Forall(int, lambda j: (Implies(0 <= j and j < Old(len(ostate)),
                                           ToSeq(ostate)[j] == Old(ToSeq(ostate))[j]
                                           and ToSeq(osrc1)[j] == Old(ToSeq(osrc1))[j]
                                           and ToSeq(osrc2)[j] == Old(ToSeq(osrc2))[j]),
                                   [[ToSeq(ostate)[j]]])))
    n = len(ostate)
    ostate.append(i)
    osrc1.append(s1)
    osrc2.append(s2)
    Assert(Forall(int, lambda j: (Implies(0 <= j and j < n,
                                          ToSeq(ostate)[j] == Old(ToSeq(ostate))[j]
                                          and ToSeq(osrc1)[j] == Old(ToSeq(osrc1))[j]
                                          and ToSeq(osrc2)[j] == Old(ToSeq(osrc2))[j]),
                                  [[ToSeq(ostate)[j]]])))


def check_sound(n1: int, n2: int, m: int,
                   start1: List[int], evt1: List[int], dst1: List[int], in_E1: List[bool],
                   start2: List[int], evt2: List[int], dst2: List[int], in_E2: List[bool],
                   p1: List[int], p2: List[int], ostart: List[int], oevt: List[int],
                   odst: List[int], ostate: List[int], osrc1: List[int], osrc2: List[int]) -> bool:
    """Walk the output in emission order and check that each transition is the next expected
    synchronous move; record which input transitions it uses. True: sound (N2a)."""
    Requires(Acc(list_pred(start1), 1 / 2) and Acc(list_pred(evt1), 1 / 2)
             and Acc(list_pred(dst1), 1 / 2) and Acc(list_pred(in_E1), 1 / 2)
             and Acc(list_pred(start2), 1 / 2) and Acc(list_pred(evt2), 1 / 2)
             and Acc(list_pred(dst2), 1 / 2) and Acc(list_pred(in_E2), 1 / 2)
             and Acc(list_pred(p1), 1 / 2) and Acc(list_pred(p2), 1 / 2)
             and Acc(list_pred(ostart), 1 / 2) and Acc(list_pred(oevt), 1 / 2)
             and Acc(list_pred(odst), 1 / 2))
    Requires(Acc(list_pred(ostate)) and Acc(list_pred(osrc1)) and Acc(list_pred(osrc2)))
    Requires(MustTerminate(len(p1) + 4))
    Requires(input_ok(n1, m, start1, evt1, dst1, in_E1) and input_ok(n2, m, start2, evt2, dst2, in_E2))
    Requires(pairs_ok(n1, n2, p1, p2) and blocks_ok(len(p1), ostart, len(oevt)))
    Requires(targets_ok(len(p1), oevt, odst))
    Requires(len(start1) == n1 + 1 and len(start2) == n2 + 1 and len(ostart) == len(p1) + 1)
    Requires(len(ostate) == 0 and len(osrc1) == 0 and len(osrc2) == 0)
    Ensures(Acc(list_pred(start1), 1 / 2) and Acc(list_pred(evt1), 1 / 2)
            and Acc(list_pred(dst1), 1 / 2) and Acc(list_pred(in_E1), 1 / 2)
            and Acc(list_pred(start2), 1 / 2) and Acc(list_pred(evt2), 1 / 2)
            and Acc(list_pred(dst2), 1 / 2) and Acc(list_pred(in_E2), 1 / 2)
            and Acc(list_pred(p1), 1 / 2) and Acc(list_pred(p2), 1 / 2)
            and Acc(list_pred(ostart), 1 / 2) and Acc(list_pred(oevt), 1 / 2)
            and Acc(list_pred(odst), 1 / 2))
    Ensures(Acc(list_pred(ostate)) and Acc(list_pred(osrc1)) and Acc(list_pred(osrc2)))
    Ensures(Implies(Result(), len(ostate) == len(oevt) and len(osrc1) == len(oevt)
                    and len(osrc2) == len(oevt) and len(odst) == len(oevt) and len(p2) == len(p1)
                    and sound_ok(start1, evt1, dst1, in_E1, start2, evt2, dst2, in_E2, p1, p2,
                                 ostart, oevt, odst, ostate, osrc1, osrc2, len(oevt))))
    k = 0
    i = 0
    Assert(sound_ok(start1, evt1, dst1, in_E1, start2, evt2, dst2, in_E2, p1, p2, ostart, oevt,
                    odst, ostate, osrc1, osrc2, 0))
    while i < len(p1):
        Invariant(Acc(list_pred(start1), 1 / 2) and Acc(list_pred(evt1), 1 / 2)
                  and Acc(list_pred(dst1), 1 / 2) and Acc(list_pred(in_E1), 1 / 2)
                  and Acc(list_pred(start2), 1 / 2) and Acc(list_pred(evt2), 1 / 2)
                  and Acc(list_pred(dst2), 1 / 2) and Acc(list_pred(in_E2), 1 / 2)
                  and Acc(list_pred(p1), 1 / 2) and Acc(list_pred(p2), 1 / 2)
                  and Acc(list_pred(ostart), 1 / 2) and Acc(list_pred(oevt), 1 / 2)
                  and Acc(list_pred(odst), 1 / 2))
        Invariant(Acc(list_pred(ostate)) and Acc(list_pred(osrc1)) and Acc(list_pred(osrc2)))
        Invariant(MustTerminate(len(p1) - i + 3))
        Invariant(ToSeq(start1) == Old(ToSeq(start1))
                  and ToSeq(evt1) == Old(ToSeq(evt1))
                  and ToSeq(dst1) == Old(ToSeq(dst1))
                  and ToSeq(in_E1) == Old(ToSeq(in_E1))
                  and ToSeq(start2) == Old(ToSeq(start2))
                  and ToSeq(evt2) == Old(ToSeq(evt2))
                  and ToSeq(dst2) == Old(ToSeq(dst2))
                  and ToSeq(in_E2) == Old(ToSeq(in_E2))
                  and ToSeq(p1) == Old(ToSeq(p1))
                  and ToSeq(p2) == Old(ToSeq(p2))
                  and ToSeq(ostart) == Old(ToSeq(ostart))
                  and ToSeq(oevt) == Old(ToSeq(oevt))
                  and ToSeq(odst) == Old(ToSeq(odst)))
        Invariant(input_ok(n1, m, start1, evt1, dst1, in_E1) and input_ok(n2, m, start2, evt2, dst2, in_E2))
        Invariant(pairs_ok(n1, n2, p1, p2) and blocks_ok(len(p1), ostart, len(oevt)))
        Invariant(targets_ok(len(p1), oevt, odst))
        Invariant(len(start1) == n1 + 1 and len(start2) == n2 + 1 and len(ostart) == len(p1) + 1)
        Invariant(0 <= i and i <= len(p1) and k == ostart[i])
        Invariant(0 <= k and k <= len(oevt) and len(ostate) == k and len(osrc1) == k and len(osrc2) == k)
        Invariant(sound_ok(start1, evt1, dst1, in_E1, start2, evt2, dst2, in_E2, p1, p2, ostart, oevt,
                           odst, ostate, osrc1, osrc2, k))
        x1 = p1[i]
        x2 = p2[i]
        Assert(0 <= x1 and x1 < n1 and 0 <= x2 and x2 < n2)   # pairs_ok at i
        hi = ostart[i + 1]
        # Moves of G1: with G2 on a shared event, alone on a private one.
        j1 = start1[x1]
        hi1 = start1[x1 + 1]
        while j1 < hi1:
            Invariant(Acc(list_pred(start1), 1 / 2) and Acc(list_pred(evt1), 1 / 2)
                      and Acc(list_pred(dst1), 1 / 2) and Acc(list_pred(in_E1), 1 / 2)
                      and Acc(list_pred(start2), 1 / 2) and Acc(list_pred(evt2), 1 / 2)
                      and Acc(list_pred(dst2), 1 / 2) and Acc(list_pred(in_E2), 1 / 2)
                      and Acc(list_pred(p1), 1 / 2) and Acc(list_pred(p2), 1 / 2)
                      and Acc(list_pred(ostart), 1 / 2) and Acc(list_pred(oevt), 1 / 2)
                      and Acc(list_pred(odst), 1 / 2))
            Invariant(Acc(list_pred(ostate)) and Acc(list_pred(osrc1)) and Acc(list_pred(osrc2)))
            Invariant(MustTerminate(hi1 - j1 + 3))
            Invariant(ToSeq(start1) == Old(ToSeq(start1))
                      and ToSeq(evt1) == Old(ToSeq(evt1))
                      and ToSeq(dst1) == Old(ToSeq(dst1))
                      and ToSeq(in_E1) == Old(ToSeq(in_E1))
                      and ToSeq(start2) == Old(ToSeq(start2))
                      and ToSeq(evt2) == Old(ToSeq(evt2))
                      and ToSeq(dst2) == Old(ToSeq(dst2))
                      and ToSeq(in_E2) == Old(ToSeq(in_E2))
                      and ToSeq(p1) == Old(ToSeq(p1))
                      and ToSeq(p2) == Old(ToSeq(p2))
                      and ToSeq(ostart) == Old(ToSeq(ostart))
                      and ToSeq(oevt) == Old(ToSeq(oevt))
                      and ToSeq(odst) == Old(ToSeq(odst)))
            Invariant(input_ok(n1, m, start1, evt1, dst1, in_E1) and input_ok(n2, m, start2, evt2, dst2, in_E2))
            Invariant(pairs_ok(n1, n2, p1, p2) and blocks_ok(len(p1), ostart, len(oevt)))
            Invariant(targets_ok(len(p1), oevt, odst))
            Invariant(len(start1) == n1 + 1 and len(start2) == n2 + 1 and len(ostart) == len(p1) + 1)
            Invariant(0 <= i and i < len(p1) and x1 == p1[i] and x2 == p2[i] and hi == ostart[i + 1])
            Invariant(0 <= x1 and x1 < n1 and 0 <= x2 and x2 < n2)
            Invariant(ostart[i] <= k and k <= hi and hi <= len(oevt))
            Invariant(hi1 == start1[x1 + 1] and start1[x1] <= j1 and j1 <= hi1)
            Invariant(0 <= k and k <= len(oevt) and len(ostate) == k and len(osrc1) == k and len(osrc2) == k)
            Invariant(sound_ok(start1, evt1, dst1, in_E1, start2, evt2, dst2, in_E2, p1, p2, ostart, oevt,
                               odst, ostate, osrc1, osrc2, k))
            e = evt1[j1]
            y1 = dst1[j1]
            if in_E2[e]:
                j2 = start2[x2]
                hi2 = start2[x2 + 1]
                while j2 < hi2:
                    Invariant(Acc(list_pred(start1), 1 / 2) and Acc(list_pred(evt1), 1 / 2)
                              and Acc(list_pred(dst1), 1 / 2) and Acc(list_pred(in_E1), 1 / 2)
                              and Acc(list_pred(start2), 1 / 2) and Acc(list_pred(evt2), 1 / 2)
                              and Acc(list_pred(dst2), 1 / 2) and Acc(list_pred(in_E2), 1 / 2)
                              and Acc(list_pred(p1), 1 / 2) and Acc(list_pred(p2), 1 / 2)
                              and Acc(list_pred(ostart), 1 / 2) and Acc(list_pred(oevt), 1 / 2)
                              and Acc(list_pred(odst), 1 / 2))
                    Invariant(Acc(list_pred(ostate)) and Acc(list_pred(osrc1)) and Acc(list_pred(osrc2)))
                    Invariant(MustTerminate(hi2 - j2 + 3))
                    Invariant(ToSeq(start1) == Old(ToSeq(start1))
                              and ToSeq(evt1) == Old(ToSeq(evt1))
                              and ToSeq(dst1) == Old(ToSeq(dst1))
                              and ToSeq(in_E1) == Old(ToSeq(in_E1))
                              and ToSeq(start2) == Old(ToSeq(start2))
                              and ToSeq(evt2) == Old(ToSeq(evt2))
                              and ToSeq(dst2) == Old(ToSeq(dst2))
                              and ToSeq(in_E2) == Old(ToSeq(in_E2))
                              and ToSeq(p1) == Old(ToSeq(p1))
                              and ToSeq(p2) == Old(ToSeq(p2))
                              and ToSeq(ostart) == Old(ToSeq(ostart))
                              and ToSeq(oevt) == Old(ToSeq(oevt))
                              and ToSeq(odst) == Old(ToSeq(odst)))
                    Invariant(input_ok(n1, m, start1, evt1, dst1, in_E1) and input_ok(n2, m, start2, evt2, dst2, in_E2))
                    Invariant(pairs_ok(n1, n2, p1, p2) and blocks_ok(len(p1), ostart, len(oevt)))
                    Invariant(targets_ok(len(p1), oevt, odst))
                    Invariant(len(start1) == n1 + 1 and len(start2) == n2 + 1 and len(ostart) == len(p1) + 1)
                    Invariant(0 <= i and i < len(p1) and x1 == p1[i] and x2 == p2[i] and hi == ostart[i + 1])
                    Invariant(0 <= x1 and x1 < n1 and 0 <= x2 and x2 < n2)
                    Invariant(ostart[i] <= k and k <= hi and hi <= len(oevt))
                    Invariant(hi1 == start1[x1 + 1] and start1[x1] <= j1 and j1 < hi1)
                    Invariant(e == evt1[j1] and y1 == dst1[j1] and in_E2[e])
                    Invariant(hi2 == start2[x2 + 1] and start2[x2] <= j2 and j2 <= hi2)
                    Invariant(0 <= k and k <= len(oevt) and len(ostate) == k and len(osrc1) == k and len(osrc2) == k)
                    Invariant(sound_ok(start1, evt1, dst1, in_E1, start2, evt2, dst2, in_E2, p1, p2, ostart, oevt,
                                       odst, ostate, osrc1, osrc2, k))
                    if evt2[j2] == e:
                        if k >= hi or oevt[k] != e or p1[odst[k]] != y1 or p2[odst[k]] != dst2[j2]:
                            return False
                        Assert(move_ok(start1, evt1, dst1, in_E1, start2, evt2, dst2, in_E2, ostart,
                                       i, x1, x2, k, e, p1[odst[k]], p2[odst[k]], j1, j2))
                        record(ostate, osrc1, osrc2, i, j1, j2)
                        k += 1
                    j2 += 1
            else:
                if k >= hi or oevt[k] != e or p1[odst[k]] != y1 or p2[odst[k]] != x2:
                    return False
                Assert(move_ok(start1, evt1, dst1, in_E1, start2, evt2, dst2, in_E2, ostart,
                               i, x1, x2, k, e, p1[odst[k]], p2[odst[k]], j1, -1))
                record(ostate, osrc1, osrc2, i, j1, -1)
                k += 1
            j1 += 1
        # Moves of G2 alone, on its private events.
        j2 = start2[x2]
        hi2 = start2[x2 + 1]
        while j2 < hi2:
            Invariant(Acc(list_pred(start1), 1 / 2) and Acc(list_pred(evt1), 1 / 2)
                      and Acc(list_pred(dst1), 1 / 2) and Acc(list_pred(in_E1), 1 / 2)
                      and Acc(list_pred(start2), 1 / 2) and Acc(list_pred(evt2), 1 / 2)
                      and Acc(list_pred(dst2), 1 / 2) and Acc(list_pred(in_E2), 1 / 2)
                      and Acc(list_pred(p1), 1 / 2) and Acc(list_pred(p2), 1 / 2)
                      and Acc(list_pred(ostart), 1 / 2) and Acc(list_pred(oevt), 1 / 2)
                      and Acc(list_pred(odst), 1 / 2))
            Invariant(Acc(list_pred(ostate)) and Acc(list_pred(osrc1)) and Acc(list_pred(osrc2)))
            Invariant(MustTerminate(hi2 - j2 + 3))
            Invariant(ToSeq(start1) == Old(ToSeq(start1))
                      and ToSeq(evt1) == Old(ToSeq(evt1))
                      and ToSeq(dst1) == Old(ToSeq(dst1))
                      and ToSeq(in_E1) == Old(ToSeq(in_E1))
                      and ToSeq(start2) == Old(ToSeq(start2))
                      and ToSeq(evt2) == Old(ToSeq(evt2))
                      and ToSeq(dst2) == Old(ToSeq(dst2))
                      and ToSeq(in_E2) == Old(ToSeq(in_E2))
                      and ToSeq(p1) == Old(ToSeq(p1))
                      and ToSeq(p2) == Old(ToSeq(p2))
                      and ToSeq(ostart) == Old(ToSeq(ostart))
                      and ToSeq(oevt) == Old(ToSeq(oevt))
                      and ToSeq(odst) == Old(ToSeq(odst)))
            Invariant(input_ok(n1, m, start1, evt1, dst1, in_E1) and input_ok(n2, m, start2, evt2, dst2, in_E2))
            Invariant(pairs_ok(n1, n2, p1, p2) and blocks_ok(len(p1), ostart, len(oevt)))
            Invariant(targets_ok(len(p1), oevt, odst))
            Invariant(len(start1) == n1 + 1 and len(start2) == n2 + 1 and len(ostart) == len(p1) + 1)
            Invariant(0 <= i and i < len(p1) and x1 == p1[i] and x2 == p2[i] and hi == ostart[i + 1])
            Invariant(0 <= x1 and x1 < n1 and 0 <= x2 and x2 < n2)
            Invariant(ostart[i] <= k and k <= hi and hi <= len(oevt))
            Invariant(hi2 == start2[x2 + 1] and start2[x2] <= j2 and j2 <= hi2)
            Invariant(0 <= k and k <= len(oevt) and len(ostate) == k and len(osrc1) == k and len(osrc2) == k)
            Invariant(sound_ok(start1, evt1, dst1, in_E1, start2, evt2, dst2, in_E2, p1, p2, ostart, oevt,
                               odst, ostate, osrc1, osrc2, k))
            f = evt2[j2]
            if not in_E1[f]:
                if k >= hi or oevt[k] != f or p1[odst[k]] != x1 or p2[odst[k]] != dst2[j2]:
                    return False
                Assert(move_ok(start1, evt1, dst1, in_E1, start2, evt2, dst2, in_E2, ostart,
                               i, x1, x2, k, f, p1[odst[k]], p2[odst[k]], -1, j2))
                record(ostate, osrc1, osrc2, i, -1, j2)
                k += 1
            j2 += 1
        if k != hi:
            return False
        i += 1
    return True
