import itertools
import os
import subprocess
import time

import igraph as ig

from DESops.automata.DFA import DFA
from DESops.automata.event import Event

from ...basic_operations.unary import find_inacc


def ISDA(A, Ea):
    ISDA = DFA(A)
    M = [v.index for v in ISDA.vs.select(dead_eq=1)]
    ISDA.delete_vertices(M)
    Euc = A.Euc.union(ISDA.Euc)
    print(Euc)
    preG = A
    preH = ISDA
    # Check each state to see if the supervisor improperly disables uncontrollable events;
    # those states must be removed.
    preG_name_dict = {v["name"]: v for v in preG.vs()}

    badstates = {1}
    while len(badstates) > 0:
        badstates = set()
        for vH in preH.vs:
            vG = preG_name_dict[vH["name"]]
            # vG = preG.vs.find(name_eq=vH["name"])

            evG = {x[1] for x in vG["out"]}
            evH = {x[1] for x in vH["out"]}
            evAH = {x[1] for x in vG["out"] if x[1] in Ea or "del" in x[1].name()}

            if evG != evH:
                for e in evG - evH:
                    if e in preG.Euc:
                        badstates.add(vH.index)
                        continue
                    if (
                        e in Ea
                        and e not in evAH
                        and "".join([e.name(), "_del"]) not in evAH
                    ):
                        badstates.add(vH.index)
                        continue
                        # print(vH["name"])

        preH.delete_vertices(badstates)

    # remove inaccessible states:
    inacc_states = find_inacc(preH)
    preH.delete_vertices(inacc_states)
    print(len(preH.vs))
    return preH
