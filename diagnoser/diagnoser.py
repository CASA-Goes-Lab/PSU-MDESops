"""
Funcions relevant to event diagnosis.
"""
import DESops as d
from collections import deque
from typing import Any, Dict, List, Optional, Set, Tuple, Union

import pydash
from tqdm import tqdm

from DESops.automata.automata import _Automata
from DESops.automata.DFA import DFA
from DESops.automata.event import Event
from DESops.automata.NFA import NFA
from DESops.basic_operations.unary import find_inacc
from DESops.error import MissingAttributeError

EventSet = Set[Event]
Automata_t = Union[DFA, NFA]

def diagnoser(G: Automata_t) -> Automata_t:
    if G.vcount() == 0:
    # check for empty automata
        return DFA()
    A_label = d.read_fsm('A_label.fsm.txt')
    GparA = d.composition.parallel(G, A_label)
    Obs = d.composition.observer(GparA)
    return Obs

def polynomial(G1: Automata_t, target) -> bool:
    G2 = G1
    bad_states = find_inacc(G1)
    # identify inaccessible states in G1, and delete them from G2
    G2.delete_vertices(list(bad_states))

    unobservable = list(G1.Euo.union(G2.Euo))
    Ver = DFA()

    G1_x0 = G1.vs[0]
    G2_x0 = G2.vs[0]
    Ver_vertices = [
        {
            "name": (G1_x0["name"], G2_x0["name"]),
            "marked": G1_x0["marked"] and G2_x0["marked"],
        }
    ]
    Ver_names = {Ver_vertices[0]["name"]: 0}
    Ver_edges = []  

    queue = deque([(G1_x0, G2_x0)])
    while len(queue) > 0:
        x1, x2 = queue.popleft()
        active_x1 = {e[1]: e[0] for e in x1["out"]}
        active_x2 = {e[1]: e[0] for e in x2["out"]}
        active_both = set(active_x1.keys()) & set(active_x2.keys())
        cur_name = (x1["name"], x2["name"])
        src_index = Ver_names[cur_name]

        for e in active_both:
            x3_dst = None
            x4_dst = None
            if e not in unobservable:
                x1_dst = G2.vs[active_x1[e]] # fN(x1,e)
                x2_dst = G1.vs[active_x2[e]] # f(x2,e)
            elif e != target:
                x1_dst = G2.vs[active_x1[e]] # fN(x1,e)
                x2_dst = x2 # x2
                x3_dst = x1 # x1
                x4_dst = G1.vs[active_x2[e]] # f(x2,e)
            elif e == target:
                x1_dst = x1 # x1
                x2_dst = G2.vs[active_x2[target]] # f(x2,ed)
            else:
                continue

            dst_name = (x1_dst["name"], x2_dst["name"])
            dst_index = Ver_names.get(dst_name)

            if dst_index is None:
                Ver_vertices.append(
                    {
                        "name": dst_name,
                        "marked": x1_dst["marked"] and x2_dst["marked"],
                    }
                )
                dst_index = len(Ver_vertices) - 1
                Ver_names[dst_name] = dst_index
                queue.append((x1_dst, x2_dst))

            # unsure about this section
            Ver_edges.append({"pair": (src_index, dst_index), "label": e}) 
            Ver_edges.append({"pair": (src_index, dst_index), "label": target})

            if x3_dst and x4_dst != None:
                dst_name2 = (x3_dst["name"], x4_dst["name"])
                dst_index2 = Ver_names.get(dst_name2)

                if dst_index2 is None:
                    Ver_vertices.append(
                    {
                        "name": dst_name2,
                        "marked": x3_dst["marked"] and x4_dst["marked"],
                    }
                )
                dst_index2 = len(Ver_vertices) - 1
                Ver_names[dst_name2] = dst_index2
                queue.append((x3_dst, x4_dst))

            Ver_edges.append({"pair": (src_index, dst_index2), "label": e})             

        Ver.add_vertices(
            len(Ver_vertices),
            [v["name"] for v in Ver_vertices],
            [v["marked"] for v in Ver_vertices],
        )
        Ver.add_edges(
            [e["pair"] for e in Ver_edges], [e["label"] for e in Ver_edges]
        )   
        Ver.events = G1.events | G2.events
        Ver.Euc.update(G1.Euc | G2.Euc)
        Ver.Euo.update(G1.Euo | G2.Euo)

        G1 = Ver

    return True

test = d.read_fsm('lecture_example.fsm.txt')
d.plot(diagnoser(test))

