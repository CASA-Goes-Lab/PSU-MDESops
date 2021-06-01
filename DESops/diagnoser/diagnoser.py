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

def diagnoser(G: Automata_t, target: Event) -> Automata_t:
    """
    Computes the diagnoser automata of the input G based on the target event
    """
    A_label = DFA()
    A_label.add_vertices(2, names = ["N","Y"])
    A_label.add_edges([(0,1),(1,1)], labels = [target, target])
    A_label.Euo = {target}  
    GparA = d.composition.parallel(G, A_label)
    Obs = d.composition.observer(GparA)
    return Obs

def delete_all_specific_edge(G: Automata_t, target: Event) -> Automata_t:
    """
    Deletes all instances of a specific event (target) in a given automata (G)
    """
    G_N = d.NFA(G)
    deleted_edges = [v for v in G_N.es if v["label"] ==target]
    G_N.delete_edges(deleted_edges)
    bad_states = find_inacc(G_N)
    G_N.delete_vertices(bad_states)
    return G_N

def verifier(G_f: Automata_t, target: Event) -> Automata_t: 
    """
    Computes the verifier automata of the input G_f based on the target event
    """
    G_N = delete_all_specific_edge(G_f, target)
    unobservable = list(G_f.Euo)
    Marked_States = list()
    Ver = NFA()

    GN_x0 = (G_N.vs[0],False)
    Gf_x0 = (G_f.vs[0],False)
    Ver_vertices = [
        {
            "name": (GN_x0[0]["name"], Gf_x0[0]["name"]),
            "marked": GN_x0[0]["marked"] and Gf_x0[0]["marked"],
        }
    ]
    Ver_names = {Ver_vertices[0]["name"]: 0}
    Ver_edges = []  

    queue = deque([(GN_x0, Gf_x0)])
    while len(queue) > 0:
        x1, x2 = queue.popleft()
        active_x1 = {e[1]: e[0] for e in x1[0]["out"]} #GN
        active_x2 = {e[1]: e[0] for e in x2[0]["out"]} #Gf
        active_both = set(active_x1.keys()) & set(active_x2.keys())
        cur_name = (x1[0]["name"], x2[0]["name"])
        src_index = Ver_names[cur_name]
        for e in set(active_x1.keys()) | set(active_x2.keys()):
            marked = False
            x3_dst = None
            x4_dst = None
            if x1[1] and x2[1] == True: 
                marked = True
            if e not in unobservable and e in active_both:
                x1_dst = G_N.vs[active_x1[e]] # fN(x1,e)
                x2_dst = G_f.vs[active_x2[e]] # f(x2,e)
                evt = Event("("+ e.label+","+ e.label+")") 
            elif e in unobservable:
                if e != target and e in active_both: 
                    x1_dst = G_N.vs[active_x1[e]] # fN(x1,e)
                    x2_dst = x2[0]
                    evt = Event("("+e.label+", eps)") 
                    x3_dst = x1[0]
                    x4_dst = G_f.vs[active_x2[e]] # f(x2,e)
                    evt2 = Event("(eps," +e.label+")")
                elif e != target and e in active_x1:
                    x1_dst = G_N.vs[active_x1[e]] # fN(x1,e)
                    x2_dst = x2[0]
                    evt = Event("("+e.label+", eps)") 
                elif e != target and e in active_x2:
                    x1_dst = x1[0]
                    x2_dst = G_f.vs[active_x2[e]] # f(x2,e)
                    evt = Event("(eps," +e.label+")")
                elif e == target:
                    marked = True
                    x1_dst = x1[0] # x1
                    x2_dst = G_f.vs[active_x2[e]] # f(x2,ed)
                    evt = Event("(eps," +target.label+")")
                    
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
                dst_index = len(Ver_vertices)-1
                Ver_names[dst_name] = dst_index
                if marked:
                    queue.append(((x1_dst,True), (x2_dst,True)))
                else:
                    queue.append(((x1_dst,False), (x2_dst,False)))

            if marked:
                i = Ver_names[dst_name]
                Ver_vertices[i]["marked"] = True

            Ver_edges.append({"pair": (src_index, dst_index), "label": evt}) 

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
                if marked:
                    queue.append(((x3_dst,True), (x4_dst,True)))
                else:
                    queue.append(((x3_dst,False), (x4_dst,False)))

                Ver_edges.append({"pair": (src_index, dst_index2), "label": evt2})
  
    Ver.add_vertices(
        len(Ver_vertices),
        [v["name"] for v in Ver_vertices],
        [v["marked"] for v in Ver_vertices],
    )
    Ver.add_edges(
        [e["pair"] for e in Ver_edges], [e["label"] for e in Ver_edges]
    )   

    Ver.events = G_f.events | G_N.events
    Ver.Euc.update(G_f.Euc | G_N.Euc)
    Ver.Euo.update(G_f.Euo | G_N.Euo)

    return Ver

def polynomial_test(G: Automata_t, target: Event) -> bool:
    ver = verifier(G, target)


G_f = d.read_fsm("verifier.fsm.txt")
evt = Event("ed")
ver = verifier(G_f, evt)
d.plot(ver)

"""
detect cycle pseudocode

def detect_cycle(G: Automata_t) -> bool:
    x = G.vs[0]
    while x is defined:
        if x is visited:
            return true
        x is visited
        x = next state to check
    return false
"""
