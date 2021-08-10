"""
Funcions relevant to event diagnosis.
"""
import time
from collections import deque
from typing import Any, Dict, List, Optional, Set, Tuple, Union

from DESops.basic_operations.cycle_detection import johnsons_algorithm
from DESops.basic_operations.cycle_detection import tarjans_algorithm
from DESops.basic_operations import cycle_detection
from DESops.automata.DFA import DFA
from DESops.automata.event import Event
from DESops.automata.NFA import NFA
from DESops.basic_operations.unary import find_inacc
from DESops.basic_operations import composition
EventSet = Set[Event]
Automata_t = Union[DFA, NFA]

def diagnoser(G: Automata_t, target: Event) -> Automata_t:
    """
    Constructs the diagnoser automaton of the input G based on the target event
    """
    A_label = DFA()
    A_label.add_vertices(2, names = ["N","Y"])
    A_label.add_edges([(0,1),(1,1)], labels = [target, target])
    A_label.Euo = {target} 
    GparA = composition.parallel(G, A_label)
    Obs = composition.observer(GparA)
    return Obs

def create_GN(G: Automata_t, target: Event) -> Automata_t:
    """
    Computes the GN, an automaton without the given target event. 
    """
    G_N = delete_all_specific_edge(G, [target])
    bad_states = find_inacc(G)
    G_N.delete_vertices_no_warning(bad_states)
    return G_N

def verifier(G_f: Automata_t, target: Event) -> Automata_t: 
    """
    Computes the verifier automata of the input G_f based on the target event
    """
    G_N = create_GN(G_f,target)
    unobservable = list(G_f.Euo)
    Ver = NFA()


    GN_x0 = (G_N.vs[0])
    Gf_x0 = (G_f.vs[0])
    Ver_vertices = [
        {
            "name": (GN_x0["name"], Gf_x0["name"]),
            "marked": GN_x0["marked"] and Gf_x0["marked"],
        }
    ]
    Ver_names = {Ver_vertices[0]["name"]: 0}
    Ver_edges = []  
    queue = deque([(GN_x0, Gf_x0)])
    while len(queue) > 0:
        x1, x2 = queue.popleft()
        active_x1 = {e[1]: e[0] for e in x1["out"]} #GN
        active_x2 = {e[1]: e[0] for e in x2["out"]} #Gf
        active_both = set(active_x1.keys()) & set(active_x2.keys())
        cur_name = (x1["name"], x2["name"])
        src_index = Ver_names[cur_name]
        for e in set(active_x1.keys()) | set(active_x2.keys()):
            marked = False
            x1_dst = list()
            x2_dst = list()
            evt = list()
            if e not in unobservable and e in active_both:
                x1_dst.append(G_N.vs[active_x1[e]]) # fN(x1,e)
                x2_dst.append(G_f.vs[active_x2[e]]) # f(x2,e)
                evt.append(Event("("+ e.label+","+ e.label+")"))
            elif e in unobservable:
                if e != target and e in active_both: 
                    x1_dst.append(G_N.vs[active_x1[e]]) # fN(x1,e)
                    x2_dst.append(x2)
                    evt.append(Event("("+e.label+",eps)")) 
                    x1_dst.append(x1)
                    x2_dst.append(G_f.vs[active_x2[e]]) # f(x2,e)
                    evt.append(Event("(eps," +e.label+")"))
                elif e != target and e in active_x1:
                    x1_dst.append(G_N.vs[active_x1[e]]) # fN(x1,e)
                    x2_dst.append(x2)
                    evt.append(Event("("+e.label+",eps)")) 
                elif e != target and e in active_x2:
                    x1_dst.append(x1)
                    x2_dst.append(G_f.vs[active_x2[e]]) # f(x2,e)
                    evt.append(Event("(eps," +e.label+")"))
                elif e == target:
                    marked = True
                    x1_dst.append(x1) # x1
                    x2_dst.append(G_f.vs[active_x2[e]]) # f(x2,ed)
                    evt.append(Event("(eps," +target.label+")"))
                    
            else:
                continue

            for i in range(0,len(x1_dst)):

                dst_name = (x1_dst[i]["name"], x2_dst[i]["name"])
                dst_index = Ver_names.get(dst_name)

                if dst_index is None:
                    Ver_vertices.append(
                        {
                            "name": dst_name,
                            "marked": x1_dst[i]["marked"] and x2_dst[i]["marked"],
                        }
                    )
                    dst_index = len(Ver_vertices)-1
                    Ver_names[dst_name] = dst_index
                    queue.append((x1_dst[i],x2_dst[i]))

                if marked:
                    x = Ver_names[dst_name]
                    Ver_vertices[x]["marked"] = True

                Ver_edges.append({"pair": (src_index, dst_index), "label": evt[i]}) 

    Ver.add_vertices(
        len(Ver_vertices),
        [v["name"] for v in Ver_vertices],
        [v["marked"] for v in Ver_vertices],
    )
    Ver.add_edges(
        [e["pair"] for e in Ver_edges], [e["label"] for e in Ver_edges]
    ) 
    Ver.events = G_f.events
    Ver.Euc.update(G_f.Euc)
    Ver.Euo.update(G_f.Euo)

    prime_marked_vertices = [v for v in Ver.vs if v["marked"] == True]
    BFS_marked_states(Ver,prime_marked_vertices)

    return Ver 

def BFS_marked_states(G:Automata_t, prime_marked_vertices:list()):
    """
    Helper function for the verifier to make sure all appropriate states are marked.
    """
    vertices = [v for v in G.vs]
    visited = [False] * len(vertices)
    for v in prime_marked_vertices:
        queue = []
        queue.append(v)
        visited[v.index] = True
        while len(queue) > 0:
            current = queue.pop(0)
            for neighbor in current.successors():
                if visited[neighbor.index] == False:
                    queue.append(neighbor)
                    visited[neighbor.index] = True
                    G.vs[neighbor.index]["marked"] = True

def polynomial_test(G: Automata_t, target: Event) -> bool:
    """
    Performs the polynomial test on a given automaton and event.
    """
    ver = verifier(G, target)
    unmarked_states = [v for v in ver.vs if v["marked"] != True]
    ver.delete_vertices_no_warning(unmarked_states)
    try:
        ver.vs[0]["name"]
    except IndexError:
        return True
    else:
        tarjan = tarjans_algorithm(ver)
        scc = tarjan.strongly_connected_components(ver.vs[0]["name"])
    indices = list()
    for g in scc:
        input = list()
        for v in g:
            if len(g) == 1 and cycle_detection.is_self_loop(v) == False:
                continue
            else:
                input.append(v[0].index)
        if len(input) > 0:
            indices.append(input)
    index = 0
    for g in scc:
        if len(g) == 1 and cycle_detection.is_self_loop(g[0]) == False:
            continue
        else:
            for v in g:
                for ev in v[0]["out"]:
                    event = str(ev[1])
                    i = event.find(',')
                    if event[i:] != ",eps)" and ev[0] in indices[index]:
                        return False
        index +=1
    return True

def extended_diagnoser(G:Automata_t, target: Event)->Automata_t:
    """
    Returns an extended diagnoser automata given an automata
    and target event
    """
    A_label = DFA()
    A_label.add_vertices(2, names = ["N","Y"])
    A_label.add_edges([(0,1),(1,1)], labels = [target, target])
    A_label.Euo = {target} 
    GparA = composition.parallel(G, A_label)
    prime_info = prime_automata(GparA, target)
    prime = prime_info[0]
    prev = prime_info[1]
    ext_diag = NFA()
    prime_x0 = prime.vs[0]
    for x in prime_x0["name"]: 
        name = str(x[0])
        break
    # The first vertex will always be the (NAME, 'N)', (NAME, 'N')
    Ext_diag_vertices = [
        {
            "name": (((name, 'N'), (name, 'N')),),
            "uncertain": False,
        }
    ]
    obs = composition.observer(prime)
    obs_x0 = obs.vs[0]
    Ext_diag_names = {Ext_diag_vertices[0]["name"]: 0}
    Ext_diag_edges = []  
    queue = deque([(obs_x0, Ext_diag_vertices[0]["name"])])
    while len(queue) > 0:
        x1 = queue.popleft()
        cur_name = x1[1]
        src_index = Ext_diag_names[cur_name]
        active_x1 = {e[1]: e[0] for e in x1[0]["out"]}
        for e in active_x1:
            dst_name = tuple()
            dst_1 = x1[0]
            dst_2 = obs.vs[active_x1[e]]
            state = list()
            # The following code iterates through the frozen
            # set for each vertex name tuple in order to properly
            # create the dst_name
            for first in x1[0]["name"]:
                for second in dst_2["name"]:
                    if first in prev[second]:
                        state.append((first,second))
            for x in state:
                dst_name += (x,)
            dst_index = Ext_diag_names.get(dst_name)
            uncertain = True

            if dst_index is None:
                Ext_diag_vertices.append(
                    {
                        "name": dst_name,
                        "uncertain": is_uncertain(dst_name),
                    }
                )
                dst_index = len(Ext_diag_vertices)-1
                Ext_diag_names[dst_name] = dst_index 
                queue.append((dst_2,dst_name))    
            Ext_diag_edges.append({"pair": (src_index, dst_index), "label": e}) 

    ext_diag.add_vertices(
        len(Ext_diag_vertices),
        [v["name"] for v in Ext_diag_vertices],
        uncertain = [v["uncertain"] for v in Ext_diag_vertices],
    )
    ext_diag.add_edges(
        [e["pair"] for e in Ext_diag_edges], [e["label"] for e in Ext_diag_edges]
    )   

    ext_diag.events = G.events
    ext_diag.Euc.update(G.Euc)
    ext_diag.Euo.update(G.Euo)
    return ext_diag

def is_uncertain(dst_name) -> bool:
    """
    Returns a boolean value based on whether or not a given state is uncertain.
    """
    if len(dst_name) == 1:
        return False 
    else:
        Y = False
        N = False
        for name in dst_name:
            if name[1][1] == 'N':
                N = True
            elif name[1][1] == 'Y':
                Y = True
        if Y == True and N == True:
            return True
    return False

def prime_automata(G: Automata_t, target: Event) -> list:
    """
    Returns a prime automata based on a given automata and
    target event and dictionary that shows the previous state of each vertex
    """
    #First take the parallel composition of A label and G
    G_x0 = G.vs[0]
    G_x0["init"] = True
    prime = NFA()
    prev = dict()
    # create an attribute called unobs_visit where events that
    # are unobservable and have been visited are marked True
    prime_vertices = [
        {
            "name": G_x0["name"],
        }
    ]
    unobservable = G.Euo
    prime_names = {prime_vertices[0]["name"]: 0}
    prime_edges = [] 
    queue = deque([G_x0])
    while len(queue) > 0:
        x1 = queue.popleft()
        cur_name = x1["name"]
        src_index = prime_names[cur_name]
        active_x1 = dict()
        for q in x1["out"]:
            if active_x1.get(q[1],-1) == -1:
                active_x1[q[1]] = [q[0]]
            else:
                active_x1[q[1]].append(q[0])
        for e in active_x1:
            for d in active_x1[e]:
                result = set()
                if e not in unobservable: #if e is observable
                    obs_states = [(G.vs[d],e)]
                elif e in unobservable:
                    if d == x1.index:
                        continue
                    else:
                        obs_states = BFS_Euo_search(G,G.vs[d],result)
                else: 
                    continue
                for state in obs_states:
                    dst_name = state[0]["name"]
                    if prev.get(dst_name,-1) == -1:
                        prev[dst_name] = [cur_name]
                    else:
                        prev[dst_name].append(cur_name)
                    dst_index = prime_names.get(dst_name)
                    if dst_index is None:
                        prime_vertices.append(
                            {
                                "name": dst_name,
                            }
                        ) 
                        dst_index = (len(prime_vertices)-1)
                        prime_names[dst_name] = dst_index
                        queue.append(state[0])
                    if {"pair": (src_index, dst_index), "label": state[1]} not in prime_edges:
                        prime_edges.append({"pair": (src_index, dst_index), "label": state[1]})

    prime.add_vertices(
        len(prime_vertices),
        [v["name"] for v in prime_vertices],
    )
    prime.add_edges(
        [e["pair"] for e in prime_edges], [e["label"] for e in prime_edges]
    )   

    prime.events = G.events
    prime.Euc.update(G.Euc)
    prime.Euo.update(G.Euo)
    prime.vs[0]["init"] = True
    return [prime,prev]

def BFS_Euo_search(G:Automata_t, V, result) -> set:
    """
    Helper function for prime automata to find all reachable unobservable events.
    """
    vertices = [v for v in G.vs]
    visited = dict()
    for i in range(0,len(vertices)):
        visited[i] = [(-1,'z')]
    queue = []
    queue.append(V)
    while len(queue) > 0:
        current = queue.pop(0)
        active_x1 = {e[1]: e[0] for e in current["out"]}
        for e in active_x1:
            v = active_x1[e]
            if current.index == v and e not in G.Euo:
                result.add((vertices[v],e))
            elif (v,e) not in visited[current.index]:
                visited[current.index].append((v,e))
                if e not in G.Euo:
                    result.add((vertices[v],e))
                else:
                    queue.append(vertices[v])
    return result


def ext_diag_test(G:Automata_t, target: Event) -> bool:
    """
    Performs extended diagnoser test based on given automaton and event.
    """
    G_uo = delete_obs_events(G)
    if cycle_detection.contains_cycle(G_uo) == True:
        print("Cycle of unobservable events detected. Does not meet the required assumption for extended diagnoser test. Please use the polynomial test.")
        return
    ext_diag = extended_diagnoser(G, target)
    test = johnsons_algorithm(ext_diag)
    cycles = test.simple_cycles(ext_diag)
    unmarked_cycles = list()
    for c in cycles:
        count = 0
        for v in c:
            if v["uncertain"] == True:
                count += 1
        if count == len(c) and count != 0:
           unmarked_cycles.append(c)
    if len(unmarked_cycles) == 0:
        return True
    # search for a cycle with all Y's
    for c in unmarked_cycles:
        init_name = c[0]["name"]
        for name in init_name:
            if name[0][1] == 'Y' and name[1][1] == 'Y':
                result = list()
                find_Y_cycle(c,name,1,result)
                if len(result) > 0:
                    return False
    return True
    
def find_Y_cycle(cycle: list, origin: tuple, start: int, result: list):
    """
    Returns a list of all cycles that solely contain 'Y'.
    """
    v = cycle[start]
    for name in v["name"]:
        if name[0][0] == origin[1][0]:
            if start != len(cycle)-1:
                find_Y_cycle(cycle, name, start+1, result)
            else:
                result.append(True)
                
def delete_all_specific_edge(G: Automata_t, target: list()) -> Automata_t:
    """
    Deletes all instances of a specific event (target) in a copy of a given automata (G) and returns the copy.
    """
    G_N = NFA(G)
    deleted_edges = [v for v in G.es if v["label"] in target]
    G_N.delete_edges(deleted_edges)
    return G_N

def delete_obs_events(G:Automata_t) -> Automata_t:
    """
    Deletes all observable events in an automaton.
    """
    obs_events = [e for e in G.events if e not in G.Euo]
    G_uo = delete_all_specific_edge(G,obs_events)
    return G_uo

 
    
