"""
Funcions relevant to event diagnosis.
"""
import DESops as d
import time
from collections import deque
from typing import Any, Dict, List, Optional, Set, Tuple, Union

import pydash
from tqdm import tqdm

from DESops.automata.automata import _Automata
from DESops.random_automata.generate import generate
from DESops.automata.DFA import DFA
from DESops.automata.event import Event
from DESops.automata.NFA import NFA
from DESops.basic_operations.unary import find_inacc
from DESops.error import MissingAttributeError
from DESops.basic_operations import composition
EventSet = Set[Event]
Automata_t = Union[DFA, NFA]

def delete_all_specific_edge(G: Automata_t, target: Event) -> Automata_t:
    """
    Deletes all instances of a specific event (target) in a given automata (G)
    """
    G_N = NFA(G)
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
            x1_dst = list()
            x2_dst = list()
            evt = list()
            if x1[1] and x2[1] == True: 
                marked = True
            if e not in unobservable and e in active_both:
                x1_dst.append(G_N.vs[active_x1[e]]) # fN(x1,e)
                x2_dst.append(G_f.vs[active_x2[e]]) # f(x2,e)
                evt.append(Event("("+ e.label+","+ e.label+")"))
            elif e in unobservable:
                if e != target and e in active_both: 
                    x1_dst.append(G_N.vs[active_x1[e]]) # fN(x1,e)
                    x2_dst.append(x2[0])
                    evt.append(Event("("+e.label+",eps)")) 
                    x1_dst.append(x1[0])
                    x2_dst.append(G_f.vs[active_x2[e]]) # f(x2,e)
                    evt.append(Event("(eps," +e.label+")"))
                elif e != target and e in active_x1:
                    x1_dst.append(G_N.vs[active_x1[e]]) # fN(x1,e)
                    x2_dst.append(x2[0])
                    evt.append(Event("("+e.label+",eps)")) 
                elif e != target and e in active_x2:
                    x1_dst.append(x1[0])
                    x2_dst.append(G_f.vs[active_x2[e]]) # f(x2,e)
                    evt.append(Event("(eps," +e.label+")"))
                elif e == target:
                    marked = True
                    x1_dst.append(x1[0]) # x1
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
                    if marked:
                        queue.append(((x1_dst[i],True), (x2_dst[i],True)))
                    else:
                        queue.append(((x1_dst[i],False), (x2_dst[i],False)))

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
    return Ver 

def polynomial_test(G: Automata_t, target: Event) -> bool:
    ver = verifier(G, target)
    unmarked_states = [v for v in ver.vs if v["marked"] != True]
    ver.delete_vertices(unmarked_states)
    tarjan = tarjans_algorithm(ver)
    scc = tarjan.strongly_connected_components(ver.vs[0]["name"])
    for g in scc:
        for v in g:
            if len(g) == 1 and is_self_loop(v) == False:
                continue
            else:
                for ev in v[0]["out"]:
                    event = str(ev[1])
                    i = event.find(',')
                    if event[i:] != ",eps)":
                        return False
    return True

def is_self_loop(vertex) -> bool:
    """
    Given an automata and vertex, returns True if the vertex contains
    a self loop, and false if it does not
    """
    try:
        vertex[0]["out"][0][0]
    except IndexError:
        return False
    else:
        for out in vertex[0]["out"]:
            if vertex[0].index == out[0]:
                return True
    return False

class tarjans_algorithm:
    """
    Computes tarjans algorithm, returns a list of strongly connected components
    along with their DFS index.
    """
    def __init__(self, G):
        self.G = G
        self.result = list()
        self.vertices = [v for v in G.vs]
        self.size = len(self.vertices)
        self.disc = [-1] * self.size
        self.low = [-1] * self.size
        self.OnStack = [False] * self.size
        self.st = []

    def strongly_connected_components(self, initial):
        """
        Driver function for tarjan's algorithm.
        """
        vertice_names = [v["name"] for v in self.vertices ]
        time = 0
        DFS_vertices = self.DFS(self.vertices[vertice_names.index(initial)])
        order = range(0, self.size)
        id_dict = dict(zip(DFS_vertices, order))
        for i in range(0, self.size):
            if self.disc[i] == -1:
                self.scc_util(i, time, id_dict, DFS_vertices)
        return self.result

    def scc_util(self, i, time, id_dict, DFS_vertices):
        self.disc[i] = time
        self.low[i] = time
        time += 1
        self.OnStack[i] = True
        self.st.append(i)
        try: 
            DFS_vertices[i].successors()
        except:
            pass
        else:
            for v in DFS_vertices[i].successors():
                if self.disc[id_dict.get(v,-1)] == -1:
                    self.scc_util(id_dict.get(v), time, id_dict, DFS_vertices)
                    self.low[i] = min(self.low[i], self.low[id_dict.get(v)])
                elif self.OnStack[id_dict.get(v)] == True:
                    self.low[i] = min(self.low[i], self.disc[id_dict.get(v)])
            w = -1
            if self.low[i] == self.disc[i]:
                scc = list()
                while w != i:
                    w = self.st.pop()
                    scc.append((DFS_vertices[w],w))
                    self.OnStack[w] = False
                self.result.append(scc)       
 
    def DFS(self, v) -> list:
        """
        Depth first search algorithm that returns 
        the order in which vertices were visited
        """
        d = []
        visited = set()
        self.DFSUtil(v, visited, d)
        for v in self.vertices:
            if v not in visited:
                self.DFSUtil(v, visited,d)
        return d

    def DFSUtil(self,v,visited,d):
        d.append(v)
        visited.add(v)
        for neighbor in v.successors():
            if neighbor not in visited:
                self.DFSUtil(neighbor,visited,d)

class johnsons_algorithm:
    """
    Computes johnson's algorithm, returns a list of 
    all cycles in a given automata.
    """
    def __init__(self, G):
        self.blocked_set = set()
        self.blocked_map = dict()
        self.stack = []
        self.all_cycles = list()
        self.vertices = [v for v in G.vs]

    def simple_cycles(self,G) -> list:
        start_index = 0
        initial = tarjans_algorithm(G)
        DFS_vertices = initial.DFS(G.vs[0])
        DFS_names = [v["name"] for v in DFS_vertices]
        while(start_index <= (len(self.vertices)-1)):
            subgraph = self.create_sub_graph(start_index, G, DFS_vertices)
            tarjan = tarjans_algorithm(subgraph)
            scc_graphs = tarjan.strongly_connected_components(DFS_names[start_index])
            least_vertex = self.find_least_vertex(scc_graphs, subgraph)
            if(least_vertex[0] != None):
                self.blocked_set.clear()
                self.blocked_map.clear()
                val = self.simple_cycles_util(least_vertex[0], least_vertex[0])
                start_index = DFS_names.index(least_vertex[0]["name"]) + 1
            else:
                break
        for v in self.vertices:
            if(self.is_self_loop(v)):
                self.all_cycles.append([v,v])
        return self.all_cycles

    def find_least_vertex(self,subgraphs,G):
        min_id = 2147483647
        min_vertex = None
        for graph in subgraphs: #add condition for self loop
            if len(graph) == 1:
                continue
            else:
                for v in graph:
                    if v[1] < min_id:
                        min_vertex = v[0]
                        min_id = v[1]
        return (min_vertex, min_id)

    def is_self_loop(self,vertex):
        try:
            out = vertex["out"][0][0]
        except IndexError:
            return False
        if vertex == self.vertices[out]:
            return True
        return False

    def create_sub_graph(self, index, G, DFS_vertices):
        """
        Given a starting index, creates a new subgraph excluding
        vertices with a DFS index less than the index
        """
        result = NFA(G)
        deleted_vertices = list()
        for x in range(0, index):
            deleted_vertices.append(DFS_vertices[x])
        result.delete_vertices(deleted_vertices)
        return result

    def simple_cycles_util(self, start, current):
        foundCycle = False
        self.stack.append(current)
        self.blocked_set.add(current)

        for neighbor in current.successors():
            if neighbor == start:
                self.stack.append(start)
                cycle = list()
                cycle.extend(self.stack)
                #cycle = cycle[::-1]
                self.stack.pop()
                self.all_cycles.append(cycle)
                foundCycle = True
            elif neighbor not in self.blocked_set:
                gotcycle = self.simple_cycles_util(start, neighbor)
                foundCycle = foundCycle or gotcycle
            
        if foundCycle:
            self.unblock(current)
        else:
            for neighbor in current.successors():
                if self.blocked_map.get(neighbor,-1) == -1:
                    self.blocked_map[neighbor] = [current]
                else:
                    self.blocked_map[neighbor].append(current)
        if(len(self.stack) > 0):
            self.stack.pop()
        return foundCycle
    
    def unblock(self, vertex):
        self.blocked_set.remove(vertex)
        if self.blocked_map.get(vertex,-1) != -1:
            for v in self.blocked_map.get(vertex):
                if v in self.blocked_set:
                    self.unblock(v)
            self.blocked_map.pop(vertex)
 
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
            "name": ((name, 'N'), (name, 'N')),
            "uncertain": False
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

    ext_diag.events = obs.events
    ext_diag.Euc.update(obs.Euc)
    ext_diag.Euo.update(obs.Euo)

    return ext_diag

def is_uncertain(dst_name) -> bool:
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
            "unobs_visit": False,
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
                    try:
                        G.vs[d]["unobs_visit"]
                    except:
                        if d == x1.index:
                            continue
                        obs_states = DFS_Euo_search(G,G.vs[d],result)
                    else:
                        if G.vs[d]["unobs_visit"] != True:
                            obs_states = DFS_Euo_search(G,G.vs[d],result)
                else: 
                    continue
                for state in obs_states:
                    state[0]["unobs_visit"] = False
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
                                "unobs_visit": False,
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

def DFS_Euo_search(G:Automata_t, V, result) -> set:
    vertices = [v for v in G.vs]
    visited = [False] * len(vertices)
    return DFS_Euo_search_util(G, V, result, vertices, visited)

def DFS_Euo_search_util(G:Automata_t, V, result:set, vertices:list, visited:list):
    visited[vertices.index(V)] = True
    G.vs[vertices.index(V)]["unobs_visit"] = True
    start = V
    active_x1 = {e[1]: e[0] for e in start["out"]}
    for e in active_x1:
        v = active_x1[e]
        if start.index == v and e not in G.Euo:
            result.add((vertices[v],e))
        elif visited[v] == False and G.vs[v]["unobs_visit"] != True:
            if e not in G.Euo:
                result.add((vertices[v],e))
            else:
                DFS_Euo_search(G, vertices[v], result)
    return result

def ext_diag_test(G:Automata_t, target: Event) -> bool:
    ext_diag = extended_diagnoser(G, target)
    test = johnsons_algorithm(ext_diag)
    cycles = test.simple_cycles(ext_diag)
    for c in cycles:
        count = 0
        for v in c:
            if v["uncertain"] == True:
                count += 1
        if count != len(c):
           cycles.remove(c)
    if len(cycles) == 0:
        return True
    # search for a cycle with all Y's
    for c in cycles:
        init_name = c[0]["name"]
        for name in init_name:
            if name[0][1] == 'Y' and name[1][1] == 'Y':
                result = list()
                find_Y_cycle(c,name,1,result)
                if len(result) > 0:
                    return False
    return True
    
def find_Y_cycle(cycle: list, origin: tuple, start: int, result: list):
    v = cycle[start]
    for name in v["name"]:
        if name[0][0] == origin[1][0]:
            if start != len(cycle)-1:
                find_Y_cycle(cycle, name, start+1, result)
            else:
                result.append(True)




F = d.read_fsm('diagnoser2.fsm.txt')
target = Event('c')
#d.plot(F)
"""F = generate(5,4,0,None,True,1,0,0,2,0)
print(F)
target = list(F.Euo)[0]
print(target)"""
"""GparA = composition.parallel(F, A_label)
print(composition.observer(GparA))"""
#print(verifier(F,target))
#d.plot(verifier(F,target))
#G = extended_diagnoser(F,target)
#G = extended_diagnoser(F, target)
print(prime_automata(F,target)[0])
begin_time = time.time()
print(polynomial_test(F, target))
print(ext_diag_test(F, target))
print(time.time()-begin_time)
#print(ext_diag_test(F, target))
#G = prime_automata(F, target)
#d.plot(G[0])
"""test = johnsons_algorithm(G)
cycles = test.simple_cycles(G)
for c in cycles:
    for v in c:
        print(v["name"])
    print("\n")"""

