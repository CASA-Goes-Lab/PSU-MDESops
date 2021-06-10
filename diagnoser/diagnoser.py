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
    d.plot(A_label) 
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
                    evt = Event("("+e.label+",eps)") 
                    x3_dst = x1[0]
                    x4_dst = G_f.vs[active_x2[e]] # f(x2,e)
                    evt2 = Event("(eps," +e.label+")")
                elif e != target and e in active_x1:
                    x1_dst = G_N.vs[active_x1[e]] # fN(x1,e)
                    x2_dst = x2[0]
                    evt = Event("("+e.label+",eps)") 
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
    unmarked_states = [v for v in ver.vs if v["marked"] == False]
    ver.delete_vertices(unmarked_states)
    tarjan = tarjans_algorithm(ver)
    scc = tarjan.strongly_connected_components()
    single_sccs = [v for v in scc if len(v) == 1]
    if len(single_sccs) == len(scc):
        return True 
    for g in scc:
        for v in g:
            event = str(v["out"][0][1])
            i = event.find(',')
            if event[i:] != ",eps)":
                return False
    return True

class tarjans_algorithm:

    def __init__(self, G):
        self.result = list()
        self.vertices = [v for v in G.vs]
        self.size = len(self.vertices)
        self.disc = [-1] * self.size
        self.low = [-1] * self.size
        self.OnStack = [False] * self.size
        self.st = []

    def strongly_connected_components(self):
        time = 0
        DFS_vertices = self.DFS(self.vertices[0])
        order = range(0, len(DFS_vertices))
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
        return d

    def DFSUtil(self,v,visited,d):
        d.append(v)
        visited.add(v)
        for neighbour in v.successors():
            if neighbour not in visited:
                self.DFSUtil(neighbour,visited,d)   

class johnsons_algorithm:

    def __init__(self, G):
        self.blocked_set = set()
        self.blocked_map = dict()
        self.stack = []
        self.all_cycles = list()
        self.vertices = [v for v in G.vs]

    def simple_cycles(self,G) -> list:
        start_index = 0 #Question 1: should this be 0
        initial = tarjans_algorithm(G)
        DFS_vertices = initial.DFS(G.vs[0])
        while(start_index <= (len(self.vertices)-1)):
            subgraph = self.create_sub_graph(start_index, G, DFS_vertices)
            print(subgraph)
            tarjan = tarjans_algorithm(subgraph)
            DFS_indices = tarjan.DFS(subgraph.vs[0])
            scc_graphs = tarjan.strongly_connected_components()
            least_vertex = self.find_least_vertex(scc_graphs, subgraph)
            if(least_vertex[0] != None):
                self.blocked_set.clear()
                self.blocked_map.clear()
                val = self.find_cycles(least_vertex[0], least_vertex[0])
                start_index += 1#DFS_indices.index(least_vertex[0]) + start_index + 1
            else:
                break
        return self.all_cycles

    def find_least_vertex(self,subgraphs,G):
        min = 2147483647
        min_id = -1
        min_vertex = None
        for graph in subgraphs: #add condition for self loop
            if len(graph) == 1:
                for s in graph:
                    if self.is_self_loop(s[0],G):
                        min_vertex = s[0]
                        min_id = s[1]
                    else:
                        continue
            else:
                for v in graph:
                    if v[1] < min:
                        min_vertex = v[0]
                        min_id = v[1]
        return (min_vertex, min_id)

    def is_self_loop(self,vertex, G):
        try:
            out = vertex["out"][0][0]
        except IndexError:
            return False
        if vertex == G.vs[out]:
            return True
        return False

    def create_sub_graph(self, index, G, DFS_vertices):
        result = d.NFA(G)
        deleted_vertices = list()
        for x in range(0, index):
            deleted_vertices.append(DFS_vertices[x])
        result.delete_vertices(deleted_vertices)
        while result.vs[0]["out"] == [] and result.vs[0]["name"] != DFS_vertices[index]["name"]:
            result.delete_vertices([result.vs[0]])
        bad_states = find_inacc(result)
        result.delete_vertices(bad_states)
        return result

    def find_cycles(self, start, current):
        foundCycle = False
        self.stack.append(current)
        self.blocked_set.add(current)

        for neighbor in current.successors():
            if neighbor == start:
                self.stack.append(start)
                cycle = list()
                cycle.extend(self.stack)
                cycle = cycle[::-1]
                self.stack.pop()
                self.all_cycles.append(cycle)
                foundCycle = True
            elif neighbor not in self.blocked_set:
                gotcycle = self.find_cycles(start, neighbor)
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
    diag = diagnoser(G, target)
    ext_diag = NFA()
    diag_x0 = diag.vs[0]
    for x in diag_x0["name"]:
        name = str(x[0])
        break
    Ext_diag_vertices = [
        {
            "name": ((name,'N'), (name,'N')),
            "marked": False and False,
        }
    ]
    Ext_diag_names = {Ext_diag_vertices[0]["name"]: 0}
    Ext_diag_edges = []  
    queue = deque([(diag_x0, Ext_diag_vertices[0]["name"])])
    while len(queue) > 0:
        x1 = queue.popleft()
        cur_name = x1[1]
        src_index = Ext_diag_names[cur_name]
        active_x1 = {e[1]: e[0] for e in x1[0]["out"]}
        for e in active_x1:
            dst_1 = x1[0]
            dst_2 = diag.vs[active_x1[e]]
            for x in dst_1["name"]:
                for y in dst_2["name"]:
                    dst_name = (x,y)
                    break
                break
            dst_index = Ext_diag_names.get(dst_name)
            if dst_index is None:
                Ext_diag_vertices.append(
                    {
                        "name": dst_name,
                        "marked": dst_1["marked"] and dst_2["marked"],
                    }
                )
                dst_index = len(Ext_diag_vertices)-1
                Ext_diag_names[dst_name] = dst_index 
                queue.append((dst_2,dst_name))    
            Ext_diag_edges.append({"pair": (src_index, dst_index), "label": e}) 

    ext_diag.add_vertices(
        len(Ext_diag_vertices),
        [v["name"] for v in Ext_diag_vertices],
        [v["marked"] for v in Ext_diag_vertices],
    )
    ext_diag.add_edges(
        [e["pair"] for e in Ext_diag_edges], [e["label"] for e in Ext_diag_edges]
    )   

    ext_diag.events = diag.events
    ext_diag.Euc.update(diag.Euc)
    ext_diag.Euo.update(diag.Euo)

    return ext_diag


G = d.read_fsm('strongly_connected.fsm.txt')
#d.plot(G)
test = johnsons_algorithm(G)
tarjan = tarjans_algorithm(G)
cycles = test.simple_cycles(G)
for c in cycles:
    for v in c:
        print(v["name"])
    print("\n")