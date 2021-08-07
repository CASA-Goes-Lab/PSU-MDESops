"""
Funcions relevant to cycle detection.
"""
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
from DESops.basic_operations import composition
from DESops import diagnoser
EventSet = Set[Event]
Automata_t = Union[DFA, NFA]

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
 
    def DFS(self, V) -> list:
        """
        Depth first search algorithm that returns 
        the order in which vertices were visited
        """
        d = []
        visited = set()
        self.DFSUtil(V,visited,d)
        for v in self.vertices:
            if v not in visited:
                self.DFSUtil(v,visited,d)
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
            vertex["out"][0][0]
        except IndexError:
            return False
        else:
            for out in vertex["out"]:
                if vertex.index == out[0]:
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
                foundCycle = gotcycle or foundCycle
            
        if foundCycle == True:
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

def contains_cycle(G:Automata_t):
    """
    Returns true if graph is cyclic otherwise it is false.
    """
    vertices = [v for v in G.vs]
    visited = [False] * (len(vertices))
    stack = [False] * (len(vertices))
    for v in vertices:
        if visited[v.index] == False:
            if contains_cycle_util(v,visited,stack) == True:
                return True
    return False

def contains_cycle_util(v, visited, stack):
    """
    Floyd's algorithm helper function.
    """
    visited[v.index] = True
    stack[v.index] = True 
    for neighbor in v.successors():
        if visited[neighbor.index] == False:
            if contains_cycle_util(neighbor, visited, stack) == True:
                return True
        elif stack[neighbor.index] == True:
            return True

    stack[v.index] = False
    return False
