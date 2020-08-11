# pylint: disable=C0103

import warnings
from collections import OrderedDict

from pydash import flatten_deep

from DESops.automata.DFA import DFA
from DESops.automata.NFA import NFA


def observer_comp(G) -> DFA:
    """
    Compute the observer automata of the input G
    G should be a DFA, NFA or PFA

    Returns the observer as a DFA
    """
    observer = DFA()
    if not G.vcount() or G is None:
        warnings.warn(
            "Observer operation with an empty automaton-return an empty automaton"
        )
        return observer

    vertice_names = list()  # list of vertex names for igraph construction
    vertice_number = dict()  # dictionary vertex_names -> vertex_id
    outgoing_list = list()  # list of outgoing lists for each vertex
    marked_list = list()  # list with vertices marking
    transition_list = list()  # list of transitions for igraph construction
    transition_label = list()  # list os transitions label for igraph construction

    # BFS queue that holds states that must be visited
    queue = list()

    # index tracks the current number of vertices in the graph
    index = 0

    if isinstance(G, NFA):
        init_states = frozenset(v.index for v in G.vs if v["init"])
    else:
        init_states = frozenset({0})

    # Makes Euo hashable for UR dict key:
    Euo = frozenset(G.Euo)

    # Find UR from initial state(s):
    v0 = G.UR.from_set(init_states, Euo, freeze_result=True)

    name_v0 = frozenset([G.vs["name"][v] for v in v0])
    marking = any([G.vs["marked"][v] for v in v0])
    vertice_names.insert(index, name_v0)
    vertice_number[v0] = index
    marked_list.insert(index, marking)

    index = index + 1
    queue.append(v0)
    while queue:
        v = queue.pop(0)

        # finding observable adjacent from v
        adj_states = dict()
        for vert in v:
            for target, event in G.vs["out"][vert]:
                if event in adj_states and event not in G.Euo:
                    adj_states[event].add(target)
                elif event not in adj_states and event not in G.Euo:
                    s = set()
                    s.add(target)
                    adj_states[event] = s

        # print(adj_states)
        outgoing_v1v2 = list()
        for ev in adj_states.keys():
            next_state = frozenset(adj_states[ev])

            next_state = G.UR.from_set(next_state, Euo, freeze_result=True)
            # updating lists for igraph construction
            if next_state in vertice_number.keys():
                transition_list.append((vertice_number[v], vertice_number[next_state]))
                transition_label.append(ev)
            else:
                name_next_state = frozenset([G.vs["name"][v] for v in next_state])
                transition_list.append((vertice_number[v], index))
                transition_label.append(ev)
                vertice_number[next_state] = index
                marking = any([G.vs["marked"][v] for v in next_state])
                marked_list.insert(index, marking)
                vertice_names.insert(index, name_next_state)
                queue.append(next_state)
                index = index + 1
            outgoing_v1v2.append(observer.Out(vertice_number[next_state], ev))
        outgoing_list.insert(vertice_number[v], outgoing_v1v2)

    # constructing DFA: igraph and events sets
    observer.add_vertices(index, vertice_names)
    observer.events = G.events - G.Euo
    observer.Euc = G.Euc - G.Euo
    observer.Euo = set()
    observer.vs["out"] = outgoing_list
    observer.vs["marked"] = marked_list
    observer.add_edges(transition_list, transition_label)
    return observer
