"""
Functions related to the two-way observer method of verifying K-step opacity
"""
import warnings

from DESops.automata.DFA import DFA
from DESops.automata.NFA import NFA
from DESops.basic_operations import composition
from DESops.basic_operations.construct_reverse import reverse
from DESops.basic_operations.ureach import ureach_from_set_adj
from DESops.opacity.contract_secret_traces import contract_secret_traces
from DESops.opacity.language_functions import find_path_between


def verify_separate_k_step_opacity_TWO(
    g, k, secret_type=2, return_num_states=False, return_violating_path=False
):
    """
    Returns whether the given automaton with unobservable events and secret states is k-step opaque

    Returns: opaque(, num_states)(, violating_path)

    Parameters:
    g: the automaton
    k: the number of steps. If k == "infinite", then infinite-step opacity will be checked
    return_num_states: if True, the number of states in the constructed observers is returned as an additional value
    return_violating_path: if True, a list of observable events representing an opacity-violating path is returned as an additional value
    """
    g = contract_secret_traces(g, secret_type)

    # names need to be indices so we can find them from observer
    g.vs["name"] = g.vs.indices

    g_r = reverse(g)

    g_obs = composition.observer(g)

    if k == "infinite":
        g_r_obs = composition.observer(g_r)
    else:
        g_r_obs = first_k_observer(g_r, k)

    # states of two-way observer are pairs of states in the forward and reverse observers
    opaque = True
    for v1 in g_obs.vs:
        for v2 in g_r_obs.vs:
            # opacity is violated if any nonempty intersection contains only secret states
            common_states = v1["name"].intersection(v2["name"])
            if common_states:
                if all([g.vs[v]["secret"] for v in common_states]):
                    opaque = False
                    violating_ids = (v1.index, v2.index)
                    break
        if not opaque:
            break

    return_list = [opaque]

    if return_num_states:
        return_list.append(g_obs.vcount() + g_r_obs.vcount())

    if return_violating_path:
        if opaque:
            return_list.append(None)
        else:
            forward_path = find_path_between(g_obs, 0, violating_ids[0])
            reverse_path = find_path_between(g_r_obs, 0, violating_ids[1])
            reverse_path.reverse()
            return_list.append(forward_path + reverse_path)

    if len(return_list) == 1:
        return return_list[0]
    else:
        return tuple(return_list)


def first_k_observer(G, k) -> DFA:
    """
    Modified version of observer_comp function

    Partially constructs the observer of G; only state estimates reachable within k steps are included
    """
    observer = DFA()
    if not G.vcount():
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
    next_queue = list()

    # index tracks the current number of vertices in the graph
    index = 0

    # computing ureach for every singleton states
    # states_ureach = preprocessing_ureach(G)

    if isinstance(G, NFA):
        init_states = {v.index for v in G.vs if v["init"]}
    else:
        init_states = {0}

    # v0 = states_ureach[0]
    states_ureach = dict()
    v0 = frozenset(ureach_from_set_adj(init_states, G, G.Euo))
    states_ureach[frozenset(init_states)] = v0
    # name_v0 = "{" + ",".join(flatten_deep([G.vs["name"][v] for v in v0])) + "}"
    name_v0 = frozenset([G.vs["name"][v] for v in v0])
    marking = any([G.vs["marked"][v] for v in v0])
    vertice_names.insert(index, name_v0)
    vertice_number[v0] = index
    marked_list.insert(index, marking)

    index = index + 1
    next_queue.append(v0)
    # construct observer one layer of depth at a time, stopping after k steps
    for _ in range(k):
        current_queue = next_queue
        next_queue = list()
        while current_queue:
            v = current_queue.pop(0)

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
                # auxiliary ureach dictionary
                if next_state in states_ureach:
                    next_state = states_ureach[next_state]
                else:
                    key = next_state
                    next_state = frozenset(ureach_from_set_adj(key, G, G.Euo))
                    states_ureach[key] = next_state

                # updating lists for igraph construction
                if next_state in vertice_number.keys():
                    transition_list.append(
                        (vertice_number[v], vertice_number[next_state])
                    )
                    transition_label.append(ev)
                else:
                    # name_next_state = (
                    # "{" + ",".join(flatten_deep([G.vs["name"][v] for v in next_state])) + "}"
                    # )
                    name_next_state = frozenset([G.vs["name"][v] for v in next_state])
                    transition_list.append((vertice_number[v], index))
                    transition_label.append(ev)
                    vertice_number[next_state] = index
                    marking = any([G.vs["marked"][v] for v in next_state])
                    marked_list.insert(index, marking)
                    vertice_names.insert(index, name_next_state)
                    next_queue.append(next_state)
                    index = index + 1
                # (use observer.Out namedtuple)
                outgoing_v1v2.append(observer.Out(vertice_number[next_state], ev))
            outgoing_list.insert(vertice_number[v], outgoing_v1v2)

    # constructing DFA: igraph and events sets
    observer.add_vertices(index, vertice_names)
    observer.events = G.events - G.Euo
    observer.Euc.update(G.Euc - G.Euo)
    observer.Euo.clear()
    if observer.ecount():
        observer.vs["out"] = outgoing_list
    observer.vs["marked"] = marked_list
    observer.add_edges(transition_list, transition_label)
    return observer
