# pylint: disable=C0103
"""
Functions relevant to constructing an observer automaton from a partially-observed automaton.

Only observer_comp is used outside this module; the rest are included as helper functions
only used by observer_comp.
"""


import warnings
from collections import OrderedDict
from pydash import flatten_deep

from DESops.automata.DFA import DFA
from DESops.basic_operations.ureach import ureach_from_set_adj


def observer_comp(G) -> DFA:
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
    queue = list()

    # index tracks the current number of vertices in the graph
    index = 0

    # computing ureach for every singleton states
    # states_ureach = preprocessing_ureach(G)

    # v0 = states_ureach[0]
    states_ureach = dict()
    v0 = frozenset(ureach_from_set_adj({0}, G, G.Euo))
    states_ureach[frozenset({0})] = v0
    name_v0 = "{" + ",".join(flatten_deep([G.vs["name"][v] for v in v0])) + "}"
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
            # auxiliary ureach dictionary
            if next_state in states_ureach:
                next_state = states_ureach[next_state]
            else:
                key = next_state
                next_state = frozenset(ureach_from_set_adj(key, G, G.Euo))
                states_ureach[key] = next_state

            # updating lists for igraph construction
            if next_state in vertice_number.keys():
                transition_list.append((vertice_number[v], vertice_number[next_state]))
                transition_label.append(ev)
            else:
                name_next_state = (
                    "{" + ",".join(flatten_deep([G.vs["name"][v] for v in next_state])) + "}"
                )
                transition_list.append((vertice_number[v], index))
                transition_label.append(ev)
                vertice_number[next_state] = index
                marking = any([G.vs["marked"][v] for v in next_state])
                marked_list.insert(index, marking)
                vertice_names.insert(index, name_next_state)
                queue.append(next_state)
                index = index + 1
            outgoing_v1v2.append((vertice_number[next_state], ev))
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


def observer_comp_old(
    part_obs,
    observer=None,
    Euo=set(),
    save_state_names=False,
    save_marked_states=False,
    dynamic=True,
):
    """
    Compute an observer automata
    Constructs an observer of the given automata. Each state in the observer
    represents the best state estimate as a set of possible states the system
    could be in.

    Returns the observer as an Automata


    """

    observer_defined = True
    if not observer:
        observer = DFA()
        observer_defined = False
    if not part_obs.vcount():
        return

    if not Euo:
        Euo = part_obs.Euo

    if "init" in part_obs.vs.attributes():
        x0 = {v.index for v in part_obs.vs if v["init"]}
    else:
        x0 = {0}

    # 1. Determine x0_obs = u-reach(x0), add to X_obs
    x0_obs = ureach_from_set_adj(x0, part_obs, Euo)
    x0_obs = frozenset(x0_obs)
    # SEQUENTIAL CONSTRUCTION VIA DICT
    X_obs_dict = OrderedDict()

    trans_list = list()
    trans_label = list()

    # queue for search:
    Q = list()
    Q.append((x0_obs, 0))

    X_obs_dict[x0_obs] = 0

    out_adj = list()
    if dynamic:
        search_d(part_obs._graph, Q, Euo, X_obs_dict, trans_list, trans_label, out_adj)
    else:
        search(part_obs._graph, Q, Euo, X_obs_dict, trans_list, trans_label, out_adj)
    convert_to_graph(
        part_obs,
        observer,
        X_obs_dict,
        trans_list,
        trans_label,
        save_state_names,
        save_marked_states,
        out_adj,
    )

    observer.Euc = set(part_obs.Euc)
    observer.Euo = set(part_obs.Euo)
    if not observer_defined:
        return observer


def search_d(part_obs, Q, Euo, X_obs_dict, trans_list, trans_label, out_adj_list):
    """
    BFS of the states of part_obs (the partially observed automaton).
    Uses queue-system via list Q.
    """
    i = 1
    S_dict = dict()
    while Q:
        q, index = Q.pop(0)

        adj_states = dict()  # maps label->set of states

        for vert in q:
            for target, label in part_obs.vs["out"][vert]:
                if label in adj_states:
                    adj_states[label].add(target)
                elif label not in Euo:
                    s = set()
                    s.add(target)
                    adj_states[label] = s

        # From current state estimate q, find all adjacent state estimates:
        # adj_states stores the destination states reached by observable transitions in q
        # adj_sets extends each state estimate in adj_states by its unoberservable reach
        adj_sets = list()
        for S in adj_states.items():
            set_states = frozenset(S[1])
            if set_states not in S_dict:
                ur = ureach_from_set_adj(S[1], part_obs, Euo)
                # S_dict[set_states] = (ur, S[0])
                # adj_sets.append((ur, S[0]))
                S_dict[set_states] = ur
                adj_sets.append((ur, S[0]))
            else:
                set_states = frozenset(S[1])
                # adj_sets.append(S_dict[set_states])
                adj_sets.append((S_dict[set_states], S[0]))

        # adj_sets = ((ureach_from_set_adj(S[1], part_obs, Euo), S[0]) for S in adj_states.items())

        out_adj_list.append([])

        for s in adj_sets:
            s_f = frozenset(s[0])
            out_adj_list[index].append((s_f, s[1]))
            if s_f not in X_obs_dict.keys():
                Q.append((s_f, i))
                X_obs_dict[s_f] = i

                i += 1

            trans_list.append((X_obs_dict[q], X_obs_dict[s_f]))
            trans_label.append(s[1])


def search(part_obs, Q, Euo, X_obs_dict, trans_list, trans_label, out_adj_list):
    """
    BFS of the states of part_obs (the partially observed automaton).
    Uses queue-system via list Q.
    """
    i = 1
    S_dict = dict()
    while Q:
        q, index = Q.pop(0)

        adj_states = dict()  # maps label->set of states

        for vert in q:
            for target, label in part_obs.vs["out"][vert]:
                if label in adj_states:
                    adj_states[label].add(target)
                elif label not in Euo:
                    s = set()
                    s.add(target)
                    adj_states[label] = s

        # From current state estimate q, find all adjacent state estimates:
        # adj_states stores the destination states reached by observable transitions in q
        # adj_sets extends each state estimate in adj_states by its unoberservable reach

        adj_sets = (
            (ureach_from_set_adj(S[1], part_obs, Euo), S[0]) for S in adj_states.items()
        )
        out_adj_list.append([])

        for s in adj_sets:
            s_f = frozenset(s[0])
            out_adj_list[index].append((s_f, s[1]))
            if s_f not in X_obs_dict.keys():
                Q.append((s_f, i))
                X_obs_dict[s_f] = i

                i += 1

            trans_list.append((X_obs_dict[q], X_obs_dict[s_f]))
            trans_label.append(s[1])


def convert_to_graph(
    part_obs,
    observer,
    X_obs_dict,
    trans_list,
    trans_label,
    save_state_names,
    save_marked_states,
    adj,
):
    """
    Convert sets/lists of states/transitions into final igraph Graph in observer.
    """
    # IT WOULD BE FASTER IF WE DO THIS DURING CONSTRUCTION NOT AFTER
    # IT WOULD AVOID A FEW FOR LOOPS

    if save_state_names:
        names = [
            frozenset(tuple(part_obs.vs[v]["name"]) for v in x) for x in X_obs_dict
        ]
    else:
        names = list(X_obs_dict.keys())

    if save_marked_states:
        marked = [any(part_obs.vs[v]["marked"] for v in x) for x in X_obs_dict]
    else:
        marked = None

    observer.add_vertices(len(X_obs_dict.keys()), names, marked)

    observer.add_edges(trans_list, trans_label)

    out = [[(X_obs_dict[s[0]], s[1]) for s in vert] for vert in adj]
    observer.vs["out"] = out
