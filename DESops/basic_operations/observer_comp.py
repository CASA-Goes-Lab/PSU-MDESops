# pylint: disable=C0103
"""
Functions relevant to constructing an observer automaton from a partially-observed automaton.

Only observer_comp is used outside this module; the rest are included as helper functions
only used by observer_comp.
"""


from collections import OrderedDict
from DESops.automata.DFA import DFA
from DESops.basic_operations.generic_functions import find_Euo
from DESops.basic_operations.ureach import ureach_from_set_adj


def observer_comp(
    part_obs, observer=None, Euo=set(), save_state_names=False, save_marked_states=False
):
    """
    Compute an observer automata
    Constructs an observer of the given automata. Each state in the observer
    represents the best state estimate as a set of possible states the system
    could be in.

    Returns the observer as an Automata

    Requires the unobersvable events in the system be notated in some way.
    If Euo is not empty, those events will be used as the unobservable event set.
    Otherwise, the observer_comp function will check the igraph Graph edges
    for an "Euo" attribute, {G.es()["Euo"]} and from that construct the unobservable
    event set (legacy, shouldn't happen anymore; any initialization method from igraph Graphs
    should find the Euo set already).

    Parameters:
    save_state_names (default True): currently does nothing (!!!!)
        Note: the thinking for this was that currently, state names ("name" vertex attribute)
        are sets of states from the original Automata. This parameter could avoid
        allowing unnecessarily saving this information. Change to be similar to parallel_comp,
        where the names just don't get assigned to the result?

    save_marked_states (default False):

    Usage:
    >>> O = observer(G)

    part_obs: part_obs partially observed automata
    observer: Obs(part_obs)
    Euo: optionally provide set of unobservable events; if not provided, will attempt to find in part_obs edge attributes
    """

    observer_defined = True
    if not observer:
        observer = DFA()
        observer_defined = False
    if not part_obs.vcount():
        return
    Euo = part_obs.Euo
    # 1. Determine x0_obs = u-reach(x0), add to X_obs
    x0_obs = set()

    x0_obs = ureach_from_set_adj({0}, part_obs, Euo)
    x0_obs = frozenset(x0_obs)
    # SEQUENTIAL CONSTRUCTION VIA DICT
    X_obs_dict = OrderedDict()

    trans_list = list()
    trans_label = list()

    # queue for search:
    Q = list()
    Q.append((x0_obs, 0))

    X_obs_dict[x0_obs] = 0

    out_adj = []
    search(part_obs._graph, Q, Euo, X_obs_dict, trans_list, trans_label, out_adj)

    convert_to_graph(
        part_obs,
        observer,
        X_obs_dict,
        trans_list,
        trans_label,
        save_state_names,
        save_marked_states,
    )

    observer.vs["out"] = out_adj
    observer.Euc = set(part_obs.Euc)
    observer.Euo = set(part_obs.Euo)
    if not observer_defined:
        return observer


def search(part_obs, Q, Euo, X_obs_dict, trans_list, trans_label, out_adj_list):
    """
    BFS of the states of part_obs (the partially observed automaton).
    Uses queue-system via list Q.
    """
    i = 1
    while Q:
        q, index = Q.pop(0)
        out_adj_list.append([])

        adj_states = dict() # maps label->set of states

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

        adj_sets = ((ureach_from_set_adj(S[1], part_obs, Euo), S[0]) for S in adj_states.items())

        for s in adj_sets:
            next_states = frozenset(s[0])
            out_adj_list[index].append((i, s[1]))
            if next_states not in X_obs_dict.keys():
                Q.append((next_states, i))
                X_obs_dict[next_states] = i

                i += 1

            trans_list.append((X_obs_dict[q], X_obs_dict[next_states]))
            trans_label.append(s[1])


def convert_to_graph(
    part_obs,
    observer,
    X_obs_dict,
    trans_list,
    trans_label,
    save_state_names,
    save_marked_states,
):
    """
    Convert sets/lists of states/transitions into final igraph Graph in observer.
    """
    # IT WOULD BE FASTER IF WE DO THIS DURING CONSTRUCTION NOT AFTER
    # IT WOULD AVOID A FEW FOR LOOPS

    if save_state_names:
        names = [frozenset(part_obs.vs[v]["name"] for v in x) for x in X_obs_dict]
    else:
        names = X_obs_dict.values()

    if save_marked_states:
        marked = [any(part_obs.vs[v]["marked"] for v in x) for x in X_obs_dict]
    else:
        marks = None

    observer.add_vertices(len(X_obs_dict.keys()), names, marks)

    observer.add_edges(trans_list, trans_label)

