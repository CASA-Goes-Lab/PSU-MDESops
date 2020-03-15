"""
Functions relevant to computing the supremal controllable and normal supervisor
of given system and specifcation automata.

supremal_cn_supervisor() computes and returns the SCNS as an igraph Graph.

The cn_preprocessing module (cn_pp.py) handles necessary preprocessing,
and returns modified system/specifiation automata that meet the necessary
assumptions in the SCNS algorithm.

The required assumptions are:

1. H (the specification) is a strict subautomata of G
2. G is an SPA (state partitioned automaton)

TODO: implement a supremal_cn_supervisor_pp() function that performs
preprocessing and calls supremal_cn_supervisor(), which performs
no preprocessing (similar to how the SCS is handled).
"""

import igraph as ig

from ..basic.generic_functions import find_obs_contr
from ..basic.observer_comp import observer_comp
from ..supremal.cn_pp import cn_preprocessing as cn_preprocessing


def supremal_cn_supervisor(H_given, G_given, Euc=None, Euo=None):
    """
    Computes the supremal controllable-normal supervisor for the given
    plant and specification Automata. An iterative process is used, where the
    specification is modified to meet the controllability condition, then the
    normality condition, ..., until convergance when the most recent controllable
    specification matches the most recent normal specification. Convergence is
    checked by verifying no states were removed in the last controllable/normal
    evaluation step.

    The supremal controllable supervisor computation was reimplemented here,
    in place of using the supremal_controllable_supervisor module, to take
    advantage of the iterative structure of this problem.

    Returns: an igraph Graph as the automata realization of the supremal
    controllable-normal supervisor.

    Parameters:
    system: igraph Graph representing the plant/system as an automaton.
    specification: igraph Graph representing the specification as an automaton.

    Euc: optionally provided set of uncontrollable events. Will attempt to find
    with find_obs_contr() via labels on the graphs' edges, if Euc isn't provided.

    Euo: optionally provided set of unobservable events. Will attempt to find
    with find_obs_contr() via labels on the graphs' edges, if Euo isn't provided.

    """

    # Find set of events that are unobservable/uncontrollable

    find_obs_contr([H_given, G_given], Euc, Euo)

    H = ig.Graph(directed=True)
    G = ig.Graph(directed=True)

    # Process H, G to ensure conditions for ^CN computation
    #   1. H is a strict subautomat of G
    #   2. G is an SPA
    [H, G, states_to_remove] = cn_preprocessing(H_given, G_given, Euc, Euo)
    # For each state:
    # 2.1: Compute normality condition
    # 2.2: Compute controllability condition
    # 2.3: Trim (or ensure we are only checking accessible states in the first place)
    # Collect set of good states, find set diff total_states - good_states = bad_states
    # delete all bad states, resulting in K^CN
    states_removed = set()
    G_obs = ig.Graph(directed=True)
    observer_comp(G, G_obs, Euo=Euo)

    not_converged = True
    first_iter = True
    while not_converged:
        if not first_iter and not states_to_remove:
            break
        else:
            states_just_removed = scs(G, H, Euc, states_to_remove, first_iter)
        if not first_iter and not states_just_removed:
            break

        else:
            states_removed.update(states_just_removed)
            states_to_remove = sns(G, G_obs, H, Euc, Euo, states_removed)

        if first_iter:
            first_iter = False

    return H


def invalid_state(G, H, Euc, H_state):
    H_uc_count = len([e for e in H.es(_source=H_state) if e["label"] in Euc])
    G_assoc_state = H.vs["name"][H_state]
    G_uc_count = len([e for e in G.es(_source=G_assoc_state) if e["label"] in Euc])
    return H_uc_count < G_uc_count


def trim(G):
    """
    Compute the trim automaton of G --- does not remove any states.
    Returns a list of vertex indices of G that are inaccessible
    and should be removed.

    E.g.: code to compute the trim automaton of G:
    >>> v_list = trim(G)
    >>> G.delete_vertices(v_list)

    """
    Q = list()
    Q.append({0})
    good_states = set()
    good_states.add(0)
    while Q:
        q = Q.pop(0)
        neighbors = {
            t.target for t in G.es(_source_in=q) if t.target not in good_states
        }
        if not neighbors:
            continue
        good_states.update(neighbors)
        Q.append(frozenset(neighbors))

    bad_states = {v.index for v in G.vs if v.index not in good_states}
    return bad_states


def scs(G, S, Euc, states_to_remove, first_iter):
    """
    Computes the supremal controllable supervisor.
    Used here to take advantage of the intermediate structure
    in the iterative process of computing the SCNS (as opposed to
    using the supremal_controllable_supervisor module). As such,
    an actual supervisor is not computed; rather, the states violating
    the controllability condition are removed from S.

    When this function is called, the only states violating the controllability
    condition should be those with uncontrollable transitions targetting a recently
    removed state. That is, only successors to states_to_remove must be checked
    for the controllability condition. Using the supremal_controllable_supervisor
    module would mean every state gets checked (same worst case computation time,
    but in general this should be significantly faster).

    Returns list of names of vertices of G that were removed (in
    this particular iteration).

    Parameters:
    G: system automaton as an igraph Graph
    S: specification/controller automaton as an igraph Graph
    Euc: set of uncontrollable events
    states_to_remove: the states most recently identified as needing
        to be deleted. Those states will be removed, along with inaccessible
        states at the end of the function.
    first_iter: bool, True if first iteration of SCS. If it's not the first
        iteration, the trim will be computed.
    """
    inacc_states = set()
    if not first_iter:
        inacc_states = trim(S)
    # states_removed = {S.vs[v]["name"][1] for v in states_to_remove}
    states_removed = set(states_to_remove).difference(inacc_states)
    # S_states_to_remove = {v.index for v in S.vs if v["name"][1] in states_to_remove}
    states_to_check = {
        e.source
        for e in S.es(_target_in=states_to_remove)
        if e["label"] in Euc
        and e.source not in states_removed
        and e.source not in inacc_states
    }
    while states_to_check:
        states_removed.update(states_to_check)
        states_to_check_new = {
            e.source
            for e in S.es(_target_in=states_to_check)
            if e["label"] in Euc
            and e.source not in states_removed
            and e.source not in inacc_states
        }
        states_to_check = states_to_check_new
    G_removed_vs_names = {S.vs[v]["name"][1] for v in states_removed}
    S.delete_vertices(states_removed | inacc_states)
    return G_removed_vs_names


def sns(G, G_obs, S, Euc, Euo, states_removed):
    """
    Computes the supremal normal supervisor (really just returns
    a set of states that violate the normality condition and need to
    be deleted).

    Returns bad_states, a set of states violating the normality condition.

    Parameters:
    G: system automaton as an igraph Graph
    G_obs: observer automaton of G, as an igraph graph
    S: spec/controller automaton as an igraph Graph
    Euc: set of uncontrollable events
    Euo: set of unobservable events
    states_removed: set of states removed from S in the last iteration.
    """
    q_dict = dict()
    bad_states = set()
    states_yi = {v["name"][1] for v in S.vs}
    Q = list()
    for yi in S.vs:
        for q in G_obs.vs["name"]:
            if yi["name"][1] in q:
                # Make sure q is in Yi
                if q in q_dict:
                    if not q_dict[q]:
                        bad_states.add(yi.index)
                else:
                    q_dict[q] = q.issubset(states_yi)
                    if not q_dict[q]:
                        bad_states.add(yi.index)

    return bad_states
