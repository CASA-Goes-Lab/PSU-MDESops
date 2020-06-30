"""
Functions related to the alternative method for k-step and infinite-step opacity that is based on language inclusion
"""
from DESops.automata.NFA import NFA
from DESops.basic_operations.construct_complement import complement
from DESops.basic_operations.construct_reverse import reverse
from DESops.basic_operations.observer_comp import observer_comp_old
from DESops.basic_operations.product_NFA import product_NFA
from DESops.opacity.contract_secret_traces import contract_secret_traces


def verify_joint_k_step_opacity_language_based(g, k, return_num_states=False):
    """
    Returns whether the given automaton with unobservable events and secret states is joint k-step opaque

    Parameters:
    g: the automaton
    k: the number of steps
    return_num_states: used for testing space usage: causes the return value to be the number of states in the language inclusion product
    """
    # edge case: all initial states are secret
    if all([v["secret"] for v in g.vs if v["init"]]):
        if return_num_states:
            return 0
        return False

    Euo = g.Euo
    Eo = set(g.es["label"]).difference(Euo)

    g_c = contract_secret_traces(g)
    g_c.vs["marked"] = True

    reverse(g_c, inplace=True)

    h = construct_reverse_unfolded_automaton(g_c, g.vs, k)

    return language_inclusion(g_c, h, Eo, return_num_states)


def verify_joint_infinite_step_opacity_language_based(g):
    """
    Returns whether the given automaton with unobservable events and secret states is joint infinite-step opaque

    Parameters:
    g: the automaton
    k: the number of steps
    """
    Euo = g.Euo
    Eo = set(g.es["label"]).difference(Euo)

    g_c = contract_secret_traces(g)
    g_c.vs["marked"] = [g.vs[state[0]]["init"] for state in g_c.vs["name"]]

    h = g_c.copy()
    h.delete_vertices([v for v in h.vs if v["secret"]])
    h.vs["marked"] = True

    return language_inclusion(g_c, h, Eo)


def min_k_for_joint_opacity_violation(g):
    """
    Returns the minimum value of K for which the automaton g is not joint K-step opaque
    """
    if verify_joint_infinite_step_opacity_language_based(g):
        return float("inf")

    k = 0
    while True:
        if not verify_joint_k_step_opacity_language_based(g, k):
            return k
        k += 1


def construct_reverse_unfolded_automaton(g_r, g_vs, k):
    """
    Returns the "unfolded" automaton that follows the reverse automaton but
    avoids visiting any secret states within the first K steps

    State name ((a, b), c):
        a corresponds to the vertex index in the original g
        b is 1 for secret observation periods, 0 for nonsecret periods
        c is the number of steps from the end of the forward string (with K representing >=K)

    Used for verifying joint K-step opacity

    g_r: the reverse contracted automaton
    g_vs: the vertex sequence of the original automaton g
    k: the number of steps
    """
    h = NFA()
    # start with nonsecret states 0 steps from the end
    S0 = [((v, 0), 0) for v in g_vs.select(secret=False).indices]
    state_indices = dict()
    for state in S0:
        state_indices[state] = h.vcount()
        h.add_vertex(state)
    h.vs["init"] = True

    need_to_check = S0
    while need_to_check:
        state = need_to_check.pop()
        if g_r.vs.select(name=state[0]):
            for t in g_r.vs.select(name=state[0])[0].out_edges():
                step = state[1]
                # if already k steps from the end, we can go to the next state even if it's secret
                if step == k:
                    next_state = (t.target_vertex["name"], k)
                # we can go to secret states within K steps from the end
                elif not t.target_vertex["secret"]:
                    next_state = (t.target_vertex["name"], step + 1)
                # we can't go to a secret state within K steps from the end
                else:
                    continue

                if next_state not in state_indices:
                    state_indices[next_state] = h.vcount()
                    h.add_vertex(next_state)
                    need_to_check.append(next_state)

                h.add_edge(
                    state_indices[state],
                    state_indices[next_state],
                    t["label"],
                    fill_out=True,
                )

    # fix added states having None instead of False for init attribute
    h.vs["init"] = [(True if state["init"] else False) for state in h.vs]
    # states are marked if they are initial in the original g
    h.vs["marked"] = [g_vs[state[0][0]]["init"] for state in h.vs["name"]]
    return h


def verify_separate_k_step_opacity_language_based(g, k):
    """
    Returns whether the given automaton with unobservable events and secret states is joint k-step opaque

    Parameters:
    g: the automaton
    k: the number of steps
    """
    Euo = g.Euo
    Eo = set(g.es["label"]).difference(Euo)

    g_c = contract_secret_traces(g, any_nonsec_is_nonsec=True)
    g_c.vs["marked"] = True

    # add self loops to each state so that runs reaching a dead state can be extended
    g_c.add_edges(
        [(i, i) for i in range(g_c.vcount())], ["e_self"] * g_c.vcount(), fill_out=True
    )

    h = construct_forward_unfolded_automaton(g_c, k)

    # more efficient to compare reverse languages
    reverse(g_c, inplace=True)
    reverse(h, inplace=True)

    return language_inclusion(g_c, h, Eo)


def construct_forward_unfolded_automaton(g_c, k):
    """
    Returns the "unfolded" automaton that follows the forward automaton but
    avoids visiting any secret states within the last K steps

    State name ((a, b), c):
        a corresponds to the vertex index in the original g
        b is 1 for secret observation periods, 0 for nonsecret periods
        c is the number of steps from the end of the forward string (with K representing >=K)

    Used for verifying separate K-step opacity

    g_c: the contracted automaton
    g_vs: the vertex sequence of the original automaton g
    k: the number of steps
    """
    h = NFA()
    # start with initial states of g_c at each step in {0,...,K}
    S0 = [(state["name"], i) for state in g_c.vs if state["init"] for i in range(k + 1)]
    state_indices = dict()
    for state in S0:
        state_indices[state] = h.vcount()
        h.add_vertex(state)
    h.vs["init"] = True

    need_to_check = S0
    while need_to_check:
        state = need_to_check.pop()
        if g_c.vs.select(name=state[0]):
            for t in g_c.vs.select(name=state[0])[0].out_edges():
                step = state[1]
                next_states = list()
                # if >=K steps until the end we can always stay at >=K steps
                if step == k:
                    next_states.append((t.target_vertex["name"], k))
                    # only nonsecret states can go from K to K-1 steps from the end
                    if step > 0 and not t.source_vertex["secret"]:
                        next_states.append((t.target_vertex["name"], k - 1))
                # between 1 and K-1 steps from the end we can visit any state
                elif step > 0:
                    next_states.append((t.target_vertex["name"], step - 1))

                while next_states:
                    next_state = next_states.pop()

                    if next_state not in state_indices:
                        state_indices[next_state] = h.vcount()
                        h.add_vertex(next_state)
                        need_to_check.append(next_state)

                    h.add_edge(
                        state_indices[state],
                        state_indices[next_state],
                        t["label"],
                        fill_out=True,
                    )

    # fix added states having None instead of False for init attribute
    h.vs["init"] = [(True if state["init"] else False) for state in h.vs]

    # for K=0, all states are at step K so we need to mark the nonsecret ones
    if k == 0:
        h.vs["marked"] = [(state[0][1] == 0) for state in h.vs["name"]]
    # for K>0 we mark any state that reached step 0
    else:
        h.vs["marked"] = [(state[1] == 0) for state in h.vs["name"]]

    return h


def language_inclusion(g, h, Eo, return_num_states=False):
    """
    Returns whether the language marked by g is a subset of the language marked by h

    Note: Only use this if the event sets are the same for both automata

    g, h: the two automata
    Eo: the set of observable events
    """
    h_det = observer_comp_old(h, save_marked_states=True)
    complement(h_det, inplace=True, events=Eo)

    prod = product_NFA([g, h_det], save_marked_states=True)

    if return_num_states:
        return prod.vcount()

    for v in prod.vs:
        if v["marked"]:
            return False
    return True
