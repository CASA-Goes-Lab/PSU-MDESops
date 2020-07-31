"""
Functions related to the alternative method for k-step and infinite-step opacity that is based on language inclusion
"""
from DESops.automata.event import Event
from DESops.automata.NFA import NFA
from DESops.basic_operations.construct_reverse import reverse
from DESops.opacity.contract_secret_traces import contract_secret_traces
from DESops.opacity.language_functions import language_inclusion


def verify_k_step_opacity_language_based(
    g,
    k,
    joint=True,
    secret_type=None,
    return_num_states=False,
    return_violating_path=False,
):
    """
    Returns whether the given automaton with unobservable events and secret states is k-step opaque

    Returns: opaque(, num_states)(, violating_path)

    Parameters:
    g: the automaton
    k: the number of steps
    return_num_states: if True, the number of states in the product used for checking language inclusion is returned as an additional value
    return_violating_path: if True, a list of observable events representing an opacity-violating path is returned as an additional value
    """
    e_ext = Event("e_ext")
    if e_ext in set(g.es["label"]):
        raise ValueError("e_ext is a reserved event label")

    if secret_type is None:
        if joint:
            secret_type = 1
        else:
            secret_type = 2

    if joint and secret_type == 1 and all([v["secret"] for v in g.vs if v["init"]]):
        # joint has edge case when all initial states are secret
        if return_num_states:
            return False, 0
        return False

    Euo = g.Euo
    Eo = set(g.es["label"]) - Euo

    g_c = contract_secret_traces(g, secret_type)

    if joint:
        reverse(g_c, inplace=True)

    else:
        # add self loops to each state so that runs reaching a dead state can be extended
        g_c.add_edges(
            [(i, i) for i in range(g_c.vcount())],
            [e_ext] * g_c.vcount(),
            fill_out=True,
        )
        Eo.add(e_ext)

    h = construct_unfolded(g_c, k, joint)

    if not joint:
        # more efficient to compare reverse languages (joint case already reversed)
        reverse(g_c, inplace=True)
        reverse(h, inplace=True)

    return_tuple = language_inclusion(
        g_c, h, Eo, return_num_states, return_violating_path
    )

    if return_violating_path:
        path = return_tuple[-1]
        if path:
            while e_ext in path:
                path.remove(e_ext)

    return return_tuple


def verify_joint_infinite_step_opacity_language_based(
    g, secret_type=1, return_num_states=False, return_violating_path=False
):
    """
    Returns whether the given automaton with unobservable events and secret states is joint infinite-step opaque

    Returns: opaque(, num_states)(, violating_path)

    Parameters:
    g: the automaton
    return_num_states: if True, the number of states in the product used for checking language inclusion is returned as an additional value
    return_violating_path: if True, a list of observable events representing an opacity-violating path is returned as an additional value
    """
    Euo = g.Euo
    Eo = set(g.es["label"]).difference(Euo)

    g_c = contract_secret_traces(g, secret_type)

    h = NFA(g_c)
    h.delete_vertices([v for v in h.vs if v["secret"]])

    return language_inclusion(g_c, h, Eo, return_num_states, return_violating_path)


def construct_unfolded(g, k, joint=True):
    """
    Returns the "unfolded" automaton that marks nonsecret behavior in the contracted automaton g

    State names (a, b):
        a corresponds to the vertex index in the contracted automaton g
        b is the number of steps from the end of the forward string (with K representing >=K)

    Paramaters
    g: the contracted automaton
    k: the number of steps
    """
    h = NFA()

    if joint:
        # start with nonsecret states 0 steps from the end
        S0 = [(v.index, 0) for v in g.vs if not v["secret"]]
    else:
        # start with initial states of g_c at each step in {0,...,K}
        S0 = [(v.index, i) for v in g.vs if v["init"] for i in range(k + 1)]

    state_indices = dict()
    for state in S0:
        state_indices[state] = h.vcount()
        h.add_vertex(state)
    h.vs["init"] = True

    need_to_check = S0
    while need_to_check:
        state = need_to_check.pop()
        for t in g.vs[state[0]].out_edges():
            step = state[1]
            next_states = list()

            if joint:
                if step == k:
                    # if already k steps from the end, we can go to the next state even if it's secret
                    next_states.append((t.target, k))

                elif not t.target_vertex["secret"]:
                    # we can go to nonsecret states within K steps from the end
                    next_states.append((t.target, step + 1))

                else:
                    # we can't go to a secret state within K steps from the end
                    continue

            else:
                if step == k:
                    # if >=K steps until the end we can always stay at >=K steps
                    next_states.append((t.target, k))

                    if step > 0 and not t.source_vertex["secret"]:
                        # only nonsecret states can go from K to K-1 steps from the end
                        next_states.append((t.target, k - 1))

                elif step > 0:
                    # between 1 and K-1 steps from the end we can visit any state
                    next_states.append((t.target, step - 1))

            while next_states:
                next_state = next_states.pop()

                if next_state not in state_indices:
                    state_indices[next_state] = h.vcount()
                    h.add_vertex(next_state)
                    need_to_check.append(next_state)

                h.add_edge(
                    state_indices[state], state_indices[next_state], t["label"],
                )

    h.generate_out()

    # fix added states having None instead of False for init attribute
    h.vs["init"] = [(True if state["init"] else False) for state in h.vs]

    if joint:
        # states are marked if they are initial in the original g
        h.vs["marked"] = [g.vs[state[0]]["marked"] for state in h.vs["name"]]
    else:
        if k == 0:
            # for K=0, all states are at step K so we need to mark the nonsecret ones
            h.vs["marked"] = [(not g.vs[state[0]]["secret"]) for state in h.vs["name"]]
        else:
            # for K>0 we mark any state that reached step 0
            h.vs["marked"] = [(state[1] == 0) for state in h.vs["name"]]

    return h
