"""
Functions related to the state-based method of verifying K-step opacity
"""
from DESops.automata.NFA import NFA


def verify_joint_k_step_opacity_state_based(g, k, return_num_states=False):
    """
    Returns whether the given automaton with unobservable events and secret states is joint k-step opaque

    Parameters:
    g: the automaton
    k: the number of steps
    return_num_states: if true, the function will return a (bool, int) tuple where:
        first return value tells whether g is k-step opaque
        second return value is the number of states in the observer constructed when checking current state opacity
    """
    # imported here to avoid error when two files import from each other
    from DESops.opacity.opacity import verify_current_state_opacity

    Euo = g.Euo

    h = NFA()
    h.Euo = Euo
    # State name (a, b):
    #    a corresponds to the vertex index in the original g
    #    b is the number of steps since the last secret state (with K+1 representing >K)
    # initial states of g marked with >K if nonsecret, 0 if secret
    S0 = [(v.index, k + 1) for v in g.vs if v["init"] and not v["secret"]]
    S0 += [(v.index, 0) for v in g.vs if v["init"] and v["secret"]]
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

            if t.target_vertex["secret"]:
                # transitions to secret events reset us to 0 steps since last secret event
                next_state = (t.target, 0)

            elif step > k:
                # if >K steps since last secret event, stay at >K
                next_state = (t.target, k + 1)

            elif t["label"] in Euo:
                # unobersevable events don't count as a step
                next_state = (t.target, step)

            else:
                # observable events give one more step since last secret event
                next_state = (t.target, step + 1)

            if next_state not in state_indices:
                state_indices[next_state] = h.vcount()
                h.add_vertex(next_state)
                need_to_check.append(next_state)

            h.add_edge(
                state_indices[state], state_indices[next_state], t["label"],
            )

    h.generate_out()

    # check current state opacity where secret states are those that visited a secret state <=K steps ago
    h.vs["secret"] = [(state[1] <= k) for state in h.vs["name"]]

    return verify_current_state_opacity(h, return_num_states)
