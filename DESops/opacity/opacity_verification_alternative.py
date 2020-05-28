"""
Functions related to the alternative method for k-step and infinite-step opacity that is based on language inclusion
"""
from DESops import Automata
from DESops.Automata import product_comp
from DESops.opacity.contract_secret_traces import contract_secret_traces


def verify_joint_k_step_opacity_alternative(g, k):
    """
    Returns whether the given automaton with unobservable events and secret states is joint k-step opaque

    Parameters:
    g: the automaton
    k: the number of steps
    """
    # edge case: all initial states are secret
    if all([v["secret"] for v in g.vs if v["init"]]):
        return False

    Euo = g.Euo
    Eo = set(g.es["label"]).difference(Euo)

    g_contracted = Automata()
    contract_secret_traces(g, g_contracted, Euo, False)

    g_contracted.reverse(inplace=True)
    g_contracted.vs["marked"] = [
        g.vs[i]["init"] for i in [state[0] for state in g_contracted.vs["name"]]
    ]
    g_contracted.vs["secret"] = [v["name"][1] for v in g_contracted.vs]

    h = construct_unfolded_automaton(g_contracted, g.vs, k)

    return language_inclusion(g_contracted, h, Eo)


def verify_joint_infinite_step_opacity_alternative(g):
    """
    Returns whether the given automaton with unobservable events and secret states is joint infinite-step opaque

    Parameters:
    g: the automaton
    k: the number of steps
    """
    Euo = g.Euo
    Eo = set(g.es["label"]).difference(Euo)

    g_contracted = Automata()
    contract_secret_traces(g, g_contracted, Euo, False)
    g_contracted.vs["marked"] = [
        g.vs[i]["init"] for i in [state[0] for state in g_contracted.vs["name"]]
    ]
    g_contracted.vs["secret"] = [v["name"][1] for v in g_contracted.vs]

    h = g_contracted.copy()
    h._graph.delete_vertices([v for v in g.vs if v["secret"]])

    return language_inclusion(g_contracted, h, Eo)


def construct_unfolded_automaton(g_r, g_vs, k):
    """
    Returns the "unfolded" automaton that follows the reverse automaton but
    avoids visiting any secret states within the first K steps

    g_r: the reverse contracted automaton
    g_vs: the vertex sequence of the original automaton g
    k: the number of steps
    """
    h = Automata()
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
                if state[1] == k:
                    next_state = (t.target_vertex["name"], k)
                elif not t.target_vertex["secret"]:
                    next_state = (t.target_vertex["name"], state[1] + 1)
                else:
                    continue

                if next_state not in state_indices:
                    state_indices[next_state] = h.vcount()
                    h.add_vertex(next_state)
                    need_to_check.append(next_state)

                h.add_edge(state_indices[state], state_indices[next_state], t["label"])

    h.vs["init"] = [(True if state["init"] else False) for state in h.vs]
    h.vs["marked"] = [g_vs[state[0][0]]["init"] for state in h.vs["name"]]
    return h


def language_inclusion(g, h, Eo):
    """
    Returns whether the language marked by g is a subset of the language marked by h
    Requires that the event sets are the same for both automata

    g, h: the two automata
    Eo: the set of observable events
    """
    g_det = g.observer(save_marked_states=True)
    h_det = h.observer(save_marked_states=True)
    h_det.complement(events=Eo, inplace=True)
    prod = product_comp([g_det, h_det], save_marked_states=True)

    for v in prod.vs:
        if v["marked"]:
            return False
    return True
