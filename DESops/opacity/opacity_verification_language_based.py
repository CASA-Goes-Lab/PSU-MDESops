from DESops import Automata
from DESops.Automata import product_comp
from DESops.opacity.contract_secret_traces import contract_secret_traces


def verify_joint_k_step_opacity_language_based(g, k):
    """
    Determine if the given automaton with unobservable events and secret states is joint k-step opaque

    Parameters:
    g: the automaton
    k: the number of steps
    """
    Euo = g.Euo
    Eo = set(g.es["label"]).difference(Euo)

    g_contracted = Automata()
    contract_secret_traces(g, g_contracted, Euo, False)

    g_r = g_contracted.reverse(save_state_names=True)
    g_r.vs["marked"] = [g.vs[i]["init"] for i in [s[0] for s in g_r.vs["name"]]]
    g_r.vs["secret"] = [v["name"][1] for v in g_r.vs]

    h = construct_unfolded_automaton(g_r, g.vs, k)

    g_r_det = g_r.observer(save_marked_states=True)

    h_det = h.observer(save_marked_states=True)

    h_det_comp = h_det.complement(Eo)

    prod = product_comp([g_r_det, h_det_comp], save_marked_states=True)

    for v in prod.vs:
        if v["marked"]:
            return False
    return True


def construct_unfolded_automaton(g_r, g_vs, k):
    """
    Returns the "unfolded" automaton

    g_r: the reverse contract automaton
    g_vs: the vertex sequence of the original automaton g
    k: the number of steps
    """
    h = Automata()
    S0 = [((v, 0), 0) for v in g_vs.select(secret=False).indices]
    state2index = dict()
    for state in S0:
        state2index[state] = h.vcount()
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

                if next_state not in state2index:
                    state2index[next_state] = h.vcount()
                    h.add_vertex(next_state)
                    need_to_check.append(next_state)

                h.add_edge(state2index[state], state2index[next_state], t["label"])

    h.vs["init"] = [(True if state["init"] else False) for state in h.vs]
    h.vs["marked"] = [g_vs[state[0][0]]["init"] for state in h.vs["name"]]
    return h
