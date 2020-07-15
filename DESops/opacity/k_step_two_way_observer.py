from DESops.basic_operations.construct_reverse import reverse
from DESops.basic_operations.observer_comp import observer_comp
from DESops.opacity.contract_secret_traces import contract_secret_traces


def verify_separate_k_step_opacity_TWO(g, k, secret_type=2, return_num_states=False):
    g = contract_secret_traces(g, secret_type)

    # names need to be indices so we can find them from observer
    g.vs["name"] = g.vs.indices

    g_r = reverse(g)

    g_obs = observer_comp(g)
    g_r_obs = observer_comp(g_r)

    forward_states = g_obs.vs["name"]
    if k == "infinite":
        # infinite-step looks at all states
        reverse_states = g_r_obs.vs["name"]
    else:
        # k-step looks only at states within final k steps
        distances = g_r_obs._graph.shortest_paths(0)[0]
        reverse_states = [v["name"] for v in g_r_obs.vs if distances[v.index] <= k]

    # states of two-way observer are pairs of states in the forward and reverse observers
    opaque = True
    for s1 in forward_states:
        for s2 in reverse_states:
            # opacity is violated if any nonempty intersection contains only secret states
            common_states = s1.intersection(s2)
            if common_states:
                if all([g.vs[v]["secret"] for v in common_states]):
                    opaque = False
                    break
        if not opaque:
            break

    return_list = [opaque]

    if return_num_states:
        return_list.append(g_obs.vcount() + g_r_obs.vcount())

    if len(return_list) == 1:
        return return_list[0]
    else:
        return tuple(return_list)
