from DESops.automata.event import Event
from DESops.basic_operations import composition
from DESops.basic_operations.construct_reverse import reverse
from DESops.basic_operations.product_NFA import product_NFA
from DESops.opacity.language_functions import (
    construct_H_NS,
    language_inclusion,
    moore_to_standard,
)


def verify_k_step_opacity_language_comparison(
    g,
    k,
    joint=True,
    secret_type=None,
    return_num_states=False,
    return_violating_path=False,
    use_reverse_comparison=True,
):
    """
    Returns whether the given automaton with unobservable events and secret states is k-step opaque

    Returns: opaque(, num_states)(, violating_path)

    Parameters:
    g: the automaton
    k: the number of steps. If k == "infinite", then infinite-step opacity will be checked
    return_num_states: if True, the number of states in the product used for checking language inclusion is returned as an additional value
    return_violating_path: if True, a list of observable events representing an opacity-violating path is returned as an additional value
    use_reverse_comparison: if True, the reverse languages are compared; otherwise the forward languages are compared
    """
    e_ext = Event("e_ext")
    e_init = Event("e_init")
    if e_ext in set(g.es["label"]):
        raise ValueError("e_ext is a reserved event label")
    if e_init in set(g.es["label"]):
        raise ValueError("e_init is a reserved event label")

    if secret_type is None:
        if joint:
            secret_type = 1
        else:
            secret_type = 2

    Euo = g.Euo
    Eo = set(g.es["label"]) - Euo
    Eo.add(e_init)

    # copy avoids changing original g outside of function
    g = g.copy()
    if not joint:
        # separate opacity uses self-loops to make all runs of g extendable
        for i in range(g.vcount()):
            g.add_edge(i, i, e_ext, fill_out=True)
    g = moore_to_standard(g)

    marked_events = set(g.es["label"])
    uo_marked_events = g.Euo

    h_ns = construct_H_NS(k, joint, secret_type, marked_events, uo_marked_events)
    g_ns = product_NFA([g, h_ns], save_marked_states=True)

    if use_reverse_comparison:
        reverse(g_ns, inplace=True)
        reverse(g, inplace=True)

    # replace (e, s) events with e events before creating observers
    g.es["label"] = [t["label"][0] for t in g.es]
    g.Euo = {e[0] for e in g.Euo}
    g.generate_out()

    g_ns.es["label"] = [t["label"][0] for t in g_ns.es]
    g_ns.Euo = {e[0] for e in g_ns.Euo}
    g_ns.generate_out()

    g_obs = composition.observer(g)
    g_ns_obs = composition.observer(g_ns)

    return_tuple = language_inclusion(
        g_obs, g_ns_obs, Eo, return_num_states, return_violating_path
    )

    if return_violating_path:
        path = return_tuple[-1]
        if path:
            while "e_init" in path:
                path.remove("e_init")
            while "e_ext" in path:
                path.remove("e_ext")

    return return_tuple
