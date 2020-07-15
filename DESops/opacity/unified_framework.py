from DESops.automata import DFA, NFA
from DESops.automata.event.event import Event
from DESops.basic_operations.construct_reverse import reverse
from DESops.basic_operations.observer_comp import observer_comp
from DESops.basic_operations.product_NFA import product_NFA
from DESops.opacity.language_functions import find_path_between, language_inclusion


def verify_k_step_opacity_unified_language(
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
    k: the number of steps. If k == "infinite", then infinite-step opacity will be checked
    return_num_states: if True, the number of states in the product used for checking language inclusion is returned as an additional value
    return_violating_path: if True, a list of observable events representing an opacity-violating path is returned as an additional value
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

    reverse(g_ns, inplace=True)
    reverse(g, inplace=True)

    # replace (e, s) events with e events before creating observers
    g.es["label"] = [t["label"][0] for t in g.es]
    g.Euo = {e[0] for e in g.Euo}
    g.generate_out()

    g_ns.es["label"] = [t["label"][0] for t in g_ns.es]
    g_ns.Euo = {e[0] for e in g_ns.Euo}
    g_ns.generate_out()

    g_obs = observer_comp(g)
    g_ns_obs = observer_comp(g_ns)

    return_tuple = language_inclusion(
        g_obs, g_ns_obs, Eo, return_num_states, return_violating_path
    )

    if return_violating_path:
        path = return_tuple[-1]
        if path:
            while e_init in path:
                path.remove(e_init)
            while e_ext in path:
                path.remove(e_ext)

    return return_tuple


def verify_k_step_opacity_state_observer(
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
    k: the number of steps. If k == "infinite", then infinite-step opacity will be checked
    return_num_states: if True, the number of states in the state observer is returned as an additional value
    return_violating_path: if True, a list of observable events representing an opacity-violating path is returned as an additional value
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

    # replace (e, s) events with e events before creating observer
    g_ns.es["label"] = [t["label"][0] for t in g_ns.es]
    g_ns.Euo = {e[0] for e in g_ns.Euo}
    g_ns.generate_out()

    state_observer = observer_comp(g_ns)

    # opacity holds if every state containing a marked q_g also contains a marked q_h
    opaque = True
    for state in state_observer.vs:
        if any([g.vs[pair[0]]["marked"] for pair in state["name"]]):
            if not any([(h_ns.vs[pair[1]]["marked"]) for pair in state["name"]]):
                opaque = False
                violating_id = state.index
                break

    return_list = [opaque]

    if return_num_states:
        return_list.append(state_observer.vcount())

    if return_violating_path:
        if opaque:
            return_list.append(None)
        else:
            inits = [v.index for v in state_observer.vs if v["init"]]
            path = find_path_between(state_observer, inits, violating_id)

            while e_init in path:
                path.remove(e_init)
            while e_ext in path:
                path.remove(e_ext)

            return_list.append(path)

    if len(return_list) == 1:
        return return_list[0]
    else:
        return tuple(return_list)


def moore_to_standard(g):
    """
    Returns an automaton that augments every event in g with whether the target vertex is secret
    A new initial vertex is added that reaches each old initial vertex via an e_init event
    The new automaton marks every string that begins with e_init and is followed by a string generated by g
    """
    h = NFA()
    h.add_vertices(g.vcount() + 1)

    # create new initial state that leads to old initial states via e_init
    # this means that vertex i in g is vertex i+1 in h
    for v in g.vs:
        if v["init"]:
            label = (Event("e_init"), v["secret"])
            h.add_edge(0, v.index + 1, label)
    h.vs["init"] = False
    h.vs[0]["init"] = True

    # all vertices except the initial one should be marked, because we should always have an e_init event
    h.vs["marked"] = True
    h.vs[0]["marked"] = False

    h.Euo = set()
    for t in g.es:
        label = (t["label"], t.target_vertex["secret"])
        h.add_edge(t.source + 1, t.target + 1, label)
        if t["label"] in g.Euo:
            h.Euo.add(label)

    h.generate_out()
    return h


def concatenate_union(g, h):
    """
    Constructs an automaton that marks any string in either in h, or in the concatenation of g and h

    The resulting automaton overwrites the original g
    """
    offset = g.vcount() - 1
    g.add_vertices(h.vcount() - 1)

    for t in h.es:
        if t.source == 0:
            # transitions from the initial state of h use marked states of g as their source
            for v in g.vs:
                if v["marked"]:
                    g.add_edge(v.index, t.target + offset, t["label"], fill_out=True)
        else:
            g.add_edge(t.source + offset, t.target + offset, t["label"], fill_out=True)

    # marked states correpsond to initial states in h
    for v in g.vs:
        if v["marked"]:
            v["init"] = True
        # fix vertices that didn't get marked as initial or non-initial
        if v["init"] is None:
            v["init"] = False

    # new marked states are those that are marked in h
    g.vs["marked"] = False
    for v in h.vs:
        if v["marked"]:
            g.vs[v.index + offset]["marked"] = True


def construct_H_NS(k, joint, secret_type, events, Euo):
    if k == "infinite":
        if not joint:
            raise ValueError("Separate infinite-step opacity is not implemented")
        h = H_infinite_NS(secret_type, events, Euo)

    else:
        h = H_star(events)

        if joint:
            # no secret behavior is allowed in final K+1 steps
            for _ in range(0, k + 1):
                concatenate_union(h, H_epoch_NS(secret_type, events, Euo))

        else:
            # nonsecret bahvaior must occur K epochs ago
            concatenate_union(h, H_epoch_NS(secret_type, events, Euo))
            # epochs 0 to K-1 steps ago don't matter
            for _ in range(0, k):
                concatenate_union(h, H_epoch_all(events, Euo))

    h.Euo = Euo
    return h


def H_star(events):
    """
    Returns an automaton that marks all strings

    events: set of (e, S/NS) pairs
    """
    h = DFA()
    h.add_vertex()
    h.vs["init"] = [True]
    h.vs["marked"] = [True]

    for e in events:
        h.add_edge(0, 0, e)

    h.generate_out()
    return h


def H_epoch_all(events, Euo):
    """
    Returns an automaton that marks any single epoch

    events: set of (e, S/NS) pairs
    Euo: set of (e, S/NS) pairs that are unobservable
    """
    h = DFA()
    h.add_vertices(2)
    h.vs["init"] = [True, False]
    h.vs["marked"] = [False, True]

    for e in events:
        if e in Euo:
            h.add_edge(1, 1, e)
        else:
            h.add_edge(0, 1, e)

    h.generate_out()
    return h


def H_epoch_NS(secret_type, events, Euo):
    """
    Returns an automaton that marks any single epoch in which nonsecret behavior occurs

    events: set of (e, S/NS) pairs
    Euo: set of (e, S/NS) pairs that are unobservable
    """
    h = NFA()

    if secret_type == 1:
        h.add_vertices(2)
        h.vs["init"] = [True, False]
        h.vs["marked"] = [False, True]
        for e in events:
            secret = e[1]
            if not secret:
                if e in Euo:
                    h.add_edge(1, 1, e)
                else:
                    h.add_edge(0, 1, e)

    else:
        h.add_vertices(3)
        h.vs["init"] = [True, False, False]
        h.vs["marked"] = [False, False, True]
        for e in events:
            secret = e[1]
            if e in Euo:
                h.add_edge(2, 2, e)
                h.add_edge(1, 1, e)
                if not secret:
                    h.add_edge(1, 2, e)

            else:
                h.add_edge(0, 1, e)
                if not secret:
                    h.add_edge(0, 2, e)

    h.generate_out()
    return h


def H_infinite_NS(secret_type, events, Euo):
    """
    Returns an automaton that marks strings that exhibit no secret behavior at any point

    events: set of (e, S/NS) pairs
    Euo: set of (e, S/NS) pairs that are unobservable
    """
    h = NFA()

    if secret_type == 1:
        h.add_vertices(3)
        h.vs["init"] = [True, False, False]
        h.vs["marked"] = [False, False, True]
        for e in events:
            secret = e[1]
            h.add_edge(1, 1, e)
            h.add_edge(2, 1, e)

            if not secret:
                h.add_edge(2, 2, e)
                if e not in Euo:
                    h.add_edge(0, 2, e)

            if e not in Euo:
                h.add_edge(0, 1, e)

    else:
        h.add_vertices(4)
        h.vs["init"] = [True, False, False, False]
        h.vs["marked"] = [False, False, False, True]
        for e in events:
            secret = e[1]
            h.add_edge(1, 2, e)
            h.add_edge(2, 2, e)

            if e in Euo:
                h.add_edge(1, 1, e)
                h.add_edge(3, 3, e)
                if not secret:
                    h.add_edge(1, 3, e)

            else:
                h.add_edge(0, 1, e)
                h.add_edge(3, 1, e)
                if not secret:
                    h.add_edge(0, 3, e)
                    h.add_edge(3, 3, e)

    h.generate_out()
    return h
