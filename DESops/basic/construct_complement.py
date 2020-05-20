def construct_complement(g, g_comp, events=None, save_state_names=False):
    """
    Construct the complement of the given marked automaton

    g: input marked automaton
    g_comp: where the complement will be stored
    events: the event set of the automaton; required if the event set includes events not found in any transition
    """
    if not events:
        events = set(g_comp.es["label"])
    # construct new automaton with additional "dead" state
    x_d = g.vcount()
    g_comp.add_vertices(g.vcount() + 1)
    if save_state_names:
        g_comp.vs["name"] = g.vs["name"] + ["x_d"]

    g_comp.vs["marked"] = [not i for i in g.vs["marked"]] + [True]

    for t in g.es:
        g_comp.add_edge(t.source, t.target, t["label"])

    # direct all nonexistent transitions to the "dead" state
    for v in g_comp.vs:
        active_events = set(t["label"] for t in v.out_edges())
        for e in events:
            if not e in active_events:
                g_comp.add_edge(v.index, x_d, e)
