from DESops.automata.NFA import NFA


def complement(g, inplace=False, g_comp=None, events=None, dead_state_name=None):
    """
    Constructs the complement of the given automaton

    Parameters:
    g: the automaton
    inplace: if True, the automaton will overwrite the original g with its complement
    g_comp: where the complement is constructed (if not inplace); if not specified, a new automaton will be constructed and returned
    events: the event set of the automaton; required if the event set includes events not found in any transition
    dead_state_name: the name of the added dead state; if None, then no state names are saved
    """
    if inplace:
        inplace_complement(g, events, dead_state_name)
        return

    g_comp_defined = True
    if g_comp is None:
        g_comp = NFA()
        g_comp_defined = False

    construct_complement(g, g_comp, events, dead_state_name)

    if not g_comp_defined:
        return g_comp


def construct_complement(g, g_comp=None, events=None, dead_state_name=None):
    """
    Constructs the complement of the given marked automaton

    g: input marked automaton
    g_comp: where the complement will be stored
    events: the event set of the automaton; required if the event set includes events not found in any transition
    """
    g_comp_defined = True
    if g_comp is None:
        g_comp = NFA()
        g_comp_defined = False

    if not events:
        events = set(g.es["label"])

    # construct new automaton with additional "dead" state
    x_d = g.vcount()
    g_comp.add_vertices(g.vcount() + 1)

    if dead_state_name is not None:
        g_comp.vs["name"] = g.vs["name"] + [dead_state_name]
    g_comp.vs["marked"] = [not i for i in g.vs["marked"]] + [True]

    for t in g.es:
        g_comp.add_edge(t.source, t.target, t["label"], fill_out=True)

    # direct all nonexistent transitions to the "dead" state
    for v in g_comp.vs:
        active_events = set(t["label"] for t in v.out_edges())
        for e in events:
            if not e in active_events:
                g_comp.add_edge(v.index, x_d, e, fill_out=True)

    if not g_comp_defined:
        return g_comp


def inplace_complement(g, events=None, dead_state_name=None):
    """
    Constructs the complement of the given automaton in-place
    """
    if not events:
        events = set(g.es["label"])

    x_d = g.vcount()
    g.add_vertex()

    if dead_state_name is not None:
        g.vs[x_d]["name"] = dead_state_name
    g.vs["marked"] = [not i for i in g.vs["marked"]]

    # direct all nonexistent transitions to the "dead" state
    for v in g.vs:
        active_events = set(t["label"] for t in v.out_edges())
        for e in events:
            if not e in active_events:
                g.add_edge(v.index, x_d, e, fill_out=True)
