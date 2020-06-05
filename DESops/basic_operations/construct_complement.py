from DESops.automata.automata import _Automata


def complement(g, g_comp=None, events=None, save_state_names=False):
    """
    Constructs the complement of the given marked automaton

    g: input marked automaton
    g_comp: where the complement will be stored
    events: the event set of the automaton; required if the event set includes events not found in any transition
    """
    g_comp_defined = True
    if g_comp is None:
        g_comp = _Automata()
        g_comp_defined = False

    if not events:
        events = set(g.es["label"])

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

    if not g_comp_defined:
        return g_comp


def inplace_complement(g, events=None, save_state_names=False):
    """
    Constructs the complement of the given automaton in-place
    """
    if not events:
        events = set(g.es["label"])

    x_d = g.vcount()
    g.add_vertex()

    if save_state_names:
        g.vs[x_d]["name"] = "x_d"
    g.vs["marked"] = [not i for i in g.vs["marked"]]

    # direct all nonexistent transitions to the "dead" state
    for v in g.vs:
        active_events = set(t["label"] for t in v.out_edges())
        for e in events:
            if not e in active_events:
                g.add_edge(v.index, x_d, e)
