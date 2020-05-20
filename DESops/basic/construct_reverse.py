def construct_reverse(g, g_r, save_state_names=False, save_marked_states=False):
    """
    Construct the reverse of the given automaton

    g: input automaton
    g_comp: where the reverse automaton will be stored
    """
    g_r.add_vertices(g.vcount())
    g_r.vs["init"] = True
    if save_state_names:
        g_r.vs["name"] = g.vs["name"]
    if save_marked_states:
        g_r.vs["marked"] = g.vs["marked"]

    for t in g.es:
        g_r.add_edge(t.target, t.source, t["label"])
