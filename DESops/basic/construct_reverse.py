def construct_reverse(g, g_r, save_state_names=False, save_marked_states=False):
    """
    Constructs the reverse of the given automaton

    g: input automaton
    g_r: where the reverse automaton will be stored
    """
    g_r.add_vertices(g.vcount())
    g_r.vs["init"] = True

    if save_state_names:
        g_r.vs["name"] = g.vs["name"]
    if save_marked_states:
        g_r.vs["marked"] = g.vs["marked"]

    for t in g.es:
        g_r.add_edge(t.target, t.source, t["label"])


def inplace_reverse(g):
    """
    Constructs the reverse of the given automaton in-place
    """
    g.vs["init"] = True

    if g.ecount() == 0:
        return
    t = g.es[0]
    for _ in range(g.ecount()):
        g.add_edge(t.target, t.source, t["label"])
        t.delete()
