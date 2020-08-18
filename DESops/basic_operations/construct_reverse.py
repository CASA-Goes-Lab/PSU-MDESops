from DESops.automata.NFA import NFA


def reverse(g, inplace=False, use_marked_states=True):
    """
    Constructs the reverse of the given automaton

    Initial and marked states are swapped so that a run is marked in g if and only if its reversal is marked in g_r
    If no states are marked, then all states in the reversed automaton will be initial

    Parameters:
    g: the automaton
    inplace: if True, the automaton will overwrite the original g with its reverse automaton
    use_marked_states: if True, the old marked states will become the new initial states; otherwise all states will be initial
    """
    if inplace:
        inplace_reverse(g, use_marked_states)
        return

    return construct_reverse(
        g, save_state_names=True, use_marked_states=use_marked_states
    )


def construct_reverse(g, g_r=None, save_state_names=False, use_marked_states=True):
    """
    Constructs the reverse of the given automaton

    Initial and marked states are swapped so that a run is marked in g if and only if its reversal is marked in g_r
    If no states are marked, then all states in the reversed automaton will be initial

    g: input automaton
    g_r: where the reverse automaton will be stored
    use_marked_states: if True, the old marked states will become the new initial states; otherwise all states will be initial
    """
    g_r_defined = True
    if g_r is None:
        g_r = NFA()
        g_r_defined = False

    g_r.add_vertices(g.vcount())

    # swap marked/initial states
    if use_marked_states:
        g_r.vs["init"] = g.vs["marked"]
    else:
        g_r.vs["init"] = True

    if "init" in g.vs.attributes():
        g_r.vs["marked"] = g.vs["init"]
    else:
        g_r.vs["marked"] = False
        g_r.vs[0]["marked"] = True

    if save_state_names:
        g_r.vs["name"] = g.vs["name"]

    for t in g.es:
        g_r.add_edge(t.target, t.source, t["label"])

    g_r.events = g.events
    g_r.Euo = g.Euo
    g_r.generate_out()

    if not g_r_defined:
        return g_r


def inplace_reverse(g, use_marked_states=True):
    """
    Constructs the reverse of the given automaton in-place

    Initial and marked states are swapped so that a run is marked in g if and only if its reversal is marked in g_r
    If no states are marked, then all states in the reversed automaton will be initial

    g: the automaton
    use_marked_states: if True, the old marked states will become the new initial states; otherwise all states will be initial
    """
    # swap marked/initial states
    if "init" not in g.vs.attributes():
        g.vs["init"] = False
        g.vs[0]["init"] = True
    old_init = g.vs["init"]

    if use_marked_states:
        g.vs["init"] = g.vs["marked"]
    else:
        g.vs["init"] = True

    g.vs["marked"] = old_init

    if g.ecount() == 0:
        return

    g.vs["out"] = [[] for _ in range(g.vcount())]

    t = g.es[0]
    for _ in range(g.ecount()):
        g.add_edge(t.target, t.source, t["label"], fill_out=True)
        t.delete()
