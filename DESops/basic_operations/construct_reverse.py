from DESops.automata.NFA import NFA


def reverse(g, inplace=False):
    """
    Constructs the reverse of the given automaton

    Initial and marked states are swapped so that a run is marked in g if and only if its reversal is marked in g_r
    If no states are marked, then all states in the reversed automaton will be initial

    Parameters:
    g: the automaton
    inplace: if True, the automaton will overwrite the original g with its reverse automaton
    """
    if inplace:
        inplace_reverse(g)
        return

    return construct_reverse(g, save_state_names=True)


def construct_reverse(g, g_r=None, save_state_names=False):
    """
    Constructs the reverse of the given automaton

    Initial and marked states are swapped so that a run is marked in g if and only if its reversal is marked in g_r
    If no states are marked, then all states in the reversed automaton will be initial

    g: input automaton
    g_r: where the reverse automaton will be stored
    """
    g_r_defined = True
    if g_r is None:
        g_r = NFA()
        g_r_defined = False

    g_r.add_vertices(g.vcount())

    # swap marked/initial states
    g_r.vs["init"] = g.vs["marked"]

    if "init" in g.vs.attributes():
        g_r.vs["marked"] = g_r.vs["init"]
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


def inplace_reverse(g):
    """
    Constructs the reverse of the given automaton in-place

    Initial and marked states are swapped so that a run is marked in g if and only if its reversal is marked in g_r
    If no states are marked, then all states in the reversed automaton will be initial
    """
    # swap marked/initial states
    if "init" not in g.vs.attributes():
        g.vs["init"] = False
        g.vs[0]["init"] = True
    old_init = g.vs["init"]

    g.vs["init"] = g.vs["marked"]

    g.vs["marked"] = old_init

    if g.ecount() == 0:
        return

    g.vs["out"] = [[] for _ in range(g.vcount())]

    t = g.es[0]
    for _ in range(g.ecount()):
        g.add_edge(t.target, t.source, t["label"], fill_out=True)
        t.delete()
