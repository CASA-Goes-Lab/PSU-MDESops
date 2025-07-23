from DESops.automata.NFA import NFA
from DESops.automata.DFA import DFA


def reverse(g, inplace=False, use_marked_states=True):
    """
    Constructs the reverse of the given automaton

    Initial and marked states are swapped so that a run is marked in g if and only if its reversal is marked in g_r
    If no states are marked, then all states in the reversed automaton will be initial

    Parameters
    ----------
    g : DFA or NFA
        The automaton
    inplace : bool
        If True, then construct the reverse in place which overwrites `g`. Otherwise create a new automaton.
    use_marked_states : bool
        If True, then swap the marked and initial states in reverse (Default value = True)

    Returns
    -------
    NFA
        The reversed automaton
    """
    if inplace:
        return _inplace_reverse(g, use_marked_states)
    else:
        return _construct_reverse(g, save_state_names=True, use_marked_states=use_marked_states)


def _construct_reverse(g, save_state_names=False, use_marked_states=True):
    """Constructs the reverse of the given automaton

    Initial and marked states are swapped so that a run is marked in g if and only if its reversal is marked in g_r
    If no states are marked, then all states in the reversed automaton will be initial

    g_r: where the reverse automaton will be stored
    use_marked_states: if True, the old marked states will become the new initial states; otherwise all states will be initial

    Parameters
    ----------
    g :

    save_state_names :
         (Default value = False)
    use_marked_states :
         (Default value = True)

    Returns
    -------

    """
    g_rev = NFA()

    g_rev.add_vertices(g.vcount())

    # swap marked/initial states
    if use_marked_states:
        g_rev.vs["init"] = g.vs["marked"]
    else:
        g_rev.vs["init"] = True

    if "init" in g.vs.attributes():
        g_rev.vs["marked"] = g.vs["init"]
    else:
        g_rev.vs["marked"] = False
        g_rev.vs[0]["marked"] = True

    if save_state_names:
        g_rev.vs["name"] = g.vs["name"]

    g_rev.add_edges([(t.target, t.source) for t in g.es], [t['label'] for t in g.es], fill_out=True)

    g_rev.events = g.events
    g_rev.Euo = g.Euo
    g_rev.generate_out()

    return g_rev


def _inplace_reverse(g, use_marked_states=True):
    """Constructs the reverse of the given automaton in-place

    Initial and marked states are swapped so that a run is marked in g if and only if its reversal is marked in g_r
    If no states are marked, then all states in the reversed automaton will be initial

    g: the automaton
    use_marked_states: if True, the old marked states will become the new initial states; otherwise all states will be initial

    Parameters
    ----------
    g :

    use_marked_states :
         (Default value = True)

    Returns
    -------

    """
    if isinstance(g, DFA):
        raise ValueError("Cannot construct reverse in place if the automaton is a DFA.")
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

    edge_states = [(t.target, t.source) for t in g.es]
    edge_labels = [t['label'] for t in g.es]
    g.delete_edges(g.es)
    g.add_edges(edge_states, edge_labels, fill_out=True)
