from DESops.automata.NFA import NFA
from DESops.automata.DFA import DFA


def complement(g, inplace=False, events=None, dead_state_name=None):
    """
    Constructs the complement of the given automaton.
    Note, the result may be nondeterministic even if the input is deterministic

    Constructed in place if `g_comp == g`. In this case the automaton `g` must be an `NFA`.

    Parameters
    ----------
    g : DFA or NFA
        The automaton
    inplace : bool
        If True, then construct the complement in place which overwrites `g`. Otherwise create a new automaton.
    events : set or NoneType
        The event set of the automaton (Default value = None)
    dead_state_name : object
        The name of the added dead state (Default value = None)

    Returns
    -------
    NFA
         The complement automaton
    """
    if inplace:
        _inplace_complement(g, events, dead_state_name)
        return g
    else:
        return _construct_complement(g, events, dead_state_name)


def _construct_complement(g, events=None, dead_state_name=None):
    """
    Constructs the complement of the given marked automaton (not in place)

    g:
    g_comp: where the complement will be stored
    events: the event set of the automaton; required if the event set includes events not found in any transition

    Parameters
    ----------
    g : DFA or NFA
        The automaton (with marking)
    events : set or NoneType
         (Default value = None)
    dead_state_name : object
         (Default value = None)

    Returns
    -------
    NFA
         The complement automaton
    """
    g_comp = NFA()

    if not events:
        events = set(g.es["label"])

    # construct new automaton with additional "dead" state
    x_d = g.vcount()
    g_comp.add_vertices(g.vcount() + 1)
    g_comp.vs["init"] = g.vs["init"] + [False]

    if dead_state_name is not None:
        g_comp.vs["name"] = g.vs["name"] + [dead_state_name]
    g_comp.vs["marked"] = [not i for i in g.vs["marked"]] + [True]

    g_comp.add_edges([(t.source, t.target) for t in g.es],
                     [(t["label"]) for t in g.es],
                     fill_out=True)

    # direct all nonexistent transitions to the "dead" state
    edge_states = []
    edge_labels = []
    for v in g_comp.vs:
        active_events = set(t["label"] for t in v.out_edges())
        edge_states += [(v.index, x_d) for e in events if not e in active_events]
        edge_labels += [e for e in events if not e in active_events]
    g_comp.add_edges(edge_states, edge_labels, fill_out=True)

    return g_comp


def _inplace_complement(g, events=None, dead_state_name=None):
    """
    Constructs the complement of the given automaton in place

    Parameters
    ----------
    g : NFA
        The automaton (with marking)
    events : set or NoneType
         (Default value = None)
    dead_state_name : object
         (Default value = None)
    """
    if isinstance(g, DFA):
        raise ValueError("Cannot construct complement in place if the automaton is a DFA.")
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

