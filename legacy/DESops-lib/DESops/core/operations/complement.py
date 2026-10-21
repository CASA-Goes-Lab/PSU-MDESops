from collections import defaultdict

from DESops.core.nfa import NFA
from DESops.core.dfa import DFA


def complement(g, inplace=False, events=None, dead_state_name=None, backend="igraph"):
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
    backend : str
        Which implementation to use: "igraph" (default, queries the automaton's
        igraph view directly) or "native" (pure Python over AutomatonData, no
        igraph dependency). Both produce equivalent results; "native" exists so
        a future non-igraph backend (e.g. BDD) can be compared or substituted.

    Returns
    -------
    NFA
         The complement automaton
    """
    if backend == "igraph":
        construct, inplace_fn = _construct_complement_igraph, _inplace_complement_igraph
    elif backend == "native":
        construct, inplace_fn = _construct_complement_native, _inplace_complement_native
    else:
        raise ValueError(f"Unknown backend: {backend!r}")

    if inplace:
        inplace_fn(g, events, dead_state_name)
        return g
    else:
        return construct(g, events, dead_state_name)


def _construct_complement_igraph(g, events=None, dead_state_name=None):
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


def _inplace_complement_igraph(g, events=None, dead_state_name=None):
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


def _construct_complement_native(g, events=None, dead_state_name=None):
    """
    Pure-Python (no igraph) equivalent of _construct_complement_igraph.
    Operates entirely on g.to_data(); the result is built through
    NFA/add_vertices/add_edges, which are themselves igraph-free.
    """
    data = g.to_data()
    n = data.num_states

    if not events:
        events = set(data.labels)

    active_events_by_source = defaultdict(set)
    for (source, _target), label in zip(data.edges, data.labels):
        active_events_by_source[source].add(label)

    x_d = n
    # data.vertex_attrs["init"] intentionally raises (matching the igraph
    # implementation's g.vs["init"] KeyError) if g has no "init" attribute,
    # e.g. a DFA rather than an NFA.
    init = list(data.vertex_attrs["init"]) + [False]
    marked = [not m for m in data.marked] + [True]
    names = list(data.names) + [dead_state_name] if dead_state_name is not None else None

    g_comp = NFA()
    g_comp.add_vertices(n + 1, names=names, marked=marked, init=init)

    pairs = list(data.edges)
    labels = list(data.labels)
    # Include x_d itself: with no outgoing edges yet, every event is
    # "missing" for it too, giving it self-loops that make it an actual
    # trap state (matching the igraph implementation, which loops over
    # g_comp.vs -- already including the just-added dead state).
    for v in range(n + 1):
        for e in events:
            if e not in active_events_by_source[v]:
                pairs.append((v, x_d))
                labels.append(e)

    g_comp.add_edges(pairs, labels, fill_out=True)
    return g_comp


def _inplace_complement_native(g, events=None, dead_state_name=None):
    """
    Pure-Python (no igraph) equivalent of _inplace_complement_igraph.
    """
    if isinstance(g, DFA):
        raise ValueError("Cannot construct complement in place if the automaton is a DFA.")

    data = g.to_data()
    n = data.num_states

    if not events:
        events = set(data.labels)

    active_events_by_source = defaultdict(set)
    for (source, _target), label in zip(data.edges, data.labels):
        active_events_by_source[source].add(label)

    x_d = n
    if dead_state_name is not None:
        g.add_vertex(name=dead_state_name)
    else:
        g.add_vertex()

    # The dead state ends up marked=True: the igraph implementation adds
    # the vertex first (giving it marked=None, add_vertex's default for an
    # omitted kwarg) and only then negates every vertex's marking in bulk,
    # and `not None` is True. Append True directly for the same result.
    g.update_marked([not m for m in data.marked] + [True])

    # Include x_d itself, matching the igraph implementation's `for v in
    # g.vs` (already including the just-added dead state): with no
    # outgoing edges yet, it gets self-loops for every event, making it an
    # actual trap state.
    for v in range(n + 1):
        for e in events:
            if e not in active_events_by_source[v]:
                g.add_edge(v, x_d, e, fill_out=True)
