"""
Conversion between AutomatonData (plain data) and igraph.Graph.

This is the one place DESops.core is allowed to depend on igraph's
Graph construction API. Everything else that needs an igraph.Graph
should go through to_igraph(); everything that wants a plain snapshot
of an igraph-backed automaton should go through from_igraph().
"""

import igraph as ig

from DESops.backends.protocol import AutomatonData


def to_igraph(data: AutomatonData) -> "ig.Graph":
    """Build a fresh igraph.Graph from an AutomatonData snapshot."""
    graph = ig.Graph(directed=True)
    graph.add_vertices(data.num_states)
    graph.vs["name"] = list(data.names)
    graph.vs["marked"] = list(data.marked)
    graph.vs["out"] = [[] for _ in range(data.num_states)]

    if data.edges:
        graph.add_edges(data.edges)
        graph.es["label"] = list(data.labels)
        if data.probs is not None:
            graph.es["prob"] = list(data.probs)

    return graph


def from_igraph(graph: "ig.Graph") -> AutomatonData:
    """Snapshot an igraph.Graph as plain AutomatonData."""
    if "name" in graph.vs.attributes():
        names = list(graph.vs["name"])
    else:
        names = [str(i) for i in range(graph.vcount())]

    if "marked" in graph.vs.attributes():
        marked = [bool(m) for m in graph.vs["marked"]]
    else:
        marked = [False] * graph.vcount()

    edges = [(e.source, e.target) for e in graph.es]

    if "label" in graph.es.attributes():
        labels = list(graph.es["label"])
    else:
        labels = [""] * graph.ecount()

    probs = list(graph.es["prob"]) if "prob" in graph.es.attributes() else None

    events = {label for label in labels if label != ""}

    return AutomatonData(
        names=names,
        marked=marked,
        edges=edges,
        labels=labels,
        events=events,
        probs=probs,
    )
