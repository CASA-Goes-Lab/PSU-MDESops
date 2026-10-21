"""
Tests for the backend-agnostic AutomatonData model and its igraph
conversion (DESops.backends). These are new, standalone units with no
dependency on core/automata.py's own (still igraph-backed) storage.
"""

import DESops as d
from DESops.backends.igraph_backend import from_igraph, to_igraph
from DESops.backends.protocol import AutomatonData


def test_automaton_data_counts():
    data = AutomatonData(
        names=["0", "1", "2"],
        marked=[False, True, False],
        edges=[(0, 1), (1, 2)],
        labels=["a", "b"],
        events={"a", "b"},
    )
    assert data.num_states == 3
    assert data.num_edges == 2


def test_to_igraph_basic():
    data = AutomatonData(
        names=["0", "1"],
        marked=[False, True],
        edges=[(0, 1)],
        labels=["a"],
        events={"a"},
    )
    graph = to_igraph(data)
    assert graph.vcount() == 2
    assert graph.ecount() == 1
    assert graph.vs["name"] == ["0", "1"]
    assert graph.vs["marked"] == [False, True]
    assert graph.es["label"] == ["a"]
    assert (graph.es[0].source, graph.es[0].target) == (0, 1)


def test_to_igraph_empty():
    data = AutomatonData(names=[], marked=[], edges=[], labels=[], events=set())
    graph = to_igraph(data)
    assert graph.vcount() == 0
    assert graph.ecount() == 0


def test_to_igraph_with_probs():
    data = AutomatonData(
        names=["0", "1"],
        marked=[False, False],
        edges=[(0, 1)],
        labels=["a"],
        events={"a"},
        probs=[0.5],
    )
    graph = to_igraph(data)
    assert graph.es["prob"] == [0.5]


def test_from_igraph_round_trip():
    original = AutomatonData(
        names=["s0", "s1", "s2"],
        marked=[False, True, False],
        edges=[(0, 1), (1, 2), (2, 0)],
        labels=["a", "b", "a"],
        events={"a", "b"},
    )
    graph = to_igraph(original)
    recovered = from_igraph(graph)

    assert recovered.names == original.names
    assert recovered.marked == original.marked
    assert recovered.edges == original.edges
    assert recovered.labels == original.labels
    assert recovered.events == original.events
    assert recovered.probs is None


def test_from_igraph_round_trip_with_probs():
    original = AutomatonData(
        names=["s0", "s1"],
        marked=[False, True],
        edges=[(0, 1)],
        labels=["a"],
        events={"a"},
        probs=[0.75],
    )
    graph = to_igraph(original)
    recovered = from_igraph(graph)
    assert recovered.probs == original.probs


def test_to_data_matches_dfa():
    g = d.DFA()
    g.add_vertices(3, marked=[False, True, False])
    g.add_edges([(0, 1), (1, 2)], [d.Event("a"), d.Event("b")])

    data = g.to_data()

    assert data.names == ["0", "1", "2"]
    assert data.marked == [False, True, False]
    assert data.edges == [(0, 1), (1, 2)]
    assert data.labels == [d.Event("a"), d.Event("b")]
    assert data.events == {d.Event("a"), d.Event("b")}


def test_to_data_matches_nfa_with_multi_edges():
    g = d.NFA()
    g.add_vertices(2)
    g.add_edges([(0, 1), (0, 1)], [d.Event("a"), d.Event("b")])

    data = g.to_data()

    assert data.num_states == 2
    assert data.num_edges == 2
    assert set(data.edges) == {(0, 1)}
    assert set(data.labels) == {d.Event("a"), d.Event("b")}


def test_to_data_matches_pfa_probs():
    g = d.PFA()
    g.add_vertices(2)
    g.add_edges([(0, 1)], [d.Event("a")], [0.5])

    data = g.to_data()

    assert data.probs == [0.5]


def test_to_data_empty_automaton():
    g = d.DFA()
    data = g.to_data()
    assert data.num_states == 0
    assert data.num_edges == 0
    assert data.events == set()


# --- extra vertex/edge attributes (e.g. "init", "forbidden" from wmod I/O) --


def test_to_igraph_with_vertex_attrs():
    data = AutomatonData(
        names=["0", "1"],
        marked=[False, False],
        edges=[],
        labels=[],
        events=set(),
        vertex_attrs={"init": [True, False], "forbidden": [False, True]},
    )
    graph = to_igraph(data)
    assert graph.vs["init"] == [True, False]
    assert graph.vs["forbidden"] == [False, True]


def test_to_igraph_with_edge_attrs():
    data = AutomatonData(
        names=["0", "1"],
        marked=[False, False],
        edges=[(0, 1)],
        labels=["a"],
        events={"a"},
        edge_attrs={"weight": [3]},
    )
    graph = to_igraph(data)
    assert graph.es["weight"] == [3]


def test_from_igraph_round_trip_with_extra_attrs():
    original = AutomatonData(
        names=["0", "1"],
        marked=[False, True],
        edges=[(0, 1)],
        labels=["a"],
        events={"a"},
        vertex_attrs={"init": [True, False]},
        edge_attrs={"weight": [3]},
    )
    recovered = from_igraph(to_igraph(original))
    assert recovered.vertex_attrs == original.vertex_attrs
    assert recovered.edge_attrs == original.edge_attrs


def test_to_data_captures_dynamic_vertex_attrs():
    # Mirrors DESops/io/wmod_to_igraph.py's read_wmod, which passes
    # arbitrary extra kwargs (e.g. "init") to add_vertex().
    g = d.DFA()
    g.add_vertex(name="s0", init=True)
    g.add_vertex(name="s1", init=False)

    data = g.to_data()

    assert data.vertex_attrs["init"] == [True, False]
