"""
Characterization tests for the mutation methods of Automata/DFA/NFA/PFA
(core/automata.py, dfa.py, nfa.py, pfa.py). These currently mutate the
underlying igraph.Graph directly and are independently reimplemented in
each subclass; this suite exists as a safety net for the future change
that makes AutomatonData (DESops.backends.protocol) the primary storage
instead of igraph. See doc/scoping-report.md for the plan.
"""

import pytest

import DESops as d


# --- add_vertex / add_vertices ---------------------------------------------


def test_add_vertex_default_name():
    g = d.DFA()
    g.add_vertex()
    assert g.vcount() == 1
    assert g.vs[0]["name"] == "0"
    assert g.vs[0]["marked"] is None


def test_add_vertex_explicit_name_and_marked():
    g = d.DFA()
    g.add_vertex(name="s0", marked=True)
    assert g.vs[0]["name"] == "s0"
    assert g.vs[0]["marked"] is True


def test_add_vertices_default_names():
    g = d.DFA()
    g.add_vertices(3)
    assert g.vcount() == 3
    assert g.vs["name"] == ["0", "1", "2"]
    assert g.vs["marked"] == [False, False, False]


def test_add_vertices_explicit_names_and_marked():
    g = d.DFA()
    g.add_vertices(2, names=["a", "b"], marked=[True, False])
    assert g.vs["name"] == ["a", "b"]
    assert g.vs["marked"] == [True, False]


def test_add_vertices_incremental():
    g = d.DFA()
    g.add_vertices(2)
    g.add_vertices(2)
    assert g.vcount() == 4
    assert g.vs["name"] == ["0", "1", "2", "3"]


def test_add_vertices_mismatched_names_raises():
    g = d.DFA()
    with pytest.raises(d.error.IncongruencyError):
        g.add_vertices(2, names=["only_one"])


# --- add_edge / add_edges (DFA) ---------------------------------------------


def test_dfa_add_edge_basic():
    g = d.DFA()
    g.add_vertices(2)
    g.add_edge(0, 1, d.Event("a"))
    assert g.ecount() == 1
    assert g.es[0]["label"] == d.Event("a")
    assert g.vs[0]["out"] == [(1, d.Event("a"))]


def test_dfa_add_edge_determinism_violation_raises():
    g = d.DFA()
    g.add_vertices(2)
    g.add_edge(0, 1, d.Event("a"))
    with pytest.raises(d.error.DeterminismError):
        g.add_edge(0, 0, d.Event("a"))


def test_dfa_add_edges_basic():
    g = d.DFA()
    g.add_vertices(3)
    g.add_edges([(0, 1), (1, 2)], [d.Event("a"), d.Event("b")])
    assert g.ecount() == 2
    assert g.es["label"] == [d.Event("a"), d.Event("b")]
    assert g.vs[0]["out"] == [(1, d.Event("a"))]
    assert g.vs[1]["out"] == [(2, d.Event("b"))]


def test_dfa_add_edges_determinism_violation_raises():
    g = d.DFA()
    g.add_vertices(2)
    g.add_edges([(0, 1)], [d.Event("a")])
    with pytest.raises(d.error.DeterminismError):
        g.add_edges([(0, 0)], [d.Event("a")])


def test_dfa_add_edges_empty_noop():
    g = d.DFA()
    g.add_vertices(1)
    g.add_edges([], [])
    assert g.ecount() == 0


# --- add_edge / add_edges (NFA) ---------------------------------------------


def test_nfa_add_edge_allows_nondeterminism():
    g = d.NFA()
    g.add_vertices(2)
    g.add_edge(0, 1, d.Event("a"))
    g.add_edge(0, 1, d.Event("a"))  # same label twice: fine for NFA
    assert g.ecount() == 2


def test_nfa_add_edges_basic():
    g = d.NFA()
    g.add_vertices(2)
    g.add_edges([(0, 1), (0, 1)], [d.Event("a"), d.Event("b")])
    assert g.ecount() == 2
    assert sorted(g.es["label"], key=str) == sorted(
        [d.Event("a"), d.Event("b")], key=str
    )
    assert set(g.vs[0]["out"]) == {(1, d.Event("a")), (1, d.Event("b"))}


# --- add_edge / add_edges (PFA) ---------------------------------------------


def test_pfa_add_edge_stores_prob():
    g = d.PFA()
    g.add_vertices(2)
    g.add_edge(0, 1, d.Event("a"), 0.5)
    assert g.es[0]["prob"] == 0.5
    assert g.vs[0]["out"] == [(1, d.Event("a"), 0.5)]


def test_pfa_add_edges_stores_probs():
    g = d.PFA()
    g.add_vertices(2)
    g.add_edges([(0, 1)], [d.Event("a")], [0.5])
    assert g.es["prob"] == [0.5]
    assert g.vs[0]["out"] == [(1, d.Event("a"), 0.5)]


def test_pfa_add_edges_multiple_preserves_probs():
    g = d.PFA()
    g.add_vertices(3)
    g.add_edges([(0, 1)], [d.Event("a")], [0.5])
    g.add_edges([(1, 2)], [d.Event("b")], [0.25])
    assert g.es["prob"] == [0.5, 0.25]


def test_pfa_add_edges_mismatched_probs_raises_before_mutating():
    g = d.PFA()
    g.add_vertices(2)
    with pytest.raises(d.error.IncongruencyError):
        g.add_edges([(0, 1)], [d.Event("a")], [0.5, 0.25])
    # the failed call must not have partially mutated the graph
    assert g.ecount() == 0


# --- delete_vertices / delete_edges -----------------------------------------


def test_delete_vertices_removes_state_and_incident_edges():
    g = d.DFA()
    g.add_vertices(3)
    g.add_edges([(0, 1), (1, 2)], [d.Event("a"), d.Event("b")])
    g.delete_vertices([g.vs[2]])
    assert g.vcount() == 2
    assert g.ecount() == 1


def test_delete_vertices_regenerates_out():
    g = d.DFA()
    g.add_vertices(3)
    g.add_edges([(0, 1), (1, 2)], [d.Event("a"), d.Event("b")])
    g.delete_vertices([g.vs[2]])
    assert g.vs[1]["out"] == []


def test_delete_edges_regenerates_out():
    g = d.DFA()
    g.add_vertices(2)
    g.add_edge(0, 1, d.Event("a"))
    g.delete_edges(g.es)
    assert g.ecount() == 0
    assert g.vs[0]["out"] == []


# --- copy() ------------------------------------------------------------------


def test_dfa_copy_is_independent():
    g = d.DFA()
    g.add_vertices(2)
    g.add_edge(0, 1, d.Event("a"))
    h = g.copy()

    assert isinstance(h, d.DFA)
    assert h.vcount() == g.vcount()
    assert h.ecount() == g.ecount()

    h.add_vertex()
    assert h.vcount() != g.vcount()


# --- vcount/ecount and traversal helpers -------------------------------------


def test_next_states_and_active_events():
    g = d.DFA()
    g.add_vertices(3)
    g.add_edges([(0, 1), (0, 2)], [d.Event("a"), d.Event("b")])
    assert g.next_states(0) == {1, 2}
    assert g.active_events(0) == {d.Event("a"), d.Event("b")}


def test_events_between():
    g = d.DFA()
    g.add_vertices(2)
    g.add_edge(0, 1, d.Event("a"))
    assert g.events_between(0, 1) == {d.Event("a")}
    assert g.events_between(0, 0) == set()


def test_trans():
    g = d.DFA()
    g.add_vertices(2)
    g.add_edge(0, 1, d.Event("a"))
    assert g.trans(0, d.Event("a")) == 1
    assert g.trans(0, d.Event("z")) is None


# --- lazy igraph view --------------------------------------------------------
#
# self._graph/.vs/.es/.write_dot are built on demand (via __getattr__), not
# eagerly on every mutation -- self._data (AutomatonData) is the source of
# truth. These tests check the laziness itself, not just its results (which
# the tests above already cover): a DFA built and read purely through the
# native API should never construct an igraph.Graph at all. See
# doc/logs/v2-igraph-decoupling.md.


def test_dfa_construction_stays_native():
    g = d.DFA()
    g.add_vertices(3)
    g.add_edges([(0, 1), (1, 2)], [d.Event("a"), d.Event("b")])
    assert "_graph" not in g.__dict__


def test_dfa_add_edge_with_check_dfa_stays_native():
    # check_DFA's duplicate-label check reads adjacency too -- must not
    # force igraph on every single add_edge call.
    g = d.DFA()
    g.add_vertices(2)
    g.add_edge(0, 1, d.Event("a"), check_DFA=True)
    assert "_graph" not in g.__dict__


def test_dfa_add_edge_check_dfa_still_raises_natively():
    g = d.DFA()
    g.add_vertices(2)
    g.add_edge(0, 1, d.Event("a"), check_DFA=True)
    with pytest.raises(Exception):
        g.add_edge(0, 1, d.Event("a"), check_DFA=True)


def test_native_read_methods_do_not_force_igraph():
    g = d.DFA()
    g.add_vertices(3)
    g.add_edges([(0, 1), (0, 2)], [d.Event("a"), d.Event("b")])

    assert g.vcount() == 3
    assert g.ecount() == 2
    assert g.next_states(0) == {1, 2}
    assert g.active_events(0) == {d.Event("a"), d.Event("b")}
    assert g.trans(0, d.Event("a")) == 1
    assert g.events_between(0, 1) == {d.Event("a")}
    data = g.to_data()
    assert data.num_states == 3 and data.num_edges == 2

    assert "_graph" not in g.__dict__


def test_ur_from_set_does_not_force_igraph():
    g = d.DFA()
    g.add_vertices(3)
    g.add_edges([(0, 1), (1, 2)], [d.Event("uo"), d.Event("b")])
    g.Euo = {d.Event("uo")}
    g.UR.Euo = g.Euo

    result = g.UR.from_set({0}, {d.Event("uo")}, freeze_result=True)

    assert result == frozenset({0, 1})
    assert "_graph" not in g.__dict__


def test_accessing_vs_lazily_builds_graph_and_is_correct():
    g = d.DFA()
    g.add_vertices(3)
    g.add_edges([(0, 1), (1, 2)], [d.Event("a"), d.Event("b")])
    assert "_graph" not in g.__dict__

    assert g.vs["name"] == ["0", "1", "2"]

    assert "_graph" in g.__dict__


def test_mutation_after_lazy_build_invalidates_graph_again():
    g = d.DFA()
    g.add_vertices(2)
    g.add_edge(0, 1, d.Event("a"))
    g.vs  # force the lazy build
    assert "_graph" in g.__dict__

    g.add_edge(1, 0, d.Event("b"))

    assert "_graph" not in g.__dict__
    # and the mutation is correctly visible once rebuilt
    assert g.vs["out"][1] == [(0, d.Event("b"))]


def test_direct_vs_edit_is_absorbed_on_next_mutation():
    # Consumer code throughout DESops mutates g.vs directly rather than
    # exclusively through Automata's own methods; _resync_data() must still
    # pick that up before the next mutation, exactly as before this change.
    g = d.DFA()
    g.add_vertices(2)
    g.vs[0]["marked"] = True  # forces the lazy build as a side effect

    g.add_vertex()  # any mutating method resyncs first

    assert g.vs["marked"] == [True, False, None]


def test_nfa_add_edges_return_value_forces_igraph_but_still_works():
    # NFA.add_edge/add_edges return an igraph Edge/EdgeSeq (unlike DFA's,
    # which return None), so calling them always builds the igraph view --
    # that's an existing part of their public contract, not changed here.
    g = d.NFA()
    g.add_vertices(2)
    edges = g.add_edges([(0, 1)], [d.Event("a")])
    assert "_graph" in g.__dict__
    assert edges[0]["label"] == d.Event("a")
