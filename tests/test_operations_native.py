"""
Tests for the native (pure-Python, no igraph) backend of core/operations/
algorithms, alongside the existing igraph-backed default. Both backends
should produce equivalent results; this suite checks that directly rather
than just re-testing behavior already covered elsewhere.

See doc/logs/v2-igraph-decoupling.md for why these coexist rather than
one replacing the other.
"""

import DESops as d
import tests.util as util


def _out_sets(g):
    """{state_index: {(target, label), ...}} for order-independent comparison."""
    return {i: set(g.vs["out"][i]) for i in range(g.vcount())}


def test_complement_construct_native_matches_igraph():
    g = util.load_model("models/textbook/fig_2-1.fsm")
    g = d.NFA(g)

    g_igraph = d.complement(g, backend="igraph")
    g_native = d.complement(g, backend="native")

    assert g_native.vcount() == g_igraph.vcount()
    assert g_native.ecount() == g_igraph.ecount()
    assert g_native.vs["marked"] == g_igraph.vs["marked"]
    assert _out_sets(g_native) == _out_sets(g_igraph)


def test_complement_construct_native_matches_expected():
    # Same expectations as test_Automata.py::test_complement, run against
    # the native backend directly.
    g = util.load_model("models/textbook/fig_2-1.fsm")
    g = d.NFA(g)

    g_c = d.complement(g, backend="native")
    assert g_c.vcount() == 4
    assert g_c.ecount() == 12
    assert (3, d.Event("b")) in g_c.vs[0]["out"]
    assert g_c.vs["marked"] == [False, True, False, True]


def test_complement_inplace_native_matches_expected():
    g = util.load_model("models/textbook/fig_2-1.fsm")
    g = d.NFA(g)

    d.complement(g, inplace=True, backend="native")
    assert g.vcount() == 4
    assert g.ecount() == 12
    assert (3, d.Event("b")) in g.vs[0]["out"]
    assert g.vs["marked"] == [False, True, False, True]


def test_complement_native_with_dead_state_name():
    g = d.NFA()
    g.add_vertices(2, marked=[False, True])
    g.add_edge(0, 1, d.Event("a"))

    g_c = d.complement(g, backend="native", events={d.Event("a"), d.Event("b")}, dead_state_name="dead")
    assert g_c.vs["name"][-1] == "dead"
    assert g_c.vcount() == 3


def test_complement_native_dfa_raises_like_igraph():
    g = d.DFA()
    g.add_vertices(1)

    for backend in ("igraph", "native"):
        try:
            d.complement(g, backend=backend)
            raised = False
        except KeyError:
            raised = True
        assert raised, f"backend={backend} should raise for a DFA with no 'init' attribute"


def test_complement_unknown_backend_raises():
    g = d.NFA()
    try:
        d.complement(g, backend="bdd")
        assert False, "expected ValueError"
    except ValueError:
        pass
