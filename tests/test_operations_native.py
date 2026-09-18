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


# --- parallel -----------------------------------------------------------


def test_parallel_native_matches_igraph():
    g1 = util.load_model("models/textbook/fig_2-1.fsm")
    g2 = util.load_model("models/textbook/fig_2-2.fsm")

    p_igraph = d.composition.parallel(g1, g2, backend="igraph")
    p_native = d.composition.parallel(g1, g2, backend="native")

    assert p_native.vcount() == p_igraph.vcount()
    assert p_native.ecount() == p_igraph.ecount()
    assert p_native.vs["marked"] == p_igraph.vs["marked"]
    assert p_native.vs["name"] == p_igraph.vs["name"]
    assert _out_sets(p_native) == _out_sets(p_igraph)


def test_parallel_native_three_automata_matches_igraph():
    # Chaining two compositions (g1 x g2, then that result x g3) means the
    # BFS in each backend visits states via `set(...) | set(...)`, whose
    # iteration order isn't strictly a function of content -- the two
    # backends can legitimately number states differently after two
    # rounds even though the automata are equivalent. Compare by language
    # rather than by exact state index for this reason (the two-automaton
    # case above matches by index exactly, since there's no compounding).
    from DESops.core.operations.language_equivalence import compare_language

    g1 = util.load_model("models/textbook/fig_2-1.fsm")
    g2 = util.load_model("models/textbook/fig_2-2.fsm")
    g3 = util.load_model("models/textbook/fig_2-21_G1.fsm")

    p_igraph = d.composition.parallel(g1, g2, g3, backend="igraph")
    p_native = d.composition.parallel(g1, g2, g3, backend="native")

    assert p_native.vcount() == p_igraph.vcount()
    assert p_native.ecount() == p_igraph.ecount()
    assert compare_language(p_native, p_igraph, type="both")


def test_parallel_native_empty_input():
    g1 = d.DFA()
    g2 = util.load_model("models/textbook/fig_2-1.fsm")
    assert d.composition.parallel(g1, g2, backend="native").vcount() == 0


# --- observer -------------------------------------------------------------


def test_observer_native_matches_igraph():
    G_t = util.load_model("models/G_t.fsm")

    obs_igraph = d.composition.observer(G_t, backend="igraph")
    obs_native = d.composition.observer(G_t, backend="native")

    assert obs_native.vcount() == obs_igraph.vcount()
    assert obs_native.ecount() == obs_igraph.ecount()
    assert obs_native.vs["marked"] == obs_igraph.vs["marked"]
    assert _out_sets(obs_native) == _out_sets(obs_igraph)


def test_observer_native_matches_expected():
    # Same expectations as test_Automata.py::test_observer.
    G_t = util.load_model("models/G_t.fsm")
    obs = d.composition.observer(G_t, backend="native")
    assert obs.vcount() == 5
    assert obs.ecount() == 6
    assert d.Event("a") in (v[1] for v in obs.vs["out"][0])


def test_observer_native_empty_automaton():
    g = d.DFA()
    obs = d.composition.observer(g, backend="native")
    assert obs.vcount() == 0


def test_observer_native_dfa_input_matches_igraph():
    # DFA input takes the `init_states = frozenset({0})` path rather than
    # reading an "init" vertex attribute.
    g = util.load_model("models/textbook/fig_2-1.fsm")
    assert isinstance(g, d.DFA)

    obs_igraph = d.composition.observer(g, backend="igraph")
    obs_native = d.composition.observer(g, backend="native")

    assert obs_native.vcount() == obs_igraph.vcount()
    assert obs_native.ecount() == obs_igraph.ecount()


# --- unobservable reach (out_adjacency as a drop-in for the igraph "out") -


def test_out_adjacency_drives_unobservable_reach_same_as_igraph():
    from DESops.core.automata import UnobservableReach

    g = util.load_model("models/G_t.fsm")
    data = g.to_data()
    adjacency = data.out_adjacency()

    native_ur = UnobservableReach(g.Euo, {"out": adjacency})

    for start in range(g.vcount()):
        expected = g.UR.from_set({start}, frozenset(g.Euo), freeze_result=True)
        actual = native_ur.from_set({start}, frozenset(g.Euo), freeze_result=True)
        assert actual == expected
