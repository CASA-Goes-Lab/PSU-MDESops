"""
Tests for the native (pure-Python, no igraph) backend of
DESops.io.fsm_to_igraph.read_fsm, alongside the existing igraph-backed
default. Both backends should produce equivalent results; this suite
checks that directly across every .fsm fixture in tests/models/, plus the
"read into an existing Automata" (`g=`) call pattern used by tests/util.py.

See doc/logs/v2-igraph-decoupling.md for why these coexist rather than
one replacing the other.
"""

from pathlib import Path

import DESops as d

cwd = Path(__file__).parent.resolve()
ALL_FSM_FILES = sorted(cwd.joinpath("models").rglob("*.fsm"))


def _out_sets(g):
    """{state_index: {(target, label), ...}} for order-independent comparison."""
    return {
        i: {(t[0], t[1]) for t in g._out_view["out"][i]} for i in range(g.vcount())
    }


def _summarize(g):
    return {
        "vcount": g.vcount(),
        "ecount": g.ecount(),
        "names": list(g.to_data().names),
        "marked": list(g.to_data().marked),
        "out": _out_sets(g),
        "events": g.events,
        "Euc": g.Euc,
        "Euo": g.Euo,
        "type": type(g).__name__,
    }


def test_read_fsm_native_matches_igraph_for_every_model():
    mismatches = []
    checked = 0
    for path in ALL_FSM_FILES:
        try:
            g_igraph = d.read_fsm(str(path), backend="igraph")
        except Exception:
            # Not every fixture under tests/models/ is a well-formed,
            # standalone .fsm file meant to be read by read_fsm() on its
            # own (some are inputs to other readers/tools) -- only compare
            # backends where the existing igraph reader actually succeeds.
            continue

        if not hasattr(g_igraph, "to_data"):
            # A completely empty (0-state) .fsm file makes
            # _read_fsm_igraph's type dispatch match nothing, so it
            # returns the bare scratch ig.Graph instead of a DFA/NFA/PFA
            # -- a pre-existing quirk of that function for this one
            # degenerate input (see doc/logs/v2-igraph-decoupling.md).
            # There's no native equivalent of "return a bare ig.Graph";
            # the native reader defaults to an empty DFA here instead, so
            # skip the equivalence comparison for this one case rather
            # than comparing against something structurally different by
            # design.
            continue

        g_native = d.read_fsm(str(path), backend="native")
        checked += 1

        s_igraph = _summarize(g_igraph)
        s_native = _summarize(g_native)
        if s_igraph != s_native:
            mismatches.append((str(path), s_igraph, s_native))

    assert checked > 0
    assert not mismatches, "\n".join(
        f"{path}:\n  igraph={s_i}\n  native={s_n}" for path, s_i, s_n in mismatches
    )


def test_read_fsm_native_stays_native():
    # A model with no init= caller-provided g -- fresh construction should
    # never force an igraph build.
    path = ALL_FSM_FILES[0]
    g = d.read_fsm(str(path), backend="native")
    assert "_graph" not in g.__dict__


def test_read_fsm_native_into_existing_dfa_matches_igraph():
    path = cwd.joinpath("models", "model1.fsm")

    g_igraph = d.DFA()
    d.read_fsm(str(path), g_igraph, backend="igraph")

    g_native = d.DFA()
    d.read_fsm(str(path), g_native, backend="native")

    assert _summarize(g_igraph) == _summarize(g_native)


def test_read_fsm_native_edge_attrs_match_igraph():
    path = cwd.joinpath("models", "model1.fsm")

    g_igraph = d.read_fsm(str(path), backend="igraph")
    g_native = d.read_fsm(str(path), backend="native")

    assert sorted(g_igraph.es["obs"]) == sorted(g_native.to_data().edge_attrs["obs"])
    assert sorted(g_igraph.es["contr"]) == sorted(g_native.to_data().edge_attrs["contr"])


def test_read_fsm_native_unknown_backend_raises():
    path = cwd.joinpath("models", "model1.fsm")
    try:
        d.read_fsm(str(path), backend="bdd")
        assert False, "expected ValueError"
    except ValueError:
        pass
