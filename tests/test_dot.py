"""DOT/SVG export for DESops.core.automaton.Automaton (DESops.visualization.dot)."""

import shutil

import pytest

import DESops as d
from DESops.core.automaton import Automaton

a, b, u = d.Event("a"), d.Event("b"), d.Event("u")
needs_graphviz = pytest.mark.skipif(shutil.which("dot") is None, reason="Graphviz not installed")


def small():
    g = Automaton(Euc={u})
    g.add_state("x0", init=True)
    g.add_state('x"1', marked=True)
    g.add_transitions([(0, a, 1), (0, b, 1), (1, u, 0)])
    return g


def test_to_dot_states_init_and_marking():
    src = d.dot.to_dot(small())
    assert 's0 [label="x0", shape=circle];' in src
    assert 's1 [label="x\\"1", shape=doublecircle];' in src
    assert "init0 -> s0;" in src


def test_to_dot_merges_parallel_arcs_and_dashes_uncontrollable():
    src = d.dot.to_dot(small())
    assert 's0 -> s1 [label="a, b"];' in src
    assert 's1 -> s0 [label="u", style=dashed];' in src


def test_to_dot_tuple_state_names_from_parallel():
    src = d.dot.to_dot(d.composition.parallel(small(), small()))
    assert 'label="x0, x0"' in src


@needs_graphviz
def test_uniform_node_size_fits_widest_label():
    g = Automaton()
    g.add_state("I2", init=True)
    g.add_state("W2")
    narrow = d.dot.uniform_node_size(g)
    g.add_state("W1, W2")
    assert d.dot.uniform_node_size(g) > narrow


@needs_graphviz
def test_laid_out_dot_gives_every_state_the_same_width(tmp_path):
    g = Automaton()
    g.add_state("I2", init=True)
    g.add_state("W2", marked=True)
    g.add_transition(0, a, 1)
    src = open(d.dot.write_dot(g, str(tmp_path / "g.dot"), layout=True)).read()
    assert "fixedsize=true" in src


@needs_graphviz
def test_write_svg_and_laid_out_dot(tmp_path):
    svg = d.dot.write_svg(small(), str(tmp_path / "g.svg"))
    assert open(svg).read().lstrip().startswith(("<?xml", "<svg"))

    laid_out = open(d.dot.write_dot(small(), str(tmp_path / "g.dot"), layout=True)).read()
    assert "pos=" in laid_out
