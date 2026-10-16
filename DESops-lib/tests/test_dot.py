"""DOT/SVG export for DESops.core.automaton.Automaton (DESops.visualization.dot)."""

import re
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


def test_to_dot_fill_default_radial_solid_and_none():
    assert 'style=radial, fillcolor="#CCCCCC:#6699FF"' in d.dot.to_dot(small())
    assert 'style=filled, fillcolor="#FFEEAA"' in d.dot.to_dot(small(), fill="#FFEEAA")
    assert "fillcolor" not in d.dot.to_dot(small(), fill=None)


@needs_graphviz
def test_uniform_node_size_is_the_label_box_diagonal():
    # A wide one-line label: the circle is the box's diagonal, not Graphviz's
    # sqrt(2) x the box's width, so it is barely wider than the box itself.
    g = Automaton()
    g.add_state("High, Active, Active, T=2", init=True)
    box = 0.06 + 129 / 72  # 2 x MARGIN + Helvetica 12pt text width
    assert box < d.dot.uniform_node_size(g) < 1.05 * box


def test_to_dot_stack_vertical_puts_one_component_per_line():
    pair = d.composition.parallel(small(), small())
    assert 'label="x0\\nx0"' in d.dot.to_dot(pair, stack="vertical")
    assert 'label="x0, x0"' in d.dot.to_dot(pair, stack="horizontal")
    with pytest.raises(ValueError):
        d.dot.to_dot(pair, stack="diagonal")


@needs_graphviz
def test_uniform_node_size_vertical_is_smaller_for_wide_composites():
    g = Automaton()
    g.add_state(("High", "Active", "Active", "T=2"), init=True)
    horizontal = d.dot.uniform_node_size(g)
    assert d.dot.uniform_node_size(g, stack="vertical") < 0.7 * horizontal


def test_to_dot_marked_and_unmarked_share_the_outer_size():
    src = d.dot.to_dot(small(), node_size=1.0)
    ring = 2 * d.dot.RING_GAP
    assert f"width={1.0 + ring:.4f}, height={1.0 + ring:.4f}, fixedsize=true" in src
    assert "shape=doublecircle, width=1.0000, height=1.0000]" in src


@needs_graphviz
def test_write_svg_draws_the_marking_ring_inside_the_fill(tmp_path):
    svg = open(d.dot.write_svg(small(), str(tmp_path / "g.svg"))).read()
    # Marked state x"1: filled outer circle, then the unfilled ring on top.
    outer, inner = re.findall(r"<ellipse [^>]*/>", svg.split('id="node2"')[1])[:2]
    assert 'fill="url(' in outer and 'fill="none"' in inner
    radius = lambda e: float(re.search(r'rx="([\d.]+)"', e).group(1))  # noqa: E731
    assert radius(outer) > radius(inner)
