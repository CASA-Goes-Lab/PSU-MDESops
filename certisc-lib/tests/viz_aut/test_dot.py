"""
Drawing automata (viz_aut): the DOT text, and the SVG when Graphviz is installed.
"""

import re
import shutil

import pytest

from core_aut import Automaton, validate
from ops_aut import parallel_2aut
from viz_aut import svg, to_dot, uniform_node_size, write_dot, write_svg

needs_dot = pytest.mark.skipif(shutil.which("dot") is None, reason="Graphviz not installed")


def _machine():
    G = Automaton(events=["start", "finish", "break", "repair"], Euc=["break"])
    idle = G.add_state("Idle", marked=True, init=True)
    work = G.add_state("Working")
    down = G.add_state("Down")
    G.add_transition(idle, "start", work)
    G.add_transition(work, "finish", idle)
    G.add_transition(work, "break", down)
    G.add_transition(down, "repair", idle)
    G.add_transition(down, "start", idle)            # merged with repair into one arc
    return G


@pytest.mark.parametrize("valid", [False, True])
def test_dot_text(valid):
    G = _machine()
    text = to_dot(validate(G) if valid else G)
    assert 's0 [label="Idle", shape=doublecircle];' in text          # marked
    assert 's1 [label="Working", shape=circle];' in text
    assert "init0 -> s0;" in text                                     # initial arrow
    assert 's1 -> s2 [label="break", style=dashed];' in text          # uncontrollable
    assert 's1 -> s0 [label="finish"];' in text
    assert 's2 -> s0 [label="repair, start"];' in text                # merged arc
    assert "rankdir=LR;" in text and 'fillcolor="#CCCCCC:#6699FF"' in text


def test_composite_names():
    G = _machine()
    P = parallel_2aut(G, G)
    assert 'label="Idle, Idle"' in to_dot(P)
    assert 'label="Idle\\nIdle"' in to_dot(P, stack="vertical")
    with pytest.raises(ValueError, match="stack"):
        to_dot(P, stack="diagonal")


def test_options():
    G = _machine()
    text = to_dot(G, node_size=0.8, fill="#FFFFFF", rankdir="TB",
                  state_label=lambda n: n.upper(), event_label=lambda e: e[:2])
    assert "fixedsize=true" in text and "rankdir=TB;" in text
    assert 'style=filled, fillcolor="#FFFFFF"' in text and 'label="IDLE"' in text
    assert 'label="re, st"' in text
    assert "style=radial" not in to_dot(G, fill=None) and "fillcolor" not in to_dot(G, fill=None)


@needs_dot
def test_svg_files(tmp_path):
    G = validate(_machine())
    d = uniform_node_size(G)
    assert 0.3 < d < 2.0
    p = write_svg(G, tmp_path / "g.svg")
    text = open(p).read()
    assert text.startswith("<?xml") and "radialGradient" in text
    # every state has the same outer size
    sizes = set(re.findall(r'<ellipse fill="url[^"]*" stroke="black" stroke-width="1.5" '
                           r'cx="[^"]*" cy="[^"]*" rx="([^"]*)"', text))
    assert len(sizes) == 1
    assert svg(G) == text
    q = write_dot(G, tmp_path / "g.dot", layout=True)
    assert "pos=" in open(q).read()
    assert write_svg(Automaton(events=["a"]), tmp_path / "empty.svg")      # no states
