"""
Graphviz (DOT) export for DESops.core.automaton.Automaton.

to_dot()    -> DOT source text
write_dot() -> .dot file. layout=True runs Graphviz first and writes node
               positions and edge routes into the file, so a program that
               imports DOT (e.g. OmniGraffle) can reuse Graphviz's layout.
write_svg() -> .svg rendered by Graphviz (needs the `dot` binary on PATH).

Conventions: every state is drawn as a circle of the same size (fitted to
the widest label; write_svg/write_dot's uniform=True); marked states are
double circles; each initial state gets an incoming arrow with no visible
source (an invisible zero-size node); transitions between the same pair of
states are merged into one arc labelled "a, b"; uncontrollable events are drawn dashed
(controllable and uncontrollable events between the same pair get separate
arcs so the style stays meaningful).
"""

import json
import shutil
import subprocess
from collections import defaultdict
from typing import Optional

from DESops.core.automaton import Automaton


def _quote(text) -> str:
    s = str(text).replace("\\", "\\\\").replace('"', '\\"')
    return f'"{s}"'


def _flat_name(name) -> str:
    """('I1', 'I2') -> 'I1, I2'; nested tuples from chained compositions flatten too."""
    if isinstance(name, tuple):
        return ", ".join(_flat_name(part) for part in name)
    return str(name)


def to_dot(
    g: Automaton,
    name: str = "G",
    rankdir: str = "LR",
    state_label=None,
    event_label=None,
    node_size: Optional[float] = None,
    _all_circles: bool = False,
) -> str:
    """
    DOT source for g. state_label(state) and event_label(event) customize
    the text shown; by default the state's name (composite names from
    parallel/product shown as "I1, I2") and str(event).

    node_size (inches): draw every state as a circle of this diameter
    (fixedsize). None lets each circle fit its own label, so "W2" comes out
    larger than "I2" in a proportional font; write_svg/write_dot default to
    the uniform size from uniform_node_size() instead.
    """
    state_label = state_label or (lambda s: _flat_name(s.name))
    event_label = event_label or str

    if node_size is None:
        # Graphviz defaults (min 0.75x0.5in, margin 0.11x0.055in) leave a lot
        # of space around short names; let each circle shrink to its label.
        size = "width=0.3, height=0.3"
    else:
        size = f"width={node_size:.4f}, height={node_size:.4f}, fixedsize=true"

    lines = [
        f"digraph {_quote(name)} {{",
        f"  rankdir={rankdir};",
        f'  node [shape=circle, fontname="Helvetica", fontsize=12, {size}, margin=0.03];',
        '  edge [fontname="Helvetica", fontsize=11];',
    ]

    for i, state in enumerate(g.states):
        shape = "doublecircle" if state.marked and not _all_circles else "circle"
        lines.append(f"  s{i} [label={_quote(state_label(state))}, shape={shape}];")

    for i in sorted(g.init):
        lines.append(
            f'  init{i} [shape=none, label="", width=0, height=0, margin=0];'
        )
        lines.append(f"  init{i} -> s{i};")

    arcs = defaultdict(list)
    for source, event, target in g.transitions():
        arcs[(source, target, event in g.Euc)].append(event)
    for (source, target, uncontrollable), events in arcs.items():
        label = ", ".join(sorted(event_label(e) for e in events))
        style = ", style=dashed" if uncontrollable else ""
        lines.append(f"  s{source} -> s{target} [label={_quote(label)}{style}];")

    lines.append("}")
    return "\n".join(lines) + "\n"


def _graphviz(args, source: str) -> str:
    exe = shutil.which("dot")
    if exe is None:
        raise RuntimeError("Graphviz `dot` not found on PATH (macOS: brew install graphviz)")
    result = subprocess.run(
        [exe, *args], input=source, capture_output=True, text=True, check=True
    )
    return result.stdout


def uniform_node_size(g: Automaton, **kwargs) -> float:
    """
    Diameter (inches) of the circle needed for g's widest state label, as
    measured by Graphviz, so every state can be drawn the same size. Marked
    states are measured as plain circles; their second ring is drawn outside.
    """
    kwargs.pop("node_size", None)
    layout = json.loads(_graphviz(["-Tjson"], to_dot(g, _all_circles=True, **kwargs)))
    widths = [
        float(obj["width"])
        for obj in layout.get("objects", [])
        if obj.get("name", "").startswith("s")
    ]
    return max(widths, default=0.3)


def _sized(g: Automaton, kwargs: dict) -> dict:
    if kwargs.get("node_size") is None and g.states:
        kwargs = dict(kwargs, node_size=uniform_node_size(g, **kwargs))
    return kwargs


def write_dot(
    g: Automaton, path: str, layout: bool = False, uniform: bool = True, **kwargs
) -> str:
    """
    Write g as DOT. layout=True includes Graphviz positions. uniform=True
    (default) draws every state the same size; it needs Graphviz to measure
    labels, and is skipped for a plain (layout=False) file if Graphviz is
    not installed.
    """
    if uniform and (layout or shutil.which("dot")):
        kwargs = _sized(g, kwargs)
    source = to_dot(g, **kwargs)
    if layout:
        source = _graphviz(["-Tdot"], source)
    with open(path, "w") as f:
        f.write(source)
    return path


def write_svg(
    g: Automaton, path: str, engine: Optional[str] = None, uniform: bool = True, **kwargs
) -> str:
    """
    Render g to SVG with Graphviz. engine: dot (default), neato, circo, ...
    uniform=True (default) draws every state the same size.
    """
    if uniform:
        kwargs = _sized(g, kwargs)
    args = ["-Tsvg"] + ([f"-K{engine}"] if engine else [])
    svg = _graphviz(args, to_dot(g, **kwargs))
    with open(path, "w") as f:
        f.write(svg)
    return path
