"""
Graphviz (DOT) export for DESops.core.automaton.Automaton.

to_dot()    -> DOT source text
write_dot() -> .dot file. layout=True runs Graphviz first and writes node
               positions and edge routes into the file, so a program that
               imports DOT (e.g. OmniGraffle) can reuse Graphviz's layout.
write_svg() -> .svg rendered by Graphviz (needs the `dot` binary on PATH).

Conventions: every state is drawn as a circle of the same size (fitted to
the widest label; write_svg/write_dot's uniform=True), filled with a radial
gradient (to_dot's fill); marked states are
double circles; each initial state gets an incoming arrow with no visible
source (an invisible zero-size node); transitions between the same pair of
states are merged into one arc labelled "a, b"; uncontrollable events are drawn dashed
(controllable and uncontrollable events between the same pair get separate
arcs so the style stays meaningful).
"""

import json
import math
import re
import shutil
import subprocess
from collections import defaultdict
from typing import Optional

from DESops.core.automaton import Automaton

FONTSIZE = 12  # state labels, points
MARGIN = 0.03  # space between a state's label and its circle, inches
LINE_SPACING = 1.2  # Graphviz's line height, as a multiple of the font size
PENWIDTH = 1.5  # state circle lines, points
RING_GAP = 4 / 72  # Graphviz's gap between a double circle's rings, inches
# Radial gradient, center color then outer color. A single color fills solid;
# None leaves states unfilled.
DEFAULT_FILL = ("#CCCCCC", "#6699FF")


def _quote(text) -> str:
    s = str(text).replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n")
    return f'"{s}"'


def _flat_name(name, sep: str = ", ") -> str:
    """('I1', 'I2') -> 'I1, I2'; nested tuples from chained compositions flatten too."""
    if isinstance(name, tuple):
        return sep.join(_flat_name(part, sep) for part in name)
    return str(name)


_STACK_SEPARATORS = {"horizontal": ", ", "vertical": "\n"}


def _fill_attrs(fill) -> str:
    if fill is None:
        return ""
    if isinstance(fill, str):
        return f", style=filled, fillcolor={_quote(fill)}"
    center, outer = fill
    return f", style=radial, fillcolor={_quote(f'{center}:{outer}')}"


def to_dot(
    g: Automaton,
    name: str = "G",
    rankdir: str = "LR",
    state_label=None,
    event_label=None,
    node_size: Optional[float] = None,
    fill=DEFAULT_FILL,
    stack: str = "horizontal",
    _all_circles: bool = False,
) -> str:
    """
    DOT source for g. state_label(state) and event_label(event) customize
    the text shown; by default the state's name (composite names from
    parallel/product shown as "I1, I2") and str(event).

    stack: how the default label lays out a composite name's components,
    "horizontal" ("I1, I2" on one line) or "vertical" (one component per
    line). Ignored when state_label is given.

    node_size (inches): every state's label fits a circle of this diameter
    (fixedsize). Marked states draw their second ring outside it; when g has
    marked states, unmarked circles grow by the ring so every state has the
    same outer size. None lets each circle fit its own label, so "W2" comes
    out larger than "I2" in a proportional font; write_svg/write_dot default
    to the uniform size from uniform_node_size() instead.

    fill: (center, outer) colors for a radial gradient, default
    ("#CCCCCC", "#6699FF"); one color string for a solid fill; None for
    no fill.
    """
    if stack not in _STACK_SEPARATORS:
        raise ValueError(f"stack must be 'horizontal' or 'vertical', not {stack!r}")
    sep = _STACK_SEPARATORS[stack]
    state_label = state_label or (lambda s: _flat_name(s.name, sep))
    event_label = event_label or str

    rings = not _all_circles and any(state.marked for state in g.states)
    marked_size = ""
    if node_size is None:
        # Graphviz defaults (min 0.75x0.5in, margin 0.11x0.055in) leave a lot
        # of space around short names; let each circle shrink to its label.
        size = "width=0.3, height=0.3"
    else:
        outer = node_size + 2 * RING_GAP if rings else node_size
        size = f"width={outer:.4f}, height={outer:.4f}, fixedsize=true"
        marked_size = f", width={node_size:.4f}, height={node_size:.4f}"

    lines = [
        f"digraph {_quote(name)} {{",
        f"  rankdir={rankdir};",
        f'  node [shape=circle, fontname="Helvetica", fontsize={FONTSIZE}, {size}, '
        f"margin={MARGIN}, penwidth={PENWIDTH}{_fill_attrs(fill)}];",
        '  edge [fontname="Helvetica", fontsize=11];',
    ]

    for i, state in enumerate(g.states):
        if state.marked and not _all_circles:
            shape = f"doublecircle{marked_size}"
        else:
            shape = "circle"
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
    Diameter (inches) of the smallest circle that holds g's widest state
    label, so every state can be drawn the same size. Graphviz measures the
    text; the circle is the diagonal of the label's box (text plus MARGIN on
    each side). Graphviz's own circle sizing multiplies the box's longer side
    by sqrt(2) instead, which leaves wide one-line labels ~40% too large.
    Marked states are measured as plain circles; their second ring is drawn
    outside.
    """
    kwargs.pop("node_size", None)
    layout = json.loads(_graphviz(["-Tjson"], to_dot(g, _all_circles=True, **kwargs)))
    diameters = []
    for obj in layout.get("objects", []):
        if not obj.get("name", "").startswith("s"):
            continue
        texts = [op for op in obj.get("_ldraw_", []) if op.get("op") == "T"]
        width = max((float(op["width"]) for op in texts), default=0.0) / 72
        height = max(len(texts), 1) * FONTSIZE * LINE_SPACING / 72
        diameters.append(math.hypot(width + 2 * MARGIN, height + 2 * MARGIN))
    return max(diameters, default=0.3)


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


# A double circle in Graphviz's SVG: the filled inner circle, then the outer
# ring with no fill.
_DOUBLE_CIRCLE = re.compile(
    r'<ellipse fill="([^"]*)"([^>]*/>)(\s*)<ellipse fill="none"([^>]*/>)'
)


def _rings_inside(svg: str) -> str:
    """
    Fill a marked state's outer circle instead of its inner one, so the
    second ring is drawn inside the color. Graphviz fills only the innermost
    periphery; DOT has no attribute for this, so it is done on the SVG (a
    .dot file opened elsewhere still shows the ring outside the fill).
    """
    # Outer circle first, filled; then the inner ring on top of it.
    return _DOUBLE_CIRCLE.sub(r'<ellipse fill="\1"\4\3<ellipse fill="none"\2', svg)


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
    svg = _rings_inside(_graphviz(args, to_dot(g, **kwargs)))
    with open(path, "w") as f:
        f.write(svg)
    return path
