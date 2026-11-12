"""
Graphviz (DOT) drawings of automata: an Automaton or a ValidAutomaton.

    to_dot(G)                 -> DOT source text
    write_dot(G, path)        -> .dot file (layout=True: with Graphviz's node positions and edge
                                 routes, for programs that import DOT, e.g. OmniGraffle)
    write_svg(G, path)        -> .svg rendered by Graphviz
    svg(G)                    -> the SVG text (e.g. for a notebook: IPython.display.SVG(svg(G)))

Needs the Graphviz `dot` program for SVG and for equal-size states (macOS:
`brew install graphviz`). Plain Python, not verified (nothing here decides a result).

Style (the one of Examples/v2/datacenter/figures, from the legacy DESops writer):
- left to right; Helvetica; every state a circle of the same size (fitted to the widest label);
  filled with a radial gradient, grey center to blue;
- marked states: double circles (the second ring drawn inside the fill in the SVG);
- each initial state: an arrow from nowhere;
- composite names from parallel/product/supervisor, e.g. (('I1', 'I2'), 'E'), shown as
  "I1, I2, E" (or one component per line with stack="vertical");
- transitions between the same two states merged into one arc labelled "a, b";
  uncontrollable events dashed (kept on separate arcs from controllable ones).
"""

import json
import math
import re
import shutil
import subprocess
from collections import defaultdict
from typing import Any, Callable, Optional, Union

from core_aut import Automaton, ValidAutomaton

FONTSIZE = 12          # state labels, points
MARGIN = 0.03          # space between a state's label and its circle, inches
LINE_SPACING = 1.2     # Graphviz's line height, as a multiple of the font size
PENWIDTH = 1.5         # state circle lines, points
RING_GAP = 4 / 72      # Graphviz's gap between a double circle's rings, inches
# Radial gradient, center color then outer color. One color string fills solid; None: no fill.
DEFAULT_FILL = ("#CCCCCC", "#6699FF")

_STACK_SEPARATORS = {"horizontal": ", ", "vertical": "\n"}


def _parts(G: Union[Automaton, ValidAutomaton]):
    """(names, marked, init, transitions, Euc) of either automaton class."""
    if isinstance(G, ValidAutomaton):
        return list(G.names), set(G.marked), sorted(G.init), list(G.transitions()), G.Euc
    return ([s.name for s in G.states], {i for i, s in enumerate(G.states) if s.marked},
            sorted(G.init), list(G.transitions()), set(G.Euc))


def _quote(text) -> str:
    s = str(text).replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n")
    return f'"{s}"'


def _flat_name(name, sep: str = ", ") -> str:
    """('I1', 'I2') -> 'I1, I2'; nested tuples from chained compositions flatten too."""
    if isinstance(name, tuple):
        return sep.join(_flat_name(part, sep) for part in name)
    return str(name)


def _fill_attrs(fill) -> str:
    if fill is None:
        return ""
    if isinstance(fill, str):
        return f", style=filled, fillcolor={_quote(fill)}"
    center, outer = fill
    return f", style=radial, fillcolor={_quote(f'{center}:{outer}')}"


def to_dot(G: Union[Automaton, ValidAutomaton], name: str = "G", rankdir: str = "LR",
           state_label: Optional[Callable[[Any], str]] = None,
           event_label: Optional[Callable[[Any], str]] = None,
           node_size: Optional[float] = None, fill=DEFAULT_FILL, stack: str = "horizontal",
           _all_circles: bool = False) -> str:
    """DOT source for G.

    state_label(name) and event_label(event) customize the text shown; by default the state's
    name (composite names shown as "I1, I2") and str(event).
    stack: how the default label lays out a composite name, "horizontal" ("I1, I2") or
    "vertical" (one component per line). Ignored when state_label is given.
    node_size (inches): every state's label fits a circle of this diameter. Marked states draw
    their second ring outside it, and when G has marked states the plain circles grow by the
    ring, so every state has the same outer size. None: each circle fits its own label
    (write_svg / write_dot / svg use the uniform size from uniform_node_size instead).
    fill: (center, outer) colors of a radial gradient; one color for a solid fill; None: none.
    rankdir: "LR" (default), "TB", "RL" or "BT"."""
    if stack not in _STACK_SEPARATORS:
        raise ValueError(f"stack must be 'horizontal' or 'vertical', not {stack!r}")
    sep = _STACK_SEPARATORS[stack]
    state_label = state_label or (lambda n: _flat_name(n, sep))
    event_label = event_label or str
    names, marked, init, transitions, euc = _parts(G)

    rings = not _all_circles and bool(marked)
    marked_size = ""
    if node_size is None:
        # Graphviz defaults leave a lot of space around short names; let circles shrink.
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
    for i, n in enumerate(names):
        shape = f"doublecircle{marked_size}" if i in marked and not _all_circles else "circle"
        lines.append(f"  s{i} [label={_quote(state_label(n))}, shape={shape}];")
    for i in init:
        lines.append(f'  init{i} [shape=none, label="", width=0, height=0, margin=0];')
        lines.append(f"  init{i} -> s{i};")
    arcs = defaultdict(list)
    for source, event, target in transitions:
        arcs[(source, target, event in euc)].append(event)
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
    result = subprocess.run([exe, *args], input=source, capture_output=True, text=True,
                            check=True)
    return result.stdout


def uniform_node_size(G: Union[Automaton, ValidAutomaton], **kwargs) -> float:
    """Diameter (inches) of the smallest circle that holds G's widest state label, so every
    state can be drawn the same size. Graphviz measures the text; the circle is the diagonal of
    the label's box (text plus MARGIN on each side). Graphviz's own circle sizing multiplies
    the box's longer side by sqrt(2), which leaves wide one-line labels about 40% too large."""
    kwargs.pop("node_size", None)
    layout = json.loads(_graphviz(["-Tjson"], to_dot(G, _all_circles=True, **kwargs)))
    diameters = []
    for obj in layout.get("objects", []):
        if not obj.get("name", "").startswith("s"):
            continue
        texts = [op for op in obj.get("_ldraw_", []) if op.get("op") == "T"]
        width = max((float(op["width"]) for op in texts), default=0.0) / 72
        height = max(len(texts), 1) * FONTSIZE * LINE_SPACING / 72
        diameters.append(math.hypot(width + 2 * MARGIN, height + 2 * MARGIN))
    return max(diameters, default=0.3)


def _num_states(G) -> int:
    return G.num_states if isinstance(G, ValidAutomaton) else len(G.states)


def _sized(G, kwargs: dict) -> dict:
    if kwargs.get("node_size") is None and _num_states(G):
        kwargs = dict(kwargs, node_size=uniform_node_size(G, **kwargs))
    return kwargs


def write_dot(G: Union[Automaton, ValidAutomaton], path, layout: bool = False,
              uniform: bool = True, **kwargs) -> str:
    """Write G as DOT. layout=True includes Graphviz's positions. uniform=True (default) draws
    every state the same size; it needs Graphviz to measure labels, and is skipped for a plain
    (layout=False) file when Graphviz is not installed. kwargs: as to_dot."""
    if uniform and (layout or shutil.which("dot")):
        kwargs = _sized(G, kwargs)
    source = to_dot(G, **kwargs)
    if layout:
        source = _graphviz(["-Tdot"], source)
    with open(path, "w") as f:
        f.write(source)
    return str(path)


# A double circle in Graphviz's SVG: the filled inner circle, then the outer ring, not filled.
_DOUBLE_CIRCLE = re.compile(r'<ellipse fill="([^"]*)"([^>]*/>)(\s*)<ellipse fill="none"([^>]*/>)')


def _rings_inside(text: str) -> str:
    """Fill a marked state's outer circle instead of its inner one, so the second ring is drawn
    inside the color. Graphviz fills only the innermost ring and DOT has no attribute for this,
    so it is done on the SVG (a .dot file opened elsewhere still shows the ring outside)."""
    return _DOUBLE_CIRCLE.sub(r'<ellipse fill="\1"\4\3<ellipse fill="none"\2', text)


def svg(G: Union[Automaton, ValidAutomaton], engine: Optional[str] = None,
        uniform: bool = True, **kwargs) -> str:
    """G rendered by Graphviz, as SVG text. engine: dot (default), neato, circo, ...
    uniform=True (default) draws every state the same size. kwargs: as to_dot."""
    if uniform:
        kwargs = _sized(G, kwargs)
    args = ["-Tsvg"] + ([f"-K{engine}"] if engine else [])
    return _rings_inside(_graphviz(args, to_dot(G, **kwargs)))


def write_svg(G: Union[Automaton, ValidAutomaton], path, engine: Optional[str] = None,
              uniform: bool = True, **kwargs) -> str:
    """Render G to an SVG file (see svg)."""
    with open(path, "w") as f:
        f.write(svg(G, engine=engine, uniform=uniform, **kwargs))
    return str(path)
