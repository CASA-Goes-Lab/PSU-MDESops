"""
Drawing automata with Graphviz (part of the certisc distribution). Public API:

- to_dot(G, ...) -> str             DOT source
- write_dot(G, path, layout=False)  .dot file
- write_svg(G, path, engine=None)   .svg file (needs the Graphviz `dot` program)
- svg(G) -> str                     SVG text (notebooks: IPython.display.SVG(svg(G)))
- uniform_node_size(G) -> float     the common state diameter, inches

G: an Automaton or a ValidAutomaton. Plain Python, not verified (drawing decides nothing).
Style and options: viz_aut/dot.py.
"""

from viz_aut.dot import svg, to_dot, uniform_node_size, write_dot, write_svg

__all__ = ["to_dot", "write_dot", "write_svg", "svg", "uniform_node_size"]
