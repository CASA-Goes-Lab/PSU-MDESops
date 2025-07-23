import igraph as ig
from pydash import flatten_deep

from DESops.automata.event import Event


def plot(
    automata,
    layout="kk",
    bbox=(0, 0, 1000, 1000),
    margin=100,
    flatten_state_name=False,
    inline=False,
):
    """
    Plot the Graph attribute of the Automata.
    If the automata is an IDA or similar, the plot will differentiate the two state types.
    layout_i, bbox_i and margin_i are passed into the igraph plot function,
    and are defined in the igraph plot documentation.
    Roughly:
        layout_i: layout algorithm used, default is Kamada-Kawai force-directed algorithm.
        bbox_i: bounding box of the plot, with dimensions in pixels.
        margin_i: margin width in pixels to surround the plot.
    Plotting is done by the igraph library.
    Requires cairo package to be installed.
    """
    # try:
    #     import cairo
    # except ImportError:
    #     raise DependencyNotInstalledError("cairo required to plot Igraph graphs")

    P = automata._graph.copy()
    P.es["label"] = [str2(l) for l in P.es["label"]]

    if "name" not in P.vs.attributes():
        P.vs["name"] = [i for i in range(0, P.vcount())]
    elif flatten_state_name is True:
        P.vs["name"] = [",".join(flatten_deep(v["name"])) for v in P.vs]

    P.vs["name"] = [str2(v) for v in P.vs["name"]]

    P.vs["label"] = P.vs["name"]
    P.vs["label_size"] = [30]
    P.vs["size"] = [70]
    return ig.plot(P, bbox=bbox, layout=layout, margin=margin, inline=inline)


def str2(label):
    """
    Helpful function used occasionally in this file.
    Handles smart/alternate casting to strings (str objects).

    e.g:
    If label is an inserted Event object, with label 'a',
    this function will return the string "('a','i')"

    If label is a frozenset, frozenset({1,2,3}), this function
    will return the str casting of the set casting of the frozenset,
    or "{1,2,3}"

    Otherwise, returns the normal str casting of label.
    """
    if isinstance(label, Event):
        return str(label.name())
    if isinstance(label, frozenset):
        return str(set(label))
    return str(label)
