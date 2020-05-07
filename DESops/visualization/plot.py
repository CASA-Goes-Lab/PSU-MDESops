import igraph as ig
from DESops.automata.event.event import Event
def plot(automata, layout_i="kk", bbox_i=(0, 0, 2000, 2000), margin_i=100):
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

    P.vs["name"] = [str2(v) for v in P.vs["name"]]

    P.vs["label"] = P.vs["name"]
    P.vs["label_size"] = [30]
    P.vs["size"] = [70]
    ig.plot(P, bbox=bbox_i, layout=layout_i, margin=margin_i)


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