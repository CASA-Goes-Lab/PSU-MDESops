# pylint: disable=C0103
"""
Convert an igraph Graph instance into an 'fsm' filetype,
which is used/defined by the DESUMA software.
"""

# from DESops.Event import Event


def igraph_to_fsm(fsm_filename, g, Euc=None, Euo=None, plot_prob=False):
    """
    fsm_filename: filename to write output to, e.g. "name_text.fsm"
    g: igraph Graph object to read from (an Automata instance would work as well).

    Keyword attributes used in this package (for igraph Graph edge/vert sequences):
    "name": vertexseq label to refer to state names
    "marked": vertexseq label to refer to marked attr
    "label": edgeseq label to refer to label of transition
    "obs": edgeseq label to refer to transition observability attr
    "contr": edgeseq label to refer to transition controllability attr

    "prob": for PFA, this additional attribute describes the probability of a transition
        occuring for a given state pair & event label. If "prob" is defined in the edgeseq,
        and plot_prob input parameter is set to True, the "prob" will be appended to the
        end of the transition line.

        For example: in state 1, there is a controllable-unobservable transition
        to state 2 with label 'a' and probability p=0.5
        > <'fsm_file.fsm'>
        > 1   0   1
        > 0   2   c   uo   0.5
        > ...
    """

    # If obs/contr attributes are not defined, mark them as true
    if "obs" not in g.es.attributes():
        if not Euo:
            g.es["obs"] = [True]
    if "contr" not in g.es.attributes():
        if not Euc:
            g.es["contr"] = [True]

    not_marked = False
    if "marked" not in g.vs.attributes():
        not_marked = True

    if "name" not in g.vs.attributes():
        g.vs["name"] = [i for i in range(0, g.vcount())]

    with open(fsm_filename, "w") as f:
        f.write(str(g.vcount()))
        f.write("\n\n")

        for v in g.vs:
            # print(','.join(v["name"]))
            f.write(",".join(v["name"]))
            f.write("\t")
            if not_marked:
                f.write("0")
            else:
                t = v["marked"]
                f.write("1" if t else "0")
            f.write("\t")

            edge_seq = g.es.select(_source=v.index)
            f.write(str(len(edge_seq)))
            f.write("\n")
            for trans in edge_seq:
                if isinstance(trans["label"], Event):
                    f.write(str(trans.tuple))
                else:
                    f.write(str2(trans["label"]))
                f.write("\t")
                f.write(",".join(g.vs["name"][trans.target]))
                f.write("\t")
                if Euc:
                    f.write("c" if trans["label"] not in Euc else "uc")
                else:
                    f.write("c" if trans["contr"] else "uc")
                f.write("\t")
                if Euo:
                    f.write("o" if trans["label"] not in Euo else "uo")
                else:
                    f.write("o" if trans["obs"] else "uo")
                if plot_prob and "prob" in g.es.attributes():
                    f.write("\t")
                    f.write(trans["prob"])
                f.write("\n")
            f.write("\n")


def str2(name):
    """
    Smarter str casting for frozensets. Converting
    frozenset to set makes 'frozenset({1,2,3})'
    as 'set({1,2,3})' which prints as '{1,2,3}'.
    """
    if isinstance(name, frozenset):
        return str(set(name))
    return str(name)
