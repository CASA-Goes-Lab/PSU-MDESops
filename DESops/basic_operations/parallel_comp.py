# pylint: disable=C0103
"""
Functions relevant to computing the parallel composition of Automata.
Mostly helper functions with the exception of parallel_comp, which
uses the helper functions.

assemble_graph and marked_bool used in product_comp
"""

import sys

from collections import OrderedDict

from DESops.automata.automata import _Automata

def parallel_comp(
    input_list,
    output = None,
    save_state_names=True,
    save_marked_states=False,
    common_events_i=None,
):
    """
    Computes the parallel composition of 2 (or more) automata (igraph Graphs),
    stores the resulting graph in output

    Parameters

    output: directed igraph Graph, assumed to be empty. Used to store the output
        instead of returning a copy. This is different from the interface in the
        Automata class file, which returns a copy of the result of the
        composition.

    input_list: an iterable collection of Automata (class object) for which
        the parallel composition will be computed. If saving state names,
        this should be ordered, as it determines the order that vertex indices
        are stored in the composition's vertex names. MUST have at least two
        graphs (length > 1).

    save_state_names (default True): whether vertex names should be saved
        in the igraph Graph "name" attribute. If set to false, the attribute
        will not be set (less memory usage). Vertex names are a list of indicies
        from each input, in the order used by 'inputs'. For example, in the operation
        A || B || C, a vertex name '(0,3,1)' in the output O means that state is
        composed of vertex 0 in A, 3 in B, and 1 in C (by index, NOT vertex name).

    save_marked_states (default False): whether states in the composition
        should be 'marked' or not (marked if the composed states are both marked).
        An error will be raised if this parameter is True and not all Automata
        in the composition have the "marked" parameter on their vertices.

    common_events_i (default None): if there are events in the event set that are not
        on any transitions of the input graphs, they can be provided through this
        parameter. For example, if in the operation A || B, A has 'c' in its event set,
        but no active transitions, including 'c' in common_events_i forces 'c' not
        to be a private event.

    Doesn't return anything to avoid potentially making redundant copies.

    """


    output_defined = True
    if not isinstance(output, _Automata):
        output_defined = False
        output = _Automata()

    all_common_events = set()
    if common_events_i:
        all_common_events = set(common_events_i)
    for i in range(0, len(input_list) - 1):
        all_common_events = all_common_events.union(
            set(input_list[i].es["label"]).intersection(input_list[i + 1].es["label"])
        )

    # set the first multiplicand term

    for i in range(1, len(input_list)):
        # Intermediate variables for output vertices and edges

        # Storage for vertice product_pairs
        output_vert = OrderedDict()

        # Always have (0,0) state
        # unless there are no shared events, then it's really an empty set of states?
        index = 0

        output_vert_mark = []

        output_edges = []
        output_edge_labels = []

        if i > 1:
            g1 = output
        else:
            g1 = input_list[0]

        g2 = input_list[i]

        # If saving state names, need to keep track of vertices from each automata
        # that 'contributed' to this composite state

        if i > 1 and save_state_names:
            if isinstance(g2.vs["name"][0], list):
                new_name = list(g1.vs["name"][0])
                new_name.append(",".join(g2.vs["name"][0]))
            elif isinstance(g2.vs["name"][0], str):
                new_name = list(g1.vs["name"][0])
                new_name.append(g2.vs["name"][0])
            else:
                sys.exit("ERROR:\nState name must be str or list of str")
            output_vert[(0, 0)] = [index, new_name, (0, 0), (0, 0)]
        elif i == 1 and save_state_names:
            if isinstance(g1.vs["name"][0], str) and isinstance(g2.vs["name"][0], list):
                new_name = [g1.vs["name"][0], ",".join(g2.vs["name"][0])]
            elif isinstance(g1.vs["name"][0], list) and isinstance(
                g2.vs["name"][0], str
            ):
                new_name = [",".join(g1.vs["name"][0]), g2.vs["name"][0]]
            elif isinstance(g1.vs["name"][0], str) and isinstance(
                g2.vs["name"][0], str
            ):
                new_name = [g1.vs["name"][0], g2.vs["name"][0]]
            elif isinstance(g1.vs["name"][0], list) and isinstance(
                g2.vs["name"][0], list
            ):
                new_name = [",".join(g1.vs["name"][0]), ",".join(g2.vs["name"][0])]
            else:
                sys.exit("ERROR:\nState name must be str or list of str")
            output_vert[(0, 0)] = [index, new_name, (0, 0), (0, 0)]
        else:
            output_vert[(0, 0)] = [index, [0, 0], (0, 0)]

        if save_marked_states:
            output_vert_mark.append(marked_bool(g1, g2, (0, 0)))


        if i > 1 and save_state_names:
            output_vert[(0, 0)] = [index, list(g1.vs["name"][0]) + [0]]
        else:
            output_vert[(0, 0)] = [index, [0, 0], (0, 0)]

        adj = dict()

        queue = list()
        queue.append((0,0))

        while queue:
            vert_pair = queue.pop()
            # select edges with source at current vertex
            new_vert_pairs = list()
            new_edge_pairs = list()
            new_edge_labels = list()
            adj_vert = list()

            
            g1_es = g1.vs["out"][vert_pair[0]]
            g2_es = g2.vs["out"][vert_pair[1]]

            g1_labels = {e[1]: e[0] for e in g1_es}
            g2_labels = {e[1]: e[0] for e in g2_es}

            """
            g1_es = g1.es(_source=vert_pair[0])
            g2_es = g2.es(_source=vert_pair[1])

            g1_labels = {e["label"]: e.target for e in g1_es}
            g2_labels = {e["label"]: e.target for e in g2_es}
            """

            l_set = set(g1_labels.keys()).union(g2_labels.keys())

            for x in l_set:
                pcomp_det(
                    x,
                    vert_pair,
                    g1_labels,
                    g2_labels,
                    all_common_events,
                    new_vert_pairs,
                    new_edge_pairs,
                    new_edge_labels,
                    adj_vert,
                )
            # new : (new vert pair, new edge pair, new edge label)
            adj[vert_pair] = adj_vert
            output_edges.extend([new_edge_pair for new_edge_pair in new_edge_pairs])
            output_edge_labels.extend(
                [new_edge_label for new_edge_label in new_edge_labels]
            )

            # see if this is a new vertex pair
            for v in new_vert_pairs:
                if v not in output_vert:
                    index += 1
                    if i > 1 and save_state_names:
                        if isinstance(g2.vs["name"][v[1]], list):
                            new_name = list(g1.vs["name"][v[0]])
                            new_name.append(",".join(g2.vs["name"][0]))
                        elif isinstance(g2.vs["name"][v[1]], str):
                            new_name = list(g1.vs["name"][v[0]])
                            new_name.append(g2.vs["name"][v[1]])
                        else:
                            sys.exit(
                                "ERROR:\nState name must be str or list of str"
                            )
                        output_vert[(v[0], v[1])] = [index, new_name, (v[0], v[1])]
                    elif i == 1 and save_state_names:
                        if isinstance(g1.vs["name"][v[0]], str) and isinstance(
                            g2.vs["name"][v[1]], list
                        ):
                            new_name = [
                                g1.vs["name"][v[0]],
                                ",".join(g2.vs["name"][v[1]]),
                            ]
                        elif isinstance(g1.vs["name"][v[0]], list) and isinstance(
                            g2.vs["name"][v[1]], str
                        ):
                            new_name = [
                                ",".join(g1.vs["name"][v[0]]),
                                g2.vs["name"][v[1]],
                            ]
                        elif isinstance(g1.vs["name"][v[0]], str) and isinstance(
                            g2.vs["name"][v[1]], str
                        ):
                            new_name = [g1.vs["name"][v[0]], g2.vs["name"][v[1]]]
                        elif isinstance(g1.vs["name"][v[0]], list) and isinstance(
                            g2.vs["name"][v[1]], list
                        ):
                            new_name = [
                                ",".join(g1.vs["name"][v[0]]),
                                ",".join(g2.vs["name"][v[1]]),
                            ]
                        else:
                            sys.exit(
                                "ERROR:\nState name must be str or list of str"
                            )
                        output_vert[(v[0], v[1])] = [index, new_name, (v[0], v[1])]
                    else:
                        output_vert[(v[0], v[1])] = [index, [str(v[0]), str(v[1])]]


                    queue.append(v)

            # need to check the new states' neighbors


        if save_marked_states:
            output_vert_mark = [marked_bool(g1, g2, v) for v in output_vert]

        assemble_graph(
            output,
            output_edges,
            index,
            output_vert_mark,
            output_edge_labels,
            output_vert,
            save_state_names,
            save_marked_states,
            adj,
        )
        # to iterate through list of inputs
        # input_list[i] = output
    if not output_defined:
        return output


def assemble_graph(
    output,
    output_edges,
    index,
    output_vert_mark,
    output_edge_labels,
    output_vert,
    save_state_names,
    save_marked_states,
    adj=dict(),
):
    """
    Assemble product_pairs, edge_pairs and edge_labels into resultant graph.
    """
    output_edges_list = list()
    # substitute names of edges via dict mapping
    for vert_pair in output_edges:
        source = output_vert[vert_pair[0]][0]
        target = output_vert[vert_pair[1]][0]
        output_edges_list.append((source, target))

    # add items to new graph
    output._graph.delete_vertices(i for i in range(0, output.vcount()))
    output.add_vertices(index + 1)
    if save_marked_states:
        output.vs["marked"] = output_vert_mark
    output.add_edges(output_edges_list, output_edge_labels)
    if save_state_names:
        output.vs["name"] = [v[1] for v in output_vert.values()]
    if adj:
        # print(adj)
        # print(output_vert.values())
        adj = [
            [(output_vert[v[0]][0], v[1]) for v in adj[l[2]]]
            for l in output_vert.values()
        ]
        output.vs["out"] = adj


def marked_bool(g1, g2, vert_pair):
    """
    graphs g1,g2
    vert_pair (v1, v2) vertices in g1,g2
    "marked" graph attribute string for marked vertices
    """
    if g1.vs[int(vert_pair[0])]["marked"] and g2.vs[int(vert_pair[1])]["marked"]:
        return True
    return False


def pcomp_det(
    x,
    vert_pair,
    g1_labels,
    g2_labels,
    all_common_events,
    new_vert_pairs,
    new_edge_pairs,
    new_edge_labels,
    adj_vert,
):
    """
    Logic for determining type of transition (e.g. private vs. shared events).
    Separated like this to test speed in computation times.
    """
    # Case 0: x is a common event (synchronous treatment)
    if x in g1_labels and x in g2_labels:
        # a = g1_es.select(label_eq = x)[0]
        # b = g2_es.select(label_eq = x)[0]
        a = g1_labels[x]
        b = g2_labels[x]
        new_vert_pairs.append((a, b))
        new_edge_pairs.append(((vert_pair[0], vert_pair[1]), (a, b)))
        new_edge_labels.append(x)
        adj_vert.append(((a, b), x))
    # Case 1: x is private to g1, add self loop at v2
    elif x in g1_labels and x not in g2_labels and x not in all_common_events:
        # a = g1_es.select(label_eq = x)[0]
        a = g1_labels[x]
        new_vert_pairs.append((a, vert_pair[1]))
        new_edge_pairs.append(((vert_pair[0], vert_pair[1]), (a, vert_pair[1])))
        new_edge_labels.append(x)
        adj_vert.append(((a, vert_pair[1]), x))
    # Case 2: x is private to g2, add self loop at v1
    elif x not in g1_labels and x in g2_labels and x not in all_common_events:
        # b = g2_es.select(label_eq = x)[0]
        b = g2_labels[x]
        new_vert_pairs.append((vert_pair[0], b))
        new_edge_pairs.append(((vert_pair[0], vert_pair[1]), (vert_pair[0], b)))
        new_edge_labels.append(x)
        adj_vert.append(((vert_pair[0], b), x))
    # Case 3: if x is a common event not present on any edges sourced at this vertex
