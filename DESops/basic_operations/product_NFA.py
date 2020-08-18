# pylint: disable=C0103
"""
Functions relevant to computing the product composition of nondeterministic Automata

This is modified from the old product_comp. It would probably be better to update the
current product_comp to work with NFAs, rather than having this as a separate function
"""
from collections import OrderedDict

from DESops.automata.NFA import NFA


def product_NFA(g_list, save_state_names=True, save_marked_states=True):
    """
    Computes the product composition of 2 (or more) Automata, and returns
    the resulting composition as an automata.

    Parameters

    g_list: an iterable collection of Automata (class object) for which
        the parallel composition will be computed. If saving state names,
        this should be ordered, as it determines the order that vertex indices
        are stored in the composition's vertex names. MUST have at least two
        graphs (length > 1).

    g_comp: directed igraph Graph, assumed to be empty. Used to store the output
        instead of returning a copy. This is different from the interface in the
        Automata class file, which returns a copy of the result of the
        composition.

    save_state_names (default True): whether vertex names should be saved
        in the igraph Graph "name" attribute. If set to false, the attribute
        will not be set (less memory usage). Vertex names are a list of indicies
        from each input, in the order used by 'inputs'. For example, in the operation
        A || B || C, a vertex name '(0,3,1)' in the output O means that state is
        composed of vertex 0 in A, 3 in B, and 1 in C (by index, NOT vertex name).

    save_marked_states (default False): whether states in the composition
        should be 'marked' or not (marked if the composed states are both marked).
        An error will be raised if this parameter is True, but not all Automata
        in the composition have the "marked" parameter on their vertices.

    Doesn't return anything to avoid potentially making redundant copies.
    """
    g_comp = NFA()

    # Compute intersection of events of all included graphs:
    all_events = g_list[0].es["label"]
    for gi in g_list[1:]:
        all_events = set(all_events).intersection(gi.es["label"])

    for i in range(1, len(g_list)):
        # Intermediate storage for g_comp vertices and edges

        # Storage for vertice pairs
        g_comp_vert = OrderedDict()

        index = 0

        g_comp_vert_mark = list()

        g_comp_edges = []
        g_comp_edge_labels = []
        # (0,0) included immediately as there will always be a state (0,0).
        next_states_to_check = {(0, 0)}

        if i > 1:
            # After the first iteration, the first multiplicand is the
            # result of the last product composition.
            g1 = g_comp
        else:
            g1 = g_list[0]

        g2 = g_list[i]

        if "init" not in g1.vs.attributes():
            g1.vs["init"] = False
            g1.vs[0]["init"] = True
        if "init" not in g2.vs.attributes():
            g2.vs["init"] = False
            g2.vs[0]["init"] = True

        next_states_to_check = {
            (v1.index, v2.index)
            for v1 in g1.vs
            if v1["init"]
            for v2 in g2.vs
            if v2["init"]
        }

        # init attirbute of the constructed graph
        init = list()

        for (v1, v2) in next_states_to_check:
            # Saving the index is useful in converting this OrderedDict into
            # If saving state names, need to keep track of vertices from each automata
            # that 'contributed' to this composite state in the second position
            # of the lists in g_comp_vert's values.
            if i > 1 and save_state_names:
                # If this isn't the first iteration, store the name of vertex 0
                # from the last computation as the start of this vertex name.
                # The result of the last product is stored in place of
                # the first multiplicand, g1.
                g_comp_vert[(v1, v2)] = [index, list(v1["name"]) + [v2]]
            else:
                g_comp_vert[(v1, v2)] = [index, (v1, v2)]
            index = index + 1
            init.append(True)

            if save_marked_states:
                g_comp_vert_mark.append(marked_bool(g1, g2, (v1, v2)))

        # set next_states_to_check returns False when empty
        while next_states_to_check:
            next_states_temp = set()

            # Iterate through all new synchronized states found in last iteration, checking neighbors
            for vert_pair in next_states_to_check:
                # select edges with source at current vertex
                g1_es = g1.es(_source=vert_pair[0])
                g2_es = g2.es(_source=vert_pair[1])

                common_events = all_events.intersection(g1_es["label"]).intersection(
                    g2_es["label"]
                )
                # iterate through each possible common event
                for x in common_events:
                    # iterate through all edges labelled x in both edgesets
                    for a in g1_es.select(label_eq=x):
                        for b in g2_es.select(label_eq=x):
                            new_vert_pair = (a.target, b.target)

                            # see if this is a new vertex pair
                            if new_vert_pair not in g_comp_vert:
                                # this is a new vertex pair: add it to the dict with value 'index'
                                # index just makes it easier later to map edge names from key to index
                                if i > 1 and save_state_names:
                                    # Stores the index, final name of the vertex as the set of states
                                    # in the composition.
                                    g_comp_vert[new_vert_pair] = [
                                        index,
                                        list(g1.vs["name"][new_vert_pair[0]])
                                        + [new_vert_pair[1]],
                                    ]
                                else:
                                    g_comp_vert[new_vert_pair] = [index, new_vert_pair]
                                index = index + 1
                                init.append(False)
                                # check if this vertex pair should get marked
                                # maybe only do this with a flag passed into fn?
                                if save_marked_states:
                                    g_comp_vert_mark.append(
                                        marked_bool(g1, g2, new_vert_pair)
                                    )
                                # need to check the new states' neighbors
                                next_states_temp.add(new_vert_pair)
                            new_edge_pair = ((a.source, b.source), (a.target, b.target))
                            g_comp_edges.append(new_edge_pair)
                            g_comp_edge_labels.append(x)

            next_states_to_check = next_states_temp

        assemble_graph(
            g_comp,
            g_comp_edges,
            index - 1,  # -1 to undo the increment after the last added vertex
            g_comp_vert_mark,
            g_comp_edge_labels,
            g_comp_vert,
            save_state_names,
            save_marked_states,
        )
        g_comp.vs["init"] = init
    # to iterate through list of inputs
    # g_list[i] = g_comp

    g_comp.Euo = set.intersection(*[g.Euo for g in g_list])
    return g_comp


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

    if not save_marked_states:
        output_vert_mark = None

    names = [v[1] for v in output_vert.values()]

    output.add_vertices(index + 1, names, output_vert_mark)
    output.add_edges(output_edges_list, output_edge_labels)

    if adj:
        # print(adj)
        # print(output_vert.values())
        adj = [
            [(output_vert[v[0]][0], v[1]) for v in adj[out_ver[2]]]
            for out_ver in output_vert.values()
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
