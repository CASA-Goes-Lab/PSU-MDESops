# pylint: disable=C0103
"""
Functions relevant to computing the product composition of Automata.
Mostly helper functions with the exception of product_comp, which
uses the helper functions.

product_comp uses assemble_graph and marked_bool from parallel_comp,
previously those functions were implemented in both product_comp and
parallel_comp but were essentially redundant.
"""
from collections import OrderedDict

from .parallel_comp import assemble_graph, marked_bool


def product_comp(g_comp, g_list, save_state_names=True, save_marked_states=False):
    """
    Computes the product composition of 2 (or more) Automata, and returns
    the resulting composition as an automata.

    Parameters

    g_comp: directed igraph Graph, assumed to be empty. Used to store the output
        instead of returning a copy. This is different from the interface in the
        Automata class file, which returns a copy of the result of the
        composition.

    g_list: an iterable collection of Automata (class object) for which
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
        An error will be raised if this parameter is True, but not all Automata
        in the composition have the "marked" parameter on their vertices.

    Doesn't return anything to avoid potentially making redundant copies.
    """

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

        # Saving the index is useful in converting this OrderedDict into
        # If saving state names, need to keep track of vertices from each automata
        # that 'contributed' to this composite state in the second position
        # of the lists in g_comp_vert's values.
        if i > 1 and save_state_names:
            # If this isn't the first iteration, store the name of vertex 0
            # from the last computation as the start of this vertex name.
            # The result of the last product is stored in place of
            # the first multiplicand, g1.
            g_comp_vert[(0, 0)] = [index, list(g1.vs["name"][0]) + [0]]
        else:
            g_comp_vert[(0, 0)] = [index, [0, 0]]

        if save_marked_states:
            g_comp_vert_mark.append(marked_bool(g1, g2, (0, 0)))
        # more_states_to_check: flag that means there are new pairs in next_states_to_check
        # Gets set when new synchronized states are found --- need to check their neighbors now
        # always should be true for first iteration (creating 0,0 state)
        more_states_to_check = True

        # set next_states_to_check returns False when empty
        while next_states_to_check:
            next_states_temp = set()

            # Iterate through all new synchronized states found in last iteration, checking neighbors
            for vert_pair in next_states_to_check:
                # select edges with source at current vertex
                g1_es = g1.es(_source=vert_pair[0])
                g2_es = g2.es(_source=vert_pair[1])

                more_states_to_check = False

                common_events = all_events.intersection(g1_es["label"]).intersection(
                    g2_es["label"]
                )
                # iterate through each possible common event
                for x in common_events:
                    # might be able to do this more efficiently
                    # Currently: find index of edge labeled x at current vertex
                    a = g1_es.select(label_eq=x)[0]
                    b = g2_es.select(label_eq=x)[0]
                    new_vert_pair = (a.target, b.target)

                    # see if this is a new vertex pair
                    if new_vert_pair not in g_comp_vert:
                        # this is a new vertex pair: add it to the dict with value 'index'
                        # index just makes it easier later to map edge names from key to index
                        index = index + 1
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

                        # check if this vertex pair should get marked
                        # maybe only do this with a flag passed into fn?
                        if save_marked_states:
                            g_comp_vert_mark.append(marked_bool(g1, g2, new_vert_pair))
                        # need to check the new states' neighbors
                        next_states_temp.add(new_vert_pair)
                    more_states_to_check = True
                    new_edge_pair = ((a.source, b.source), (a.target, b.target))
                    g_comp_edges.append(new_edge_pair)
                    g_comp_edge_labels.append(x)

            next_states_to_check = next_states_temp

        assemble_graph(
            g_comp,
            g_comp_edges,
            index,
            g_comp_vert_mark,
            g_comp_edge_labels,
            g_comp_vert,
            save_state_names,
            save_marked_states,
        )
    # to iterate through list of inputs
    # g_list[i] = g_comp
