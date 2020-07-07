# pylint: disable=C0103
"""
Functions relevant to computing the product composition of Automata.
Mostly helper functions with the exception of product_comp, which
uses the helper functions.

product_comp uses assemble_graph and marked_bool from parallel_comp,
previously those functions were implemented in both product_comp and
parallel_comp but were essentially redundant.
"""
import sys
import warnings

import DESops.automata as automata


def product_comp(input_list):
    """
    G1xG2xG3x...xGN -> P - product composition of N automata -> returns automaton P
    Parameters
        input_list: an iterable collection with length > 1 of DFA.
    """
    if len(input_list) <= 1:
        sys.exit("ERROR PRODUCT COMPOSITION NEEDS AT LEAST 2 AUTOMATA TO COMPOSE")
        return
    output = automata.DFA()
    for i in range(1, len(input_list)):
        if i > 1:
            g1 = output
            output = automata.DFA()
        else:
            g1 = input_list[0]

        g2 = input_list[i]

        if len(g1.vs) == 0 or len(g2.vs) == 0:
            warnings.warn(
                "Product composition with an empty automaton-return an empty automaton"
            )
            return output

        vertice_names = list()  # list of vertex names for igraph construction
        vertice_number = dict()  # dictionary vertex_names -> vertex_id
        outgoing_list = list()  # list of outgoing lists for each vertex
        marked_list = list()  # list with vertices marking
        transition_list = list()  # list of transitions for igraph construction
        transition_label = list()  # list os transitions label for igraph construction

        # BFS queue that holds states that must be visited
        queue = list()

        # index tracks the current number of vertices in the graph
        index = 0

        # inseting initial state to the graph
        vertice_names.insert(index, (g1.vs["name"][0], g2.vs["name"][0]))
        vertice_number[(g1.vs["name"][0], g2.vs["name"][0])] = index
        marked_list.insert(index, g1.vs["marked"][0] and g2.vs["marked"][0])
        index = index + 1
        queue.append((g1.vs[0], g2.vs[0]))

        common_events = g1.events.intersection(g2.events)
        while queue:
            (v1, v2) = queue.pop(0)

            active_v1 = {e[1]: e[0] for e in v1["out"]}
            active_v2 = {e[1]: e[0] for e in v2["out"]}
            active_events = set(active_v1.keys()).union(active_v2.keys())

            outgoing_v1v2 = list()
            for e in active_events:
                if (
                    e in common_events
                    and e in active_v1.keys()
                    and e in active_v2.keys()
                ):
                    nx_v1 = g1.vs[active_v1[e]]
                    nx_v2 = g2.vs[active_v2[e]]
                    (n, t, index, m, q) = composition(
                        v1, v2, nx_v1, nx_v2, index, vertice_number
                    )
                else:
                    continue

                transition_list.append(t)
                transition_label.append(e)
                outgoing_v1v2.append((vertice_number[n], e))
                # print(index)
                if q:
                    vertice_names.insert(vertice_number[n], n)
                    marked_list.insert(vertice_number[n], m)
                    queue.append((nx_v1, nx_v2))

            outgoing_list.insert(
                vertice_number[(v1["name"], v2["name"])], outgoing_v1v2
            )

        # print(index,len(vertice_names))
        output.add_vertices(index, vertice_names)
        output.events = g1.events.union(g2.events)
        output.Euc = g1.Euc.union(g2.Euc)
        output.Euo = g1.Euo.union(g2.Euo)
        output.vs["out"] = outgoing_list
        output.vs["marked"] = marked_list
        output.add_edges(transition_list, transition_label)

    return output
    # print(vertice_names)


def composition(v1, v2, nx_v1, nx_v2, index, vertice_number):
    name = (nx_v1["name"], nx_v2["name"])
    if name in vertice_number.keys():
        transition = (vertice_number[(v1["name"], v2["name"])], vertice_number[name])
        new = False
    else:
        transition = (vertice_number[(v1["name"], v2["name"])], index)
        vertice_number[name] = index
        new = True
        index = index + 1
    marking = nx_v1["marked"] and nx_v2["marked"]
    return name, transition, index, marking, new


# def product_comp_old(
#     input_list,
#     output=None,
#     save_state_names=True,
#     save_marked_states=True,
#     save_names_as="str",
# ):
#     """
#     Computes the product composition of 2 (or more) Automata, and returns
#     the resulting composition as an automata.

#     Parameters

#     g_list: an iterable collection of Automata (class object) for which
#         the parallel composition will be computed. If saving state names,
#         this should be ordered, as it determines the order that vertex indices
#         are stored in the composition's vertex names. MUST have at least two
#         graphs (length > 1).

#     save_state_names (default True): whether vertex names should be saved
#         in the igraph Graph "name" attribute. If set to false, the attribute
#         will not be set (less memory usage). Vertex names are a list of indicies
#         from each input, in the order used by 'inputs'. For example, in the operation
#         A || B || C, a vertex name '(0,3,1)' in the output O means that state is
#         composed of vertex 0 in A, 3 in B, and 1 in C (by index, NOT vertex name).

#     save_marked_states (default False): whether states in the composition
#         should be 'marked' or not (marked if the composed states are both marked).
#         An error will be raised if this parameter is True, but not all Automata
#         in the composition have the "marked" parameter on their vertices.

#     save_names_as (default "str"):
#         If storing names, store as either pairs of old names or pairs of old vertices
#         e.g.    save_names_as=="str" --> ("state1","state2")
#                 save_names_as==any_other_str --> (1, 1)

#     Returns an Automata object.

#     """
#     output_def = True
#     if not output:
#         output_def = False
#         output = _Automata()

#     if save_marked_states:
#         if not all(["marked" in a.vs.attributes() for a in input_list]):
#             raise MissingAttributeError(
#                 'Graph does not have "marked" attribute on states'
#             )

#     # Compute intersection of events of all included graphs:
#     all_events = input_list[0].es["label"]
#     for gi in input_list[1:]:
#         all_events = set(all_events).intersection(gi.es["label"])

#     # types are objects. This doesn't show up in VSCODE but it works
#     ref_type = str if save_names_as == "str" else int

#     for i in range(1, len(input_list)):

#         # Storage for vertice pairs
#         output_vert = OrderedDict()

#         index = 0

#         output_vert_mark = list()

#         output_edges = []
#         output_edge_labels = []

#         if i > 1:
#             # After the first iteration, the first multiplicand is the
#             # result of the last product composition.
#             g1 = output
#         else:
#             g1 = input_list[0]

#         g2 = input_list[i]

#         if save_state_names and save_names_as == "str":
#             g1_names = g1.vs["name"]
#             g2_names = g2.vs["name"]
#         elif save_state_names and i > 1:
#             # Carry over names from last iter: since names were saved as indices,
#             # g1_names now has the running collection of indices
#             g1_names = g1.vs["name"]
#             g2_names = [i for i in range(g2.vcount())]
#         else:
#             g1_names = [i for i in range(g1.vcount())]
#             g2_names = [i for i in range(g2.vcount())]

#         if g1.vcount() == 0 or g2.vcount() == 0:
#             continue

#         # Saving the index is useful in converting this OrderedDict into
#         # If saving state names, need to keep track of vertices from each automata
#         # that 'contributed' to this composite state in the second position
#         # of the lists in output_vert's values.
#         new_name = list()
#         new_state_name(g1_names, g2_names, (0, 0), new_name, save_state_names, ref_type)
#         output_vert[(0, 0)] = [index, new_name, (0, 0)]

#         if save_marked_states:
#             output_vert_mark.append(marked_bool(g1, g2, (0, 0)))

#         adj = dict()
#         adj[(0, 0)] = list()
#         queue = list()
#         queue.append((0, 0))
#         while queue:
#             vert_pair = queue.pop()

#             # select edges with source at current vertex
#             g1_es = g1.vs["out"][vert_pair[0]]
#             g2_es = g2.vs["out"][vert_pair[1]]
#             g1_labels = {e[1]: e[0] for e in g1_es}
#             g2_labels = {e[1]: e[0] for e in g2_es}

#             common_events = all_events.intersection(g1_labels.keys()).intersection(
#                 g2_labels.keys()
#             )
#             # iterate through each possible common event
#             for x in common_events:
#                 # might be able to do this more efficiently
#                 # Currently: find index of edge labeled x at current vertex

#                 a = [i[0] for i in g1_es if i[1] == x][0]
#                 b = [i[0] for i in g2_es if i[1] == x][0]
#                 new_vert = (a, b)

#                 adj[vert_pair].append((new_vert, x))

#                 # see if this is a new vertex pair
#                 if new_vert not in output_vert:
#                     # this is a new vertex pair: add it to the dict with value 'index'
#                     # index just makes it easier later to map edge names from key to index
#                     index += 1

#                     new_name = list()
#                     new_state_name(
#                         g1_names,
#                         g2_names,
#                         new_vert,
#                         new_name,
#                         save_state_names,
#                         ref_type,
#                     )
#                     output_vert[new_vert] = [index, new_name, new_vert]

#                     # check if this vertex pair should get marked
#                     # maybe only do this with a flag passed into fn?
#                     if save_marked_states:
#                         output_vert_mark.append(marked_bool(g1, g2, new_vert))
#                     # need to check the new states' neighbors
#                     queue.append(new_vert)
#                     adj[new_vert] = list()

#                 new_edge_pair = (vert_pair, new_vert)
#                 output_edges.append(new_edge_pair)
#                 output_edge_labels.append(x)

#         assemble_graph(
#             output,
#             output_edges,
#             index,
#             output_vert_mark,
#             output_edge_labels,
#             output_vert,
#             save_state_names,
#             save_marked_states,
#             adj,
#         )
#     if not output_def:
#         return output

#     # else, output is saved in the existing object already
