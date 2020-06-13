# pylint: disable=C0103
"""
Functions relevant to computing the parallel composition of Automata.
Mostly helper functions with the exception of parallel_comp, which
uses the helper functions.

assemble_graph and marked_bool used in product_comp
"""

import sys
from collections import OrderedDict
from collections.abc import Iterable

import DESops.automata as automata


def parallel_comp(
    input_list,
    output=None,
    save_state_names=True,
    save_marked_states=False,
    common_events_i=None,
    save_names_as="str",
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
    """
    if not input_list:
        return
    output_defined = True
    if not output:
        output_defined = False
        if any(isinstance(g, automata.PFA) for g in input_list):
            output = automata.NFA()  # warn
            import warnings

            warnings.warn(
                "P-comp returning a DFA. Probabilistic information will be lost if type PFA."
            )
        elif any(isinstance(g, automata.NFA) for g in input_list):
            output = automata.NFA()
        else:
            output = automata.DFA()

    # types are objects. This doesn't show up in VSCODE but it works
    ref_type = str if save_names_as == "str" else int

    for i in range(1, len(input_list)):

        if i > 1:
            g1 = output
            output = automata.DFA()
        else:
            g1 = input_list[0]

        g2 = input_list[i]

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
        private_g1 = g1.events.difference(g2.events)
        private_g2 = g2.events.difference(g1.events)
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
                elif e in private_g1:
                    nx_v1 = g1.vs[active_v1[e]]
                    nx_v2 = v2
                    (n, t, index, m, q) = composition(
                        v1, v2, nx_v1, nx_v2, index, vertice_number
                    )
                elif e in private_g2:
                    nx_v1 = v1
                    nx_v2 = g2.vs[active_v2[e]]
                    (n, t, index, m, q) = composition(
                        v1, v2, nx_v1, nx_v2, index, vertice_number
                    )
                else:
                    continue

                # print(v1["name"],v2["name"],n,e)
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


# OLD CODE BY JACK
#     if save_state_names and save_names_as == "str":
#         g1_names = g1.vs["name"]
#         g2_names = g2.vs["name"]
#     elif save_state_names and i > 1:
#         # Carry over names from last iter: since names were saved as indices,
#         # g1_names now has the running collection of indices
#         g1_names = g1.vs["name"]
#         g2_names = [i for i in range(g2.vcount())]
#     else:
#         g1_names = [i for i in range(g1.vcount())]
#         g2_names = [i for i in range(g2.vcount())]

#     if g1.vcount() == 0 or g2.vcount() == 0:
#         continue
#     # If saving state names, need to keep track of vertices from each automata
#     # that 'contributed' to this composite state
#     new_name = list()
#     new_state_name(g1_names, g2_names, (0, 0), new_name, save_state_names, ref_type)
#     output_vert[(0, 0)] = [index, new_name, (0, 0)]

#     if save_marked_states:
#         output_vert_mark.append(marked_bool(g1, g2, (0, 0)))

#     adj = dict()

#     queue = list()
#     queue.append((0, 0))

#     while queue:
#         vert_pair = queue.pop()

#         # select edges with source at current vertex
#         new_vert_pairs = list()
#         new_edge_pairs = list()
#         new_edge_labels = list()
#         adj_vert = list()

#         g1_es = g1.vs["out"][vert_pair[0]]
#         g2_es = g2.vs["out"][vert_pair[1]]

#         # THIS ONLY WORKS WITH DFAS
#         # SHOULD NOT USE DICT IF WANT TO EXTEND TO NFAs
#         # FOR NFAs should be different: returning to DFAs case only
#         g1_labels = {e[1]: e[0] for e in g1_es}
#         g2_labels = {e[1]: e[0] for e in g2_es}
#         l_set = set(g1_labels.keys()).union(g2_labels.keys())
#         # print(l_set)
#         # pcomp_det checks for set membership in g1_, g2_labels
#         # Maybe faster to store membership when computing set unions?
#         # (Significant time is spent in pcomp_det)
#         for x in l_set:
#             pcomp_det(
#                 x,
#                 vert_pair,
#                 g1_labels,
#                 g2_labels,
#                 all_common_events,
#                 new_vert_pairs,
#                 new_edge_pairs,
#                 new_edge_labels,
#                 adj_vert,
#             )
#             # print(adj_vert)

#         # new : (new vert pair, new edge pair, new edge label)
#         adj[vert_pair] = adj_vert
#         output_edges.extend([new_edge_pair for new_edge_pair in new_edge_pairs])
#         output_edge_labels.extend(
#             [new_edge_label for new_edge_label in new_edge_labels]
#         )

#         # see if this is a new vertex pair
#         for v in new_vert_pairs:
#             if v not in output_vert:
#                 index += 1
#                 new_name = list()
#                 new_state_name(
#                     g1_names, g2_names, v, new_name, save_state_names, ref_type
#                 )
#                 output_vert[v] = [index, new_name, v]

#                 queue.append(v)

#     if save_marked_states:
#         output_vert_mark = [marked_bool(g1, g2, v[2]) for v in output_vert.values()]

#     assemble_graph(
#         output,
#         output_edges,
#         index,
#         output_vert_mark,
#         output_edge_labels,
#         output_vert,
#         save_state_names,
#         save_marked_states,
#         adj,
#     )

#     # to iterate through list of inputs
#     # input_list[i] = output

# # update events attribute
# output.events = set(all_common_events)
# if not output_defined:
#     return output


def new_state_name(g1_names, g2_names, v, new_name, save_state_names, ref_type):
    v1 = v[0]
    v2 = v[1]

    if save_state_names:
        if isinstance(g1_names[v1], ref_type) and isinstance(g2_names[v2], ref_type):
            new_name.append(g1_names[v1])
            new_name.append(g2_names[v2])

        elif isinstance(g2_names[v2], ref_type):
            new_name.extend(g1_names[v1])
            new_name.append(g2_names[v2])

        elif isinstance(g1_names[v1], ref_type):
            new_name.append(g1_names[v1])
            new_name.extend(g2_names[v2])

        else:
            new_name.extend(g1_names[v1])
            new_name.extend(g2_names[v2])


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
    # print(x)
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
