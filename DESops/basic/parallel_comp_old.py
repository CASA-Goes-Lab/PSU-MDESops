from collections import OrderedDict

import igraph as ig


def parallel_comp(
    g_comp,
    g_list,
    save_state_names=True,
    save_marked_states=False,
    common_events_i=None,
):
    # OLD version: slightly slower
    # g_list: input graphs, minimum 2
    # g_comp: output product of g1 x g2 x ... x gn
    # "label": graph attribute string for edge labels
    # "marked": graph attribute string for marked vertices
    # "name" : graph attribute string for vertex names

    # common_events: present in at least two automata in the composition
    all_common_events = set()
    if common_events_i:
        all_common_events = set(common_events_i)
    for i in range(0, len(g_list) - 1):
        all_common_events = all_common_events.union(
            set(g_list[i].es["label"]).intersection(g_list[i + 1].es["label"])
        )

    # Intermediate variables for g_comp vertices and edges
    # Storage for vertice pairs
    g_comp_vert = OrderedDict()

    # Always have (0,0) state
    # unless there are no shared events, then it's really an empty set of states?
    index = 0
    g_comp_vert[(0, 0)] = index

    g_comp_vert_mark = list()

    g_comp_edges = []
    g_comp_edge_labels = []
    next_states_to_check = {(0, 0)}

    # set the first multiplicand term

    for i in range(1, len(g_list)):
        g1 = g_list[i - 1]
        g2 = g_list[i]
        if save_marked_states:
            g_comp_vert_mark.append(marked_bool(g1, g2, (0, 0)))
        # more_states_to_check: flag that means there are new pairs in next_states_to_check
        # Gets set when new synchronized states are found --- need to check their neighbors now
        # always should be true for first iteration (creating 0,0 state)
        more_states_to_check = True

        # set next_states_to_check returns False when empty
        while next_states_to_check:
            next_states_temp = set()

            # Iterate through all new states found in last iteration
            for vert_pair in next_states_to_check:
                # select edges with source at current vertex
                g1_es = g1.es(_source=vert_pair[0])
                g2_es = g2.es(_source=vert_pair[1])

                more_states_to_check = False

                all_local_events = set(g1_es["label"]).union(g2_es["label"])
                common_events = all_common_events.intersection(
                    g1_es["label"]
                ).intersection(g2_es["label"])
                for x in all_local_events:
                    # Case 0: x is a common event (synchronous treatment)
                    if x in common_events:
                        a = g1_es.select(label_eq=x)[0]
                        b = g2_es.select(label_eq=x)[0]
                        new_vert_pair = (a.target, b.target)
                        new_edge_pair = ((a.source, b.source), (a.target, b.target))
                    # Case 1: x is private to g1, add self loop at v2
                    elif (
                        x in g1_es["label"]
                        and x not in g2_es["label"]
                        and x not in all_common_events
                    ):
                        a = g1_es.select(label_eq=x)[0]
                        new_vert_pair = (a.target, vert_pair[1])
                        new_edge_pair = (
                            (a.source, vert_pair[1]),
                            (a.target, vert_pair[1]),
                        )

                    # Case 2: x is private to g2, add self loop at v1
                    elif (
                        x in g2_es["label"]
                        and x not in g1_es["label"]
                        and x not in all_common_events
                    ):
                        b = g2_es.select(label_eq=x)[0]
                        new_vert_pair = (vert_pair[0], b.target)
                        new_edge_pair = (
                            (vert_pair[0], b.source),
                            (vert_pair[0], b.target),
                        )
                    # Case 3: if x is a common event not present on any edges sourced at this vertice
                    else:
                        continue

                    g_comp_edges.append(new_edge_pair)
                    g_comp_edge_labels.append(x)

                    # see if this is really a new vertex pair
                    if new_vert_pair not in g_comp_vert:
                        # this is a new vertex pair: add it to the dict with value 'index'
                        # index just makes it easier later to map edge names from key to index
                        index = index + 1
                        g_comp_vert[new_vert_pair] = index

                        # check if this vertex pair should get marked
                        if save_marked_states:
                            g_comp_vert_mark.append(marked_bool(g1, g2, new_vert_pair))

                        # need to check the new states' neighbors
                        next_states_temp.add(new_vert_pair)
                    more_states_to_check = True

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
        g_list[i] = g_comp
    return


def assemble_graph(
    g_comp,
    g_comp_edges,
    index,
    g_comp_vert_mark,
    g_comp_edge_labels,
    g_comp_vert,
    save_state_names,
    save_marked_states,
):
    # Assemble product_pairs, edge_pairs and edge_labels into resultant graph
    g_comp_edges_list = list()
    # substitute names of edges via dict mapping
    for vert_pair in g_comp_edges:
        source = g_comp_vert[vert_pair[0]]
        target = g_comp_vert[vert_pair[1]]
        g_comp_edges_list.append((source, target))

    # add items to new graph
    g_comp.add_vertices(index + 1)
    if save_marked_states:
        g_comp.vs["marked"] = g_comp_vert_mark
    g_comp.add_edges(g_comp_edges_list)
    g_comp.es["label"] = g_comp_edge_labels
    if save_state_names:
        g_comp.vs["name"] = list(g_comp_vert.keys())

    return


# graphs g1,g2
# vert_pair (v1, v2) vertices in g1,g2
# "marked" graph attribute string for marked vertices
def marked_bool(g1, g2, vert_pair):
    if g1.vs[int(vert_pair[0])]["marked"] and g2.vs[int(vert_pair[1])]["marked"]:
        return True
    return False


def pcomp2():
    edge_checked = {e1.index: False for e1 in G1.es for e2 in G2.es}

    Q = list()
    Q.append((0, 0))
    q = Q.pop(0)

    H = list()
    X = dict()

    while Q:
        q = Q.pop(0)
        G1_es = G1.es(_source=q[0])
        G2_es = G2.es(_source=q[1])

        pcomp_det(G1, G2, common_events, q)


def pcomp_det(G1, G2, common_events, q):
    for e1 in G1_es:
        if e1["label"] not in common_events:
            # private case to G1
            next_pairs.add(e1.target, e1["label"], q[1])
            continue
        for e2 in G2_es:
            if e1["label"] == e2["label"]:
                # synchronized case
                next_pairs.add((e1.target, e1["label"], e2.target))
    for e2 in G2.es:
        if e2["label"] in common_events:
            continue
        # private case to G2
        next_pairs.add(q[0], e2["label"], e2.target)
