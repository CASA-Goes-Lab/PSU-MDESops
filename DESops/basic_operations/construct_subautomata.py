# pylint: disable=C0103
"""
Functions relevant to the process of constructing Automata wherein one
is a strict subautomaton of the other.
"""
from DESops.basic_operations.product_comp import product_comp


def construct_subautomata(
    H_given, G_given, H, G, find_H=True, save_state_markings=False
):
    """
    Given H_given, G_given, constructs H & G s.t. H is a strict subautomata of G
    H, G do NOT have proper edge attributes for observability/controllability
    Optional paramater find_H: If false, don't extract H from G; default true
    Returns the index of the dead state

    1. Build A (H with {dead} state added, and transitions to dead/self loops at dead
    2. Calculate AG := A x G
    3. (i) Obtain G~ from AG by marking states iff 2nd state component is marked in G
        (ii) Obtain H~ by taking the largest subautomata of AG where the first state
            component isn't {dead}. Delete from H~ all states where first component
            is {dead}. Mark states in H~ iff first component marked in H.
    """

    # Define E = E(H) U E(G) event labels in either H or G
    E = set(H_given.es["label"]).union(G_given.es["label"])
    add_transitions_to_dead(H_given, E)

    # Find G := H_given_with_dead x G
    # (This G does not have proper markings yet)
    product_comp([H_given, G_given], G, save_state_names=True, save_names_as="int")
    dead_state_index = H_given.vcount() - 1

    if find_H:
        # Find H := G w/o dead states
        delete_dead_states(G, H, dead_state_index)

    if save_state_markings:
        # Add markings to H
        if find_H and "marked" in H_given.vs.attributes():
            marked_labels = [False] * H.vcount()
            for state in H.vs:
                if H_given.vs[state["name"][0]]["marked"]:
                    marked_labels[state.index] = True
            H.vs["marked"] = marked_labels

        # Add markings to G
        if "marked" in G_given.vs.attributes():
            marked_labels = [False] * G.vcount()
            for state in G.vs:
                g_vert = state["name"][1]
                if G_given.vs[g_vert]["marked"]:
                    marked_labels[state.index] = True
            G.vs["marked"] = marked_labels

    G.Euc = G_given.Euc.union(H_given.Euc)
    G.Euo = G_given.Euo.union(H_given.Euo)
    return dead_state_index


def add_transitions_to_dead(H_given, E):
    """
    Add transitions from each state in H_given to a new 'dead' state
    for each event in E that is not present in the active event set
    of that state.
    """
    trans_to_dead_pairs = list()
    trans_to_dead_labels = list()
    # Add edges to dead state
    t = H_given.vs["out"]
    out = []
    dead_index = H_given.vcount()

    H_given.add_vertex("dead")
    H_given.vs[dead_index].update_attributes({"out" : []})
    
    for state in H_given.vs():
        neighbors = []
        active_event_set = {v[1] for v in H_given.vs["out"][state.index]}
        for label in E:
            if label not in active_event_set:
                # Transition from current state index to "dead" state index (last state added)
                trans_to_dead_pairs.append((state.index, H_given.vcount() - 1))
                trans_to_dead_labels.append(label)
                neighbors.append((dead_index, label))
        out.append(neighbors)
    out.append([])
    out = [[*old, *new] for old, new in zip(H_given.vs["out"], out)]
    H_given.vs["out"] = out
    # Add transitions to H_given:
    H_given.add_edges(trans_to_dead_pairs, trans_to_dead_labels)


def delete_dead_states(G, H, dead_state_index):
    """
    Compose H as G w/o dead states
    """
    states_to_delete = [
        state.index for state in G.vs if state["name"][0] == dead_state_index
    ]
    # H is a deepcopy of G
    H.add_vertices(G.vcount())
    H.vs["name"] = G.vs["name"]
    H.add_edges((e.tuple for e in G.es), G.es["label"])
    H.delete_vertices(states_to_delete)
    return H
