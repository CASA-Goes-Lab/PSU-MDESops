# pylint: disable=C0103
"""
Convert an 'fsm' filetype, which is used/defined by the DESUMA software,
into an igraph Graph object.
"""


def fsm_to_igraph(fsm_filename, g):
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
        occuring for a given state pair & event label. This is NOT included in the 'fsm'
        file format from DESUMA, but if the probability is included as a tab-separated
        value at the end of the line for a transition, it will be read as the probability
        for that transition.

        For example: in state 1, there is a controllable-unobservable transition
        to state 2 with label 'a' and probability p=0.5
        > <'fsm_file.fsm'>
        > 1   0   1
        > 0   2   c   uo   0.5
        > ...
    """

    state_markings = list()
    state_names = list()
    state_crit = list()

    trans_list = list()
    trans_labels = list()
    trans_observable = list()
    trans_controllable = list()
    trans_prob = list()

    with open(fsm_filename, "r") as f:
        # First line in fsm is # of states
        g.add_vertices(int(f.readline()))
        for line in f:
            if not line or line == "\n":
                continue
            # Should be delimited in the line by tabs
            states_tuple = line.split("\t")
            last_el = states_tuple.pop()
            states_tuple.append(last_el[0:-1])
            state_names.append(states_tuple[0])
            state_markings.append(states_tuple[1])
            if len(states_tuple) > 3:
                state_crit.append(states_tuple[2])
            for _ in range(0, int(states_tuple[2])):
                trans_tuple = f.readline().split("\t")
                last_el = trans_tuple.pop()
                trans_tuple.append(last_el[0:-1])
                trans_labels.append(trans_tuple[0])
                trans_list.append((states_tuple[0], trans_tuple[1]))
                trans_controllable.append(trans_tuple[2])
                trans_observable.append(trans_tuple[3])
                if len(trans_tuple) == 5:
                    # probabilistic info encoded
                    trans_prob.append(trans_tuple[4])

    # Construct graph
    g.vs["marked"] = [m == "1" for m in state_markings]
    if state_crit:
        g.vs["crit"] = state_crit
    g.vs["name"] = state_names
    trans_list_int_names = list()
    for pair in trans_list:
        source = state_names.index(pair[0])
        target = state_names.index(pair[1])
        trans_list_int_names.append((source, target))
    g.add_edges(trans_list_int_names)
    g.es["label"] = trans_labels
    trans_observable_bool = [x == "o" for x in trans_observable]
    g.es["obs"] = trans_observable_bool
    trans_controllable_bool = [x == "c" for x in trans_controllable]
    g.es["contr"] = trans_controllable_bool

    if trans_prob:
        g.es["prob"] = trans_prob
