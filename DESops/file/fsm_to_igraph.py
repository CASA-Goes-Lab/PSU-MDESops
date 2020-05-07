import sys

from DESops.automata.automata import Automata


# pylint: disable=C0103
"""
Convert an 'fsm' filetype, which is used/defined by the DESUMA software,
into an igraph Graph object.
"""


def read_fsm(fsm_filename, g=None):
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

    g_defined = True
    if not g:
        g_defined = False
        g = Automata()

    state_markings = list()
    state_names = list()
    state_crit = list()

    trans_list = list()
    trans_labels = list()
    trans_observable = list()
    trans_controllable = list()
    trans_prob = list()
    neighbors_list = list()

    with open(fsm_filename, "r") as f:
        # First line in fsm is # of states
        g.add_vertices(int(f.readline()))
        # next(f)
        i = 2
        for line in f:
            if not line or line == "\n":
                i += 1
                continue
            # Should be delimited in the line by tabs
            states_tuple = line.split("\t")
            if len(states_tuple) < 3:
                sys.exit(
                    "ERROR %s:\nMissing argument in line %d\nStates are in the format:\nSOURCE_STATE\tMARKED\t#TRANSITIONS"
                    % (fsm_filename, i)
                )
            last_el = states_tuple.pop()
            states_tuple.append(last_el[0:-1])  # REMOVING \n
            # print(states_tuple)
            state_names.append(states_tuple[0])
            state_markings.append(states_tuple[1])
            if len(states_tuple) > 3:
                state_crit.append(states_tuple[2])
            i += 1
            total = 0
            neigh = list()
            for _ in range(0, int(states_tuple[2])):
                trans_tuple = f.readline().split("\t")
                if trans_tuple == ["\n"]:
                    sys.exit(
                        "ERROR %s:\nToo many transitions at state %s"
                        % (fsm_filename, states_tuple[0])
                    )
                if len(trans_tuple) > 5:
                    sys.exit(
                        "ERROR %s in line %d:\nToo many argument\nTransitions are in the format:\nEVENT\tTARGET_STATE\tc/uc\to/uo\tprob(optional)"
                        % (fsm_filename, i)
                    )
                if len(trans_tuple) < 4:
                    sys.exit(
                        "ERROR %s in line %d:\nMissing arguments\nTransitions are in the format:\nEVENT\tTARGET_STATE\tc/uc\to/uo\tprob(optional)"
                        % (fsm_filename, i)
                    )
                last_el = trans_tuple.pop()
                trans_tuple.append(last_el[0:-1])
                trans_labels.append(trans_tuple[0])
                trans_list.append((states_tuple[0], trans_tuple[1]))
                trans_controllable.append(trans_tuple[2])
                trans_observable.append(trans_tuple[3])
                if len(trans_tuple) == 5:
                    # probabilistic info encoded
                    try:
                        float(trans_tuple[4])
                    except ValueError:
                        sys.exit(
                            "ERROR %s in line %d:\nProbability value must be a number smaller than or equal to 1"
                            % (fsm_filename, i)
                        )
                    trans_prob.append(trans_tuple[4])
                    total = total + float(trans_tuple[4])
                    neigh.append((trans_tuple[1], trans_tuple[0], int(trans_tuple[4])))
                else:
                    neigh.append((trans_tuple[1], trans_tuple[0]))
                i += 1
            neighbors_list.append(neigh)
            if total > 0 and total != 1:
                sys.exit(
                    "ERROR %s:\nTransitions in state %s do not sum up to 1"
                    % (fsm_filename, states_tuple[0])
                )

    # Construct graph
    g.vs["marked"] = bool(state_markings == "1")
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
    neighbors_list = [
        [(state_names.index(adj[0]), adj[1]) for adj in l] for l in neighbors_list
    ]
    g.vs["out"] = neighbors_list
    if trans_prob:
        g.es["prob"] = trans_prob

    if not g_defined:
        return g
