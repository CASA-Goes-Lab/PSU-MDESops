import sys

import igraph as ig

from DESops.automata.DFA import DFA
from DESops.automata.PFA import PFA
from DESops.automata.event.event import Event
from DESops.automata.state.state import State


# pylint: disable=C0103
"""
Convert an 'fsm' filetype, which is used/defined by the DESUMA software,
into an igraph Graph object.
"""


def read_fsm(fsm_filename, g=None, type_aut=""):
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

    # IF WE USE READ_FSM WITHOUT CALLING FROM INIT OF DFA, PFA, OR NFA, THEN IT MUST CREATE ONE BASED ON THE FILE.
    # E.G. IF FSM HAS PROBABILITIES THEN A PFA IS CREATED. WE SHOULD NOT CREATE _Automata() ITS ABSTRACT
    # THE READ_FSM IS NOT CREATING STATE OBJECTS NEITHER EVENT OBJECTS
    g_defined = True
    if not g:
        g_defined = False
        # g = _Automata()
        g = ig.Graph(directed=True)

    state_markings = list()
    state_names = list()
    state_crit = list()
    events = set()
    events_unobs = set()
    events_unctr = set()
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
            # states.append(State(states_tuple[0]))
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
                elif len(trans_tuple) < 4:
                    sys.exit(
                        "ERROR %s in line %d:\nMissing arguments\nTransitions are in the format:\nEVENT\tTARGET_STATE\tc/uc\to/uo\tprob(optional)"
                        % (fsm_filename, i)
                    )

                if not g_defined and not type_aut:
                    if len(trans_tuple) == 5:
                        type_aut = "PFA"
                    elif (len(trans_tuple) == 4):  
                        # TODO WHEN NFA IS DEFINED THEN SET AS DFA UNTIL A NONDETERMINISTIC TRANS IS FOUND
                        type_aut = "DFA"
                if type_aut == "PFA" and len(trans_tuple) != 5:
                    sys.exit(
                        "ERROR %s in line %d:\nPFA transitions are in the format:\nEVENT\tTARGET_STATE\tc/uc\to/uo\tprob "
                        % (fsm_filename, i)
                    )
                elif type_aut == "DFA" and len(trans_tuple) != 4:
                    sys.exit(
                        "ERROR %s in line %d:\nDFA transitions are in the format:\nEVENT\tTARGET_STATE\tc/uc\to/uo"
                        % (fsm_filename, i)
                    )

                last_el = trans_tuple.pop()
                trans_tuple.append(last_el[0:-1])
                trans_labels.append(Event(trans_tuple[0]))
                events.add(Event(trans_tuple[0]))
                trans_list.append((states_tuple[0], trans_tuple[1]))
                if trans_tuple[2] == "uc":
                    events_unctr.add(Event(trans_tuple[0]))
                trans_controllable.append(trans_tuple[2])
                if trans_tuple[3] == "uo":
                    events_unobs.add(Event(trans_tuple[0]))
                trans_observable.append(trans_tuple[3])

                if type_aut == "PFA":
                    # probabilistic info encoded
                    # must be a PFA
                    type_aut = "PFA"
                    try:
                        #float(trans_tuple[4])
                        if float(trans_tuple[4]) > 1 or float(trans_tuple[4]) < 0:
                            raise ValueError
                    except ValueError:
                        sys.exit(
                            "ERROR %s in line %d:\nProbability value must be a number smaller than or equal to 1"
                            % (fsm_filename, i)
                        )
                    trans_prob.append(trans_tuple[4])
                    total = total + float(trans_tuple[4])
                    neigh.append(
                        (trans_tuple[1], Event(trans_tuple[0]), float(trans_tuple[4]))
                    )
                else:
                    neigh.append((trans_tuple[1], Event(trans_tuple[0])))
                    type_aut = "DFA"
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

    # print(events)
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

    if type_aut == "DFA":
        G = DFA(g, events_unctr, events_unobs, events)
    elif type_aut == "PFA": 
        G = PFA(g, events_unctr, events_unobs, events)
        return G

    # TODO WHEN NFA CLASS IS DEFINED

    if not g_defined:
        return G
    else:
        g = G
