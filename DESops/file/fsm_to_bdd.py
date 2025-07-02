import ast

import igraph as ig
from dd.autoref import BDD

from DESops import error
from DESops.automata.DFA import DFA
from DESops.automata.event import Event


def read_fsm_to_bdd(fsm_filename):
    """
		fsm_filename: filename to write output to, e.g. "name_text.fsm"
		g: igraph Graph object to read from (an Automata instance would work as well).

		Keyword attributes used in this package (for igraph Graph edge/vert sequences):
		"name": vertexseq label to refer to state names
		"marked": vertexseq label to refer to marked attr
		"label": edgeseq label to refer to label of transition
		"obs": edgeseq label to refer to transition observability attr
		"contr": edgeseq label to refer to transition controllability attr
		"""
    state_names = dict()
    event_names = dict()
    with open(fsm_filename, "r") as f:
        # First line in fsm is # of states
        line = f.readline()
        line = line.split("\t")
        n_states = int(line[0])
        n_events = int(line[1])
        bdd = BDD()
        bdd.configure(reordering=True)
        states = set()
        events = set()
        for k in range(n_states.bit_length()):
            name_t = "".join(["s", str(k)])
            states.add(name_t)
            name_s = "".join(["t", str(k)])
            bdd.declare(name_s, name_t)
        for k in range(n_events.bit_length()):
            name_e = "".join(["e", str(k)])
            bdd.declare(name_e)
            events.add(name_e)
        # next(f)
        index = 0
        index_event = 0
        i = 2
        formula = ""
        uctr = ""
        uobs = ""
        for line in f:
            if not line or line == "\n":
                i += 1
                continue
            # Should be delimited in the line by tabs
            states_tuple = line.split("\t")
            if len(states_tuple) < 3:
                raise error.FileFormatError(
                    "ERROR %s:\nMissing argument in line %d\nStates are in the format:\nSOURCE_STATE\tMARKED\t#TRANSITIONS"
                    % (fsm_filename, i)
                )
            last_el = states_tuple.pop()
            states_tuple.append(last_el[0:-1])  # REMOVING \n
            # print(states_tuple)
            name = states_tuple[0]
            states_tuple[0] = ast.literal_eval(name) if name[0] == "(" else name
            if states_tuple[0] not in state_names:
                binary = bin(index)[2:]
                binary = binary.zfill(n_states.bit_length())
                state_names[states_tuple[0]] = binary
                index += 1
            source = state_names[states_tuple[0]]
            for _ in range(0, int(states_tuple[2])):
                trans_tuple = f.readline().split("\t")
                if trans_tuple == ["\n"]:
                    raise error.FileFormatError(
                        "ERROR %s:\nToo many transitions at state %s"
                        % (fsm_filename, states_tuple[0])
                    )
                if len(trans_tuple) > 5:
                    raise error.FileFormatError(
                        "ERROR %s in line %d:\nToo many argument\nTransitions are in the format:\nEVENT\tTARGET_STATE\tc/uc\to/uo\tprob(optional)"
                        % (fsm_filename, i)
                    )
                elif len(trans_tuple) < 4:
                    raise error.FileFormatError(
                        "ERROR %s in line %d:\nMissing arguments\nTransitions are in the format:\nEVENT\tTARGET_STATE\tc/uc\to/uo\tprob(optional)"
                        % (fsm_filename, i)
                    )
                last_el = trans_tuple.pop()
                trans_tuple.append(last_el[0:-1])
                t_name = trans_tuple[1]
                trans_tuple[1] = (
                    ast.literal_eval(t_name) if t_name[0] == "(" else t_name
                )
                if trans_tuple[1] not in state_names:
                    binary = bin(index)[2:]
                    binary = binary.zfill(n_states.bit_length())
                    state_names[trans_tuple[1]] = binary
                    index += 1
                target = state_names[trans_tuple[1]]
                new_ev = False
                if trans_tuple[0] not in event_names:
                    binary = bin(index_event)[2:]
                    binary = binary.zfill(n_events.bit_length())
                    event_names[trans_tuple[0]] = binary
                    index_event += 1
                    new_ev = True
                event = event_names[trans_tuple[0]]
                if formula == "":
                    formula = edge_bdd_formula(source, target, event)
                else:
                    formula = " | ".join(
                        [formula, edge_bdd_formula(source, target, event)]
                    )
                # trans_list.append((states_tuple[0], trans_tuple[1]))
                if trans_tuple[2] == "uc" and new_ev:
                    if uctr == "":
                        uctr = event_bdd_formula(event)
                    else:
                        uctr = " | ".join([uctr, event_bdd_formula(event)])
                if trans_tuple[3] == "uo" and new_ev:
                    if uobs == "":
                        uobs = event_bdd_formula(event)
                    else:
                        uobs = " | ".join([uobs, event_bdd_formula(event)])

                    # events_unctr.add(Event(trans_tuple[0]))
                # trans_controllable.append(trans_tuple[2])
                # if trans_tuple[3] == "uo":
                # 	events_unobs.add(Event(trans_tuple[0]))
                # trans_observable.append(trans_tuple[3])

        # transitions encodes the transition function of the DFA
        # to find all transitions from a specific source state
        # 		1- select source - source = dict(s0=False, s1=False) (assuming two bdd variable)
        # 		2- replace variables in the transition formula - v = bdd.let(source,transitions
        # 		3- get all possible targets - t = list(bdd.pick_iter(v))
        # 	t lists of all possible (target, event) pair such that (source,event,target) is in the transition function of the DFA
        transitions = bdd.add_expr(formula)
        # uctr encodes the uncontrollable events
        if uctr:
            uctr = bdd.add_expr(uctr)
        else:
            uctr = bdd.false
        # uobs encodes the unobservable events
        if uobs:
            uobs = bdd.add_expr(uobs)
        else:
            uobs = bdd.false
    args = {
        "bdd": bdd,
        "transitions": transitions,
        "uctr": uctr,
        "uobs": uobs,
        "states": (state_names, states),
        "events": (event_names, events),
    }
    G = DFA(**args)
    # A DFA CLASS MUST HAVE A BDD OPTIONAL
    return G
    # target = bdd.add_expr('t0 & !t1')
    # target = dict(t0= True,t1 = False)
    # source = dict(s0=False, s1=False,e0=True)
    # v = bdd.let(source,transitions)
    # print(bdd.pick(v))
    # ev=dict(e0=False)
    # v=bdd.let(ev,uctr)
    # print(bdd.pick(v))
    # bdd.collect_garbage()
    # print(len(bdd))
    # print(bdd.vars)


def edge_bdd_formula(source, target, event):
    source = "&".join(
        [
            "".join(["s", str(i)]) if s == "1" else "".join(["!s", str(i)])
            for i, s in enumerate(source)
        ]
    )
    target = "&".join(
        [
            "".join(["t", str(i)]) if s == "1" else "".join(["!t", str(i)])
            for i, s in enumerate(target)
        ]
    )
    event = "&".join(
        [
            "".join(["e", str(i)]) if s == "1" else "".join(["!e", str(i)])
            for i, s in enumerate(event)
        ]
    )
    formula = "&".join([source, target, event])
    return formula


def event_bdd_formula(event):
    event = "&".join(
        [
            "".join(["e", str(i)]) if s == "1" else "".join(["!e", str(i)])
            for i, s in enumerate(event)
        ]
    )
    return event
