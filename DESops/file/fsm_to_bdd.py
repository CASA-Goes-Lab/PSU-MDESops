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
    name_last_pos = fsm_filename.find(".fsm")
    if not fsm_filename.find('.fsm'):
        raise error.FileFormatError(
                    "ERROR %s:\ Filename does not end in .fsm"
                )
    name_init_pos = fsm_filename.rfind("/")
    if not name_init_pos:
        name_init_pos = 0
    automaton_name = fsm_filename[name_init_pos+1:name_last_pos]                                      

    state_names = dict()
    event_names = dict()
    with open(fsm_filename, "r") as f:
        # First line in fsm is # of states
        line = f.readline()
        line = line.split("\t")
        n_states = int(line[0])
        n_states = (n_states-1) # Number of bits to represent n_states
        if not n_states: n_states = 1
        n_events = int(line[1])
        n_events = (n_events-1) # Number of bits to represent n_events
        if not n_events: n_events = 1
        bdd = BDD() 
        bdd.configure(reordering=True)
        states = set()
        events = set()
        
        for k in range(n_states.bit_length()):
            name_t = "".join([automaton_name+"_s", str(k)])
            states.add(name_t)
            name_s = "".join([automaton_name+"_t", str(k)])
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
                    formula = edge_bdd_formula(source, target, event, automaton_name)
                else:
                    formula = " | ".join(
                        [formula, edge_bdd_formula(source, target, event, automaton_name)]
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
        transitions_formula = formula
        # uctr encodes the uncontrollable events
        if uctr:
            uctr_formula = uctr
            uctr = bdd.add_expr(uctr)
        else:
            uctr_formula = ""
            uctr = bdd.false
        # uobs encodes the unobservable events
        if uobs:
            uobs_formula = uobs
            uobs = bdd.add_expr(uobs)
        else:
            uobs_formula = ""
            uobs = bdd.false
    # Save all Boolean expr formulas for updates later if needed            
    state_names = {value: key for key, value in state_names.items()}            
    args = {
        "bdd": bdd,
        "transitions": transitions,
        "trans_formula": transitions_formula,
        "uctr": uctr,
        "uctr_formula": uctr_formula,
        "uobs": uobs,
        "uobs_formula": uobs_formula,
        "states": (state_names, states),
        "events": (event_names, events),
    }
    G = DFA(**args)
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
    return G


def edge_bdd_formula(source, target, event,name):
    source = "&".join(
        [
            "".join([name+"_s", str(i)]) if s == "1" else "".join(["!"+name+"_s", str(i)])
            for i, s in enumerate(source)
        ]
    )
    target = "&".join(
        [
            "".join([name+"_t", str(i)]) if s == "1" else "".join(["!"+name+"_t", str(i)])
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


