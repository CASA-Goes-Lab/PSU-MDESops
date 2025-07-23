# pylint: disable=C0103

"""
Contains helpful functions used in various operations.
"""
from collections.abc import Iterable
from DESops import automata

from dd.autoref import BDD


def find_obs_contr(S, Euc=set(), Euo=set(), E=set()):
    """
    For set of graphs S, find Euc and Euo if not provided.
    This way, checks for Euc, Euo as empty sets are done
    here, rather than at the place this function gets called
    (slight convenience).
    """
    if not isinstance(S, Iterable):
        S = [S]

    if not Euc:
        find_Euc(S, Euc)
    if not Euo:
        find_Euo(S, Euo)
    if not E:
        find_E(S, E)

    return (Euc, Euo, E)


def find_Euc(S, Euc):
    """
    Check set of graphs S to find uncontrollable events.
    """
    if not S:
        return set()
    if Euc:
        return
    try:
        for graph in S:
            if "contr" not in graph.es.attributes():
                continue
            G_uc = [trans["label"] for trans in graph.es if not trans["contr"]]
            Euc.update(G_uc)
    except TypeError:
        if "contr" not in S.es.attributes():
            return
        G_uc = [trans["label"] for trans in S.es if not trans["contr"]]
        Euc.update(G_uc)


def find_Euo(S, Euo):
    """
    Check set of graphs S to find unobservable events.
    """
    if not S:
        return set()
    if Euo:
        return
    try:
        for graph in S:
            if "obs" not in graph.es.attributes():
                continue
            G_uo = [trans["label"] for trans in graph.es if not trans["obs"]]
            Euo.update(G_uo)
    except TypeError:
        if "obs" not in S.es.attributes():
            return
        G_uo = [trans["label"] for trans in S.es if not trans["obs"]]
        Euo.update(G_uo)


def find_E(S, E):
    """
    Check set of graphs S to find all events.
    """
    if not S:
        return set()
    if E:
        return
    for graph in S:
        events = [trans["label"] for trans in graph.es]
        E.update(events)


def write_transition_attributes(G, Euc=set(), Euo=set()):
    """
    Given a graph G, and set of events Euc, Euo:
    Write obs/contr attributes to transitions of G
    Only writes Euc/Euo if provided (can optionally not be provided)
    """
    contr_list = list()
    obs_list = list()
    for edge in G.es:
        if Euc:
            if edge["label"] in Euc:
                contr_list.append(False)
            else:
                contr_list.append(True)
        if Euo:
            if edge["label"] in Euo:
                obs_list.append(False)
            else:
                obs_list.append(True)
    if Euc:
        G.es["contr"] = contr_list
    if Euo:
        G.es["obs"] = obs_list


def next_state_symbolic_target(state, event, G):
    # computes next state given set of state and set of event and DFA G
    # this is a symbolic operator: state is a formula over variables s0,...,sn (source variables) and event is a formula over variables e0,...,em (event variables)
    # Normally state is a set of states and events is a set of observable events
    # returns a formula over target variables

    next_state = G.symbolic["transitions"] & state & event
    bvar = G.symbolic["states"].union(G.symbolic["events"])
    bits_states_G = len(G.symbolic["states"])-1
    if not bits_states_G: bits_states_G = 1
    bits_states_G = int(bin(bits_states_G)[2:])
    # subs = {(s[:-bits_states_G-1]+'t'+s[-bits_states_G:]): s for s in G.symbolic["states"]}

    # bvar = G.symbolic["states"].union(G.symbolic["events"])
    # subs = {"".join(["t", s[1:]]): s for s in G.symbolic["states"]}
    next_state = G.symbolic["bdd"].quantify(next_state, bvar, forall=False)
    # next_state = G.symbolic["bdd"].let(subs, next_state)
    G.symbolic["bdd"].collect_garbage()
    # print(next_state.to_expr())
    # print(list(G.symbolic["bdd"].pick_iter(next_state)))
    return next_state

def next_state_symbolic(state, event, G):
    # computes next state given set of state and set of event and DFA G
    # this is a symbolic operator: state is a formula over variables s0,...,sn (source variables) and event is a formula over variables e0,...,em (event variables)
    # Normally state is a set of states and events is a set of observable events
    # returns a formula over source variables again

    next_state = G.symbolic["transitions"] & state & event
    bvar = G.symbolic["states"].union(G.symbolic["events"])
    bits_states_G = len(G.symbolic["states"])-1
    if not bits_states_G: bits_states_G = 1
    bits_states_G = int(bin(bits_states_G)[2:])
    subs = {(s[:-bits_states_G-1]+'t'+s[-bits_states_G:]): s for s in G.symbolic["states"]}

    # bvar = G.symbolic["states"].union(G.symbolic["events"])
    # subs = {"".join(["t", s[1:]]): s for s in G.symbolic["states"]}
    next_state = G.symbolic["bdd"].quantify(next_state, bvar, forall=False)
    next_state = G.symbolic["bdd"].let(subs, next_state)
    G.symbolic["bdd"].collect_garbage()
    print(next_state.to_expr())
    print(list(G.symbolic["bdd"].pick_iter(next_state)))
    return next_state


def ureach_symbolic(state, event, G):
    # computes ureach state set given set of state and set of event and DFA G
    # this is a symbolic operator: state is a formula over variables s0,...,sn (source variables) and event is a formula over variables e0,...,em (event variables)
    # Used as state represents a set of states and event represents a set of unobservable events
    # returns a formula over source variables again

    transitions = G.symbolic["transitions"]
    bvar = G.symbolic["states"].union(G.symbolic["events"])
    subs = {"".join(["t", s[1:]]): s for s in G.symbolic["states"]}
    # print(subs)
    next_state = state
    state = None
    while next_state != state:
        state = next_state
        next_state = G.symbolic["transitions"] & state & event
        next_state = G.symbolic["bdd"].quantify(next_state, bvar, forall=False)
        next_state = G.symbolic["bdd"].let(subs, next_state)
        next_state = next_state | state
        # print(list(G.symbolic["bdd"].pick_iter(next_state)))
    G.symbolic["bdd"].collect_garbage()
    # print(next_state.to_expr())
    # print(list(G.symbolic["bdd"].pick_iter(next_state)))
    return next_state


def obs_events_symbolic(state, G):
    # computes available set of event at state set in DFA G
    # this is a symbolic operator: state is a formula over variables s0,...,sn (source variables)
    # returns a formula over events variables
    next_state = G.symbolic["transitions"] & state & ~G.symbolic["uobs"]
    tvar = {"".join(["t", s[1:]]) for s in G.symbolic["states"]}
    bvar = G.symbolic["states"].union(tvar)
    events = G.symbolic["bdd"].quantify(next_state, bvar, forall=False)
    G.symbolic["bdd"].collect_garbage()
    # print(next_state.to_expr())
    # print(list(G.symbolic["bdd"].pick_iter(events)))
    return events

def composition_symbolic(G1, G2):
    # Computes the symbolic parallel composition of G_1||G_2
    


    # With multiple automata, it is better to do all at once for BDDs

    # We will need to compute all possible private and shared events among all possible combinations
    

    # Initiate bdd
    bdd = BDD()
    # First check shared events among G1 and G2
    events_G1 = set(G1.symbolic['events_dict'].keys())
    events_G2 = set(G2.symbolic['events_dict'].keys())
    shared_events = events_G1.intersection(events_G2)
    private_G1 = events_G1.difference(shared_events)
    private_G2 = events_G2.difference(shared_events)
    state_size = 2**(len(G1.symbolic['states']))*2**(len(G2.symbolic['states']))-1
    event_size = len(events_G1.union(events_G2))-1
    if not event_size: event_size = 1


    states = set()
    events = set()
    state_names = dict()
    event_names = dict()


    G1_bdd = G1.symbolic['bdd']
    G2_bdd = G2.symbolic['bdd']

    # Creating the replacements needed for G1 s variables to G1 t variables
    bvar_G1 = G1.symbolic["states"].union(G1.symbolic["events"])
    bits_states_G1 = len(G1.symbolic["states"])-1
    if not bits_states_G1: bits_states_G1 = 1
    bits_states_G1 = int(bin(bits_states_G1)[2:])
    subs_G1 = {(s[:-bits_states_G1-1]+'t'+s[-bits_states_G1:]): s for s in G1.symbolic["states"]}
    subs_G1_t = {s:(s[:-bits_states_G1-1]+'t'+s[-bits_states_G1:]) for s in G1.symbolic["states"]}


    bvar_G2 = G2.symbolic["states"].union(G2.symbolic["events"])
    bits_states_G2 = len(G2.symbolic["states"])-1
    if not bits_states_G2: bits_states_G2 = 1
    bits_states_G2 = int(bin(bits_states_G2)[2:])
    subs_G2 = {(s[:-bits_states_G2-1]+'t'+s[-bits_states_G2:]): s for s in G2.symbolic["states"]}
    subs_G2_t = {s:(s[:-bits_states_G2-1]+'t'+s[-bits_states_G2:]) for s in G2.symbolic["states"]}

    for st in G1.symbolic['states']:
    #     # Declaring G1 variable states s
        bdd.declare(st)
    #     #Finding the last _ location - variables are named: autname_s#
    #     underscore_location = st.rfind("_")
    #     #replacing s with t in variable name
    #     # Declaring G1 variable target states t
    #     bdd.declare(st[:underscore_location+1]+"t"+ st[underscore_location+2:])
    for st in subs_G1:
    #     # Declaring G1 variable states s
        bdd.declare(st)
    #     #Finding the last _ location - variables are named: autname_s#
    #     underscore_location = st.rfind("_")
    #     #replacing s with t in variable name
    #     # Declaring G1 variable target states t
    #     bdd.declare(st[:underscore_location+1]+"t"+ st[underscore_location+2:])
    for st in G2.symbolic['states']:
    #    # Declaring G1 variable states s
        bdd.declare(st)
    #     #Finding the last _ location - variables are named: autname_s#
    #     underscore_location = st.rfind("_")
    #     #replacing s with t in variable name
    #     # Declaring G1 variable target states t
    #     bdd.declare(st[:underscore_location+1]+"t"+ st[underscore_location+2:]) 
    for st in subs_G2:
    #     # Declaring G1 variable states s
        bdd.declare(st)

    # Declaring the event variables
    for k in range(event_size.bit_length()):
            name_e = "".join(["e", str(k)])
            bdd.declare(name_e)
            events.add(name_e)   
    

    # Finding out shared events that are different variable names in G1 and G2
    for i,ev in enumerate(events_G1.union(events_G2)):
        binary = bin(i)[2:]
        binary = binary.zfill(event_size.bit_length())
        event_names[ev] = binary

    

    init_G1 = G1.symbolic["bdd"].add_expr("&".join(["!"+var for var in G1.symbolic['states']]))
    init_G2 = G2.symbolic["bdd"].add_expr("&".join(["!"+var for var in G2.symbolic['states']]))
    # Creating list of states to visit and pushing initial state both from G1 and G2 bdds
    states_to_visit = []
    visited_states = []
    states_to_visit.append((init_G1,init_G2))
    transitions = bdd.false
    # Add a while all not visited states (similar to visiting all reachable states)
    while states_to_visit:
        # removing fist item in list: st_G1 is a state in the G1 bdd and st_G2 is a state in G2 bdd
        (st_G1, st_G2) = states_to_visit.pop(0)
        visited_states.append((st_G1, st_G2))


        # add transitions for privates events G1
        for ev in private_G1:
            ev_number_G1 = G1.symbolic["events_dict"][ev]
            ev_G1 = G1_bdd.add_expr(event_bdd_formula(ev_number_G1))
            # Next state for G1 only
            nx_G1 = next_state_symbolic_target(st_G1,ev_G1,G1)
            # Changing t to s for G1
            nx_G1_in_s  = G1_bdd.let(subs_G1, nx_G1)

            # Changing s to t for G2 (same state)
            nx_G2 = st_G2
            nx_G2 = G2_bdd.let(subs_G2_t, nx_G2)
            nx_G2_in_s = nx_G2
            
            nx_G1_expr = bdd.add_expr(nx_G1.to_expr()) #Gets next state G1 as expression on t
            nx_G2_expr = bdd.add_expr(nx_G2.to_expr()) # Gets next state G1 as expression on t
            if ev not in event_names:
                binary = bin(index_event)[2:]
                binary = binary.zfill(event_size.bit_length())
                event_names[ev] = binary
                index_event += 1
                new_ev = True
            event_bin = event_names[ev]
            ev_str_expr = event_bdd_formula(event_bin)
            ev_expr = bdd.add_expr(ev_str_expr)
            # Check if target states has been visited or in the states to visit list
            if (nx_G1_in_s,nx_G2_in_s) not in visited_states and (nx_G1_in_s,nx_G2_in_s) not in states_to_visit:
                states_to_visit.append((nx_G1_in_s,nx_G2_in_s))
            trans_expr = nx_G1_expr & nx_G2_expr & ev_expr & bdd.add_expr(st_G1.to_expr()) & bdd.add_expr(st_G2.to_expr())
            transitions = transitions | trans_expr
            # print(formula.to_expr())


        # add transitions for privates events G2
        for ev in private_G2:
            # ev_G1 = G1_bdd.add_expr(event_bdd_formula(ev))
            ev_number_G2 = G2.symbolic["events_dict"][ev]
            ev_G2 = G2_bdd.add_expr(event_bdd_formula(ev_number_G2))
            # Changing s to t for G1 (same state)
            nx_G1 = st_G1
            nx_G1 = G1_bdd.let(subs_G1_t, nx_G1)
            nx_G1_in_s = nx_G1
            # Next state for G2 only
            nx_G2 = next_state_symbolic_target(st_G2,ev_G2,G2)
            # Changing t to s for G2
            nx_G2_in_s  = G2_bdd.let(subs_G2, nx_G2)
            nx_G1_expr = bdd.add_expr(nx_G1.to_expr()) #Gets next state G1 as expression on t
            nx_G2_expr = bdd.add_expr(nx_G2.to_expr()) # Gets next state G1 as expression on t
            if ev not in event_names:
                binary = bin(index_event)[2:]
                binary = binary.zfill(event_size.bit_length())
                event_names[ev] = binary
                index_event += 1
                new_ev = True
            event_bin = event_names[ev]
            ev_str_expr = event_bdd_formula(event_bin)
            ev_expr = bdd.add_expr(ev_str_expr)
            # Check if target states has been visited or in the states to visit list
            if (nx_G1_in_s,nx_G2_in_s) not in visited_states and (nx_G1_in_s,nx_G2_in_s) not in states_to_visit:
                states_to_visit.append((nx_G1_in_s,nx_G2_in_s))
            trans_expr = nx_G1_expr & nx_G2_expr & ev_expr & bdd.add_expr(st_G1.to_expr()) & bdd.add_expr(st_G2.to_expr())
            transitions = transitions | trans_expr
            # print(formula.to_expr())

        # add transitions for shared events 
        for ev in shared_events:
            ev_number_G1 = G1.symbolic["events_dict"][ev]
            ev_G1 = G1_bdd.add_expr(event_bdd_formula(ev_number_G1))
            ev_number_G2 = G2.symbolic["events_dict"][ev]
            ev_G2 = G2_bdd.add_expr(event_bdd_formula(ev))
            nx_G1 = next_state_symbolic_target(st_G1,ev_G1,G1)
            # Changing t to s for G1
            nx_G1_in_s  = G1_bdd.let(subs_G1, nx_G1)
            nx_G2 = next_state_symbolic_target(st_G2,ev_G2,G2)
            # Changing t to s for G2
            nx_G2_in_s  = G2_bdd.let(subs_G2, nx_G2)
            nx_G1_expr = bdd.add_expr(nx_G1.to_expr()) #Gets next state G1 as expression on t
            nx_G2_expr = bdd.add_expr(nx_G2.to_expr()) # Gets next state G1 as expression on t
            if ev not in event_names:
                binary = bin(index_event)[2:]
                binary = binary.zfill(event_size.bit_length())
                event_names[ev] = binary
                index_event += 1
                new_ev = True
            event_bin = event_names[ev]
            ev_str_expr = event_bdd_formula(event_bin)
            ev_expr = bdd.add_expr(ev_str_expr)
            # Check if target states has been visited or in the states to visit list
            if (nx_G1_in_s,nx_G2_in_s) not in visited_states and (nx_G1_in_s,nx_G2_in_s) not in states_to_visit:
                states_to_visit.append((nx_G1_in_s,nx_G2_in_s))
            trans_expr = nx_G1_expr & nx_G2_expr & ev_expr & bdd.add_expr(st_G1.to_expr()) & bdd.add_expr(st_G2.to_expr())
            transitions = transitions | trans_expr
            # print(formula.to_expr())
    # with open("bdd.dot", "w") as f_dot:
    bdd.add_expr(transitions.to_expr())
    bdd.collect_garbage()
    
    # Save all Boolean expr formulas for updates later if needed            
    state_names = {value: key for key, value in state_names.items()}            
    args = {
        "bdd": bdd,
        "transitions": transitions,
        # "trans_formula": transitions_formula,
        # "uctr": uctr,
        # "uctr_formula": uctr_formula,
        # "uobs": uobs,
        # "uobs_formula": uobs_formula,
        "states": (state_names, states),
        "events": (event_names, events),
        # "name": automaton_name,
    }
    # print(formula.to_expr())
    G = automata.DFA(**args)
    return G


def symbolic_observer(G):
    queue = list()
    init = G.symbolic["bdd"].add_expr("!s0 & !s1 & !s2")
    uobs = G.symbolic["uobs"]
    init = ureach_symbolic(init, uobs, G)
    queue.append(init)
    new_states = list()
    new_states.append(init)
    while queue:
        state = queue.pop(0)
        events = obs_events_symbolic(state, G)
        list_ev = list(G.symbolic["bdd"].pick_iter(events))
        for ev in list_ev:
            event = "&".join([s if ev[s] else "".join(["!", s]) for s in ev.keys()])
            event = G.symbolic["bdd"].add_expr(event)
            next_state = next_state_symbolic(state, event, G)
            next_state = ureach_symbolic(next_state, uobs, G)
            # print(list(G.symbolic["bdd"].pick_iter(next_state)))
            if next_state not in new_states:
                queue.append(next_state)
                new_states.append(next_state)
    print(new_states)



def event_bdd_formula(event):
    event = "&".join(
        [
            "".join(["e", str(i)]) if s == "1" else "".join(["!e", str(i)])
            for i, s in enumerate(event)
        ]
    )
    return event