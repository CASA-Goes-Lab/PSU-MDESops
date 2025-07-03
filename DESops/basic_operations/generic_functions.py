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


def next_state_symbolic(state, event, G):
    # computes next state given set of state and set of event and DFA G
    # this is a symbolic operator: state is a formula over variables s0,...,sn (source variables) and event is a formula over variables e0,...,em (event variables)
    # Normally state is a set of states and events is a set of observable events
    # returns a formula over source variables again

    next_state = G.symbolic["transitions"] & state & event
    bvar = G.symbolic["states"].union(G.symbolic["events"])
    subs = {"".join(["t", s[1:]]): s for s in G.symbolic["states"]}
    next_state = G.symbolic["bdd"].quantify(next_state, bvar, forall=False)
    next_state = G.symbolic["bdd"].let(subs, next_state)
    G.symbolic["bdd"].collect_garbage()
    # print(next_state.to_expr())
    # print(list(G.symbolic["bdd"].pick_iter(next_state)))
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
    
    # Initiate bdd
    bdd = BDD()
    # First check shared events among G1 and G2
    events_G1 = set(G1.symbolic['events_dict'].keys())
    events_G2 = set(G2.symbolic['events_dict'].keys())
    shared_events = events_G1.intersection(events_G2)
    state_size = 2**(len(G1.symbolic['states']))*2**(len(G2.symbolic['states']))-1
    event_size = len(events_G1.union(events_G2))-1
    
    for st in G1.symbolic['states']:
        # Declaring G1 variable states s
        bdd.declare(st)
        #Finding the last _ location - variables are named: autname_s#
        underscore_location = st.rfind("_")
        #replacing s with t in variable name
        # Declaring G1 variable target states t
        bdd.declare(st[:underscore_location+1]+"t"+ st[underscore_location+2:])
    for st in G2.symbolic['states']:
       # Declaring G1 variable states s
        bdd.declare(st)
        #Finding the last _ location - variables are named: autname_s#
        underscore_location = st.rfind("_")
        #replacing s with t in variable name
        # Declaring G1 variable target states t
        bdd.declare(st[:underscore_location+1]+"t"+ st[underscore_location+2:])    
    states = set()
    events = set()
    state_names = dict()
    event_names = dict()

    # Finding out shared events that are different variable names in G1 and G2
    for ev in shared_events:
        renames = dict()
        if G1.symbolic['events_dict'][ev] != G2.symbolic['events_dict'][ev]:
            renames['e'+G1.symbolic['events_dict'][ev]] = 'e'+G2.symbolic['events_dict'][ev]
    # for k in range(state_size.bit_length()):
    #         name_t = "".join(["s", str(k)])
    #         states.add(name_t)
    #         name_s = "".join(["t", str(k)])
    #         bdd.declare(name_s, name_t)
        
    # for k in range(event_size.bit_length()):
    #         name_e = "".join(["e", str(k)])
    #         bdd.declare(name_e)
    #         events.add(name_e)
    st1 = G1.symbolic["bdd"].add_expr("!s0")
    st2 = G2.symbolic["bdd"].add_expr("!s0")
    ev1 = G1.symbolic["bdd"].add_expr("!e0")
    ev2 = G2.symbolic["bdd"].add_expr("e0")
    nx_st1 = next_state_symbolic(st1,ev1,G1)
    nx_st2 = next_state_symbolic(st2,ev2,G2)
    # init = G.symbolic["bdd"].add_expr("!1.s0 & !2.s0")
    # transitions1 = G1.symbolic["transitions"]
    # bvar1 = G1.symbolic["states"].union(G.symbolic["events"])
    # subs1 = {"".join(["t", s[1:]]): s for s in G.symbolic["states"]}

    # transitions2 = G2.symbolic["transitions"]
    # bvar2 = G2.symbolic["states"].union(G.symbolic["events"])
    # subs2 = {"".join(["t", s[1:]]): s for s in G.symbolic["states"]}
    # print(subs)
    G = automata.DFA()
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
