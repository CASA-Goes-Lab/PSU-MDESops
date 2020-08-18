"""
Functions relevant to computing the maximal robust supervisor for a system
afflicted with sensor deception attacks.

The primary function, construct_maxrobust(), computes the maximal supervisor
given a system modelled as an automaton represented as an Automata instance.
Uses a modified version of the VLPPO algorithm to compute control decisions.
Depending on the priority ordering used, the algorithm will produce different,
but "comparably permissive" (maximal) supervisors.

Uses material from the paper "Towards resilient supervisors against sensor
deception attacks" {better citation here}
"""

from DESops.automata.DFA import DFA
from DESops.automata.event import Event
from DESops.basic_operations import composition
from DESops.SDA.event_extensions import (
    deleted_event,
    inserted_event,
    is_deleted,
    is_inserted,
    unedited_event,
)
from DESops.supervisory_control.VLPPO.VLPPO import ext_ur_from_set


def construct_maxrobust(G, X_crit, Ea, A=None, Euo=None, Euc=None, event_ordering=None):
    """
    Construct a maximally robust supervisor for plant G

    Parameters:
    G: input Automata

    A (default None): known attack strategy (as an igraph graph); if not provided,
        assumes an all-out attack strategy (considers all possible attacks at each state).
    Ea: set of compromised events ("attackable" events).
    Euo: set of unobservable events
    Euc: set of uncontrollable events

    event_ordering: priority ordering on controllable events for the VLPPO algorithm.
        For example, the first element has the highest priority when choosing a control
        decision. See the VLPPO algorithm for more details.

    """
    if Euc is None:
        Euc = G.Euc
    if Euo is None:
        Euo = G.Euo

    if event_ordering is None:
        event_ordering = list({e["label"] for e in G.es if e["label"] not in Euc})
    Ea_i = {inserted_event(e) for e in Ea}
    Ea_d = {deleted_event(e) for e in Ea}

    # Make Ga:
    if not A:
        # If no A provided, augment Ga according to an all-out attack strategy
        Ga = augment_plant(G, Ea_i, Ea_d)
    elif A:
        # If A provided, Ga is found as Ga = A || G
        Ga = composition.parallel(A, G)

    # Construct Gm from Ga
    Gm = construct_Gm(Ga)

    states_to_remove = Gm.vs.select(name_in=X_crit)
    indices_to_remove = [v.index for v in states_to_remove]
    bad_states = Gm.compute_state_costs(indices_to_remove, Euc)

    Euo_new = Euo | Ea_i | Ea_d
    edge_labels = list()
    edge_pairs = list()
    sets_of_states = set()
    # Find Rm via bfs w/ VLPPOPC
    init_set = VLPPOCP_search(
        Gm,
        Ea,
        Euc,
        Euo_new,
        bad_states,
        event_ordering,
        edge_labels,
        edge_pairs,
        sets_of_states,
    )

    return convert_to_graph(Gm, edge_labels, edge_pairs, sets_of_states, init_set)


def VLPPOCP_search(
    G, Ea, Euc, Euo, bad_states, event_ordering, edge_labels, edge_pairs, sets_of_states
):
    """
    Handles search of states & executing the VLPPOCP algorithm.
    """

    # Smallest control pattern from Ca w/ condition for events in Ea_e
    sm_cont_pat = {inserted_event(e) for e in Euc if e in Ea}
    sm_cont_pat.update({deleted_event(e) for e in Euc if e in Ea})
    sm_cont_pat.update(Euc)

    Q = list()
    init_set = frozenset({0})
    # ACT: 'global' var that stores current issued control decision
    ACT = set()
    # NS: 'global' var that stores current state estimate
    NS = set()

    # cache ext ureach computations:
    eur_dict = dict()

    # Initialize ACT & PS w/ 'None' event
    [ACT, PS] = VLPPOCP(
        G,
        init_set,
        None,
        Euc,
        Euo,
        event_ordering,
        sm_cont_pat,
        bad_states,
        Ea,
        eur_dict,
    )
    init_set = PS
    Q.append((ACT, PS))
    sets_of_states.add(frozenset(PS))

    if not PS:
        return
    while Q:
        # Iterate VLPPOCP computations to build supervisor
        (ACT, PS) = Q.pop(0)
        # E_set = set(G.es(_source_in = PS)["label"])
        E_set = set(t[1] for v in PS for t in G.vs[v]["out"])
        for e in ACT:
            NS = PS
            if e not in Euo and e in E_set:
                # Only check observable & valid neighbors (in active event set of PS) for more VLPPOCP computations
                [ACT_new, NS] = VLPPOCP(
                    G,
                    PS,
                    e,
                    Euc,
                    Euo,
                    event_ordering,
                    sm_cont_pat,
                    bad_states,
                    Ea,
                    eur_dict,
                )
                if NS not in sets_of_states:
                    sets_of_states.add(frozenset(NS))
                    Q.append((ACT_new, NS))
            # Add transitions for all e in ACT; if e not in Euo and E_set, edge will be a self-loop (NS = PS)
            edge_labels.append(e)
            edge_pairs.append((frozenset(PS), frozenset(NS)))
    return frozenset(init_set)


def VLPPOCP(G, PS, e, Euc, Euo, event_ordering, sm_cont_pat, bad_states, Ea, eur_dict):
    """
    Modified VLPPOCP algorithm (same steps, but control_actions() is slightly different).

    Parameters:
    G: igraph graph for the system model
    PS: present state estimate
    e: last event
    Euc, Euo: sets of uncontrollable/unobservable events
    event_ordering: priority ordering on controllable events for the VLPPO algorithm.
        For example, the first element has the highest priority when choosing a control
        decision. See the VLPPO algorithm for more details.
    sm_cont_pat: smallest control pattern, defined in section IV part B 'Computing robust
        supervisor'.
    bad_states: set of infinite cost states, precomputed.
    Ea: set of compromised/attackable events
    """
    # Same as the general VLPPO algorithm:
    NS = get_N(G, PS, e, Euo)

    ACT = control_actions(
        G, NS, event_ordering.copy(), sm_cont_pat, bad_states, Euo, Ea, eur_dict
    )

    PS_new = G.UR.from_set(NS, frozenset(ACT.intersection(Euo)), freeze_result=True)
    return [ACT, PS_new]


def control_actions(G, S, Elist, sm_cont_pat, bad_states, Euo, Ea, eur_dict):
    """
    Modified version of control_actions function w/ smallest control pattern
    """
    ACT = sm_cont_pat.copy()
    # Pt initialized from 0 instead of 1
    Pt = 0
    while Elist:
        if Pt > len(Elist) - 1:
            return ACT.union(Elist)
        e = Elist[Pt]
        if e in Ea:
            gamma = sm_cont_pat | {e, inserted_event(e), deleted_event(e)}
        else:
            gamma = sm_cont_pat | {e}

        ACT_U_GAMMA = ACT.union(gamma)
        UO_ACT_U_GAMMA = ACT_U_GAMMA.intersection(Euo)
        UO_ACT = frozenset(ACT.intersection(Euo))
        x_set_gamma = G.UR.from_set(S, frozenset(UO_ACT_U_GAMMA), freeze_result=True)
        ACT_EUR_w_gamma = ext_ur_from_set(x_set_gamma, G, ACT | gamma, Euo, eur_dict)

        x_set = G.UR.from_set(S, UO_ACT, freeze_result=True)
        ACT_EUR = ext_ur_from_set(x_set, G, ACT, Euo, eur_dict)

        if ACT_EUR == ACT_EUR_w_gamma:
            Pt += 1
            continue

        flag = False
        if any(True if x in bad_states else False for x in ACT_EUR_w_gamma):
            # Check if V(x) = inf --> found as bad_states in precompute step
            # bad_states are indicies of G (stored in the names of assoc. states of Gspec w/ names: (G.vs["name"][i],i)
            # Remove all elements of gamma from Elist
            Elist = [el for el in Elist if el not in gamma]
            continue
        ACT.update(gamma)
        Elist = [t for t in Elist if t not in gamma]
        Pt = 0
    return ACT


def construct_Gm(Ga):
    """
    Create the modified system model Gm
    """
    new_trans = list()
    new_labels = list()
    new_states = list()
    trans_to_delete = list()
    trans_tuple = list()

    Gm = DFA(Ga)
    for e in Ga.es:
        # Track insertions w/ intermediate state between source & target
        if is_inserted(e["label"]):
            trans_to_delete.append(e.index)
            new_trans.append((e.source, Gm.vcount() + len(new_states)))
            new_labels.append(e["label"])
            new_states.append((e.source, e["label"], Gm.vcount() + len(new_states)))

    # For all new vertices, add the next transition back to the original target
    for t in new_states:
        new_trans.append((t[2], t[0]))
        new_labels.append(unedited_event(t[1]))

    Gm.delete_edges(trans_to_delete)
    Gm.add_vertices(len(new_states), new_states)
    Gm.add_edges(new_trans, new_labels)
    Gm.generate_out()
    return Gm


def augment_plant(G, Ea_i, Ea_d):
    """
    Modify Ga: G w/ added events according to def. III.1
    """
    Ga = DFA(G)
    new_trans = list()
    new_labels = list()
    for x in range(G.vcount()):
        for e in Ea_i:
            new_trans.append((x, x))
            new_labels.append(e)
        for e in Ea_d:
            # Check if d_G(x,M(e))!
            trans_def = [t for t in G.vs["out"][x] if t[1] == e]
            for t in G.vs["out"][x]:
                if t[1] == unedited_event(e):
                    # M(e) is defined in original plant:
                    new_trans.append((x, t[0]))
                    new_labels.append(e)
                    continue

    Ga.add_edges(new_trans, new_labels)
    return Ga


def get_N(G, S, event, Euo=None):
    """
    NX function from VLPPO algorithm.
    """
    if event is None:
        return S
    return frozenset(t[0] for v in S for t in G.vs[v]["out"] if t[1] == event)


def convert_to_graph(G, edge_labels, edge_pairs, sets_of_states, init_set):
    """
    Converts the supervisor into an igraph graph Rm.
    """
    Rm = DFA()
    Rm.add_vertices(len(sets_of_states))

    sets_of_states.remove(init_set)
    states_dict = {s: i for i, s in enumerate(sets_of_states, 1)}
    states_dict[init_set] = 0

    new_edge_pairs = [(states_dict[p[0]], states_dict[p[1]]) for p in edge_pairs]

    # Below required to name states (currently just using generic names as the examples
    # in the paper used generic state names. Makes it hard to read state names).

    # Replace indices in sets (in sets_of_states) w/ their respective names in G
    # sets_of_states = {frozenset({G.vs["name"][i] if not isinstance(i,Event) else G.vs["name"][i].tuple() for i in s}) for s in sets_of_states}
    # init_set = frozenset({G.vs["name"][i] for i in init_set})

    # vs_names = list()
    # vs_names.append(init_set)
    # vs_names.extend(sets_of_states)

    # Rm.vs["name"] = vs_names
    Rm.add_edges(new_edge_pairs, edge_labels)
    Rm.vs["name"] = [i for i in range(0, Rm.vcount())]
    Rm.generate_out()
    return Rm
