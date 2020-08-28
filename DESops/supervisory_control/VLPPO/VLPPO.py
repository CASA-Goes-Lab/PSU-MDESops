"""
Functions related to computing a maximal controllable and observable supervisor
for a given system & specification automaton.

offline_VLPPO(), implemented here, is used in an interface to Automata objects
in the Automata class declaration (Automata/Automata.py)
"""

import copy

import igraph as ig

from DESops.automata.DFA import DFA
from DESops.automata.event import Event
from DESops.basic_operations import composition


def offline_VLPPO(
    plant,
    spec,
    Euc=None,
    Euo=None,
    event_ordering=None,
    preprocess=True,
    supervisor=None,
):
    """
    Returns an Automata object which is a maximal controllable & observable supervisor of
        the given system and specification Automata.

    Parameters:
    plant: Automata representing the plant/system.
    spec: Either an automata representing the specification or a set of critical states
        (names of states in plant)

    event_ordering: optionally provide a priority list of controllable events;
        if not provided, an arbitrary ordering will be used (the set of controllable
        events will be found as a python set(), and then casting the set into a list()).

    X_crit (default None): if the specification only intends to disable states in the plant,
        those vertices can be provided directly (slightly more efficient, as the specification
        associated with a list of bad states would already be a subautomaton of the system,
        skipping the step in offline_VLPPO_i where the system & spec are constructed again as
        subautomata). Can be provided as a list or iterable of vertice names.

    construct_SA (default True): flag to construct an equivalent G', H' from the system G and
        specification H such that H' is a subautomata of G'. Set to False if the input spec is
        already a subautomata of the input system or X_crit was provided (the specification
        is just a disabling of certain states in the system).

    The sets of uncontrollable and unobservable events, Euc and Euo respectively,
    are found as the unions of the Euc & Euo sets in the plant & specification.
    """

    if plant.vcount() == 0:
        return DFA()
    if not Euo:
        if isinstance(spec, DFA):
            Euo = plant.Euo.union(spec.Euo)
        else:
            Euo = plant.Euo
        Euo = frozenset(Euo)
    elif isinstance(Euo, list):
        Euo = frozenset(Euo)

    if not Euc:
        if isinstance(spec, DFA):
            Euc = plant.Euc.union(spec.Euc)
        else:
            Euc = plant.Euc

    elif isinstance(Euc, list):
        Euc = set(Euc)

    if not isinstance(spec, DFA) and not isinstance(spec, set):
        raise TypeError(
            "Expected spec to be type DFA or set (of names of critical states). Got {}".format(
                type(spec)
            )
        )

    if event_ordering and not isinstance(event_ordering, list):
        try:
            event_ordering = [i for i in event_ordering]
        except:
            raise ValueError("Could not convert event_ordering to list().")
    if event_ordering:
        event_ordering = [
            i if isinstance(i, Event) else Event(i) for i in event_ordering
        ]
        event_ordering = [i for i in event_ordering if i not in Euc]

    if isinstance(spec, DFA):
        _, plant_pp = composition.strict_subautomata(spec, plant, skip_H_tilde=True)

        X_crit = set(i.index for i in plant_pp.vs if i["name"][0] == "dead")

    else:
        # X_crit provided; specification is plant w/o X_crit states
        plant_pp = plant
        X_crit = set(i.index for i in plant_pp.vs if i["name"] in spec)

    # Accumlate sets of states for final control policy in sets_of_states var
    sets_of_states = set()

    bad_states = plant_pp.compute_state_costs(X_crit, Euc)
    # State is illegal if in bad_states

    # if initial state is in bad_states, there is no solution:

    if 0 in bad_states:
        # return empty DFA
        empty_sol = DFA()
        return empty_sol

    if not event_ordering:
        # "unspecified" event_ordering follows nondeterministic set ordering
        event_ordering = [label for label in plant_pp.events if label not in Euc]

    edge_labels, edge_pairs = list(), list()

    eur_dict = dict()

    # Compute next set of present states PS, and control policy ACT
    ACT, PS = VLPPO(
        plant_pp,
        Euc,
        Euo,
        frozenset(0 for _ in range(1)),
        None,
        bad_states,
        event_ordering,
        eur_dict,
    )
    init_set = PS

    supervisor_def = True
    if not supervisor:
        supervisor_def = False
        supervisor = DFA()

    # If the first VLPPO computation found a possible next set of states, use bfs to traverse all sets of states

    if PS:
        sets_of_states.add(init_set)
        search_VLPPO(
            plant_pp,
            Euc,
            Euo,
            PS,
            bad_states,
            sets_of_states,
            edge_labels,
            edge_pairs,
            ACT,
            event_ordering,
            eur_dict,
        )
        # Create graph P using sets_of_states, edge_labels & edge_pairs
        # modifies sets_of_states

        convert_to_graph(
            supervisor, sets_of_states, edge_pairs, edge_labels, Euc, Euo, init_set
        )

    # Otherwise, P will be an empty graph?

    supervisor.Euc.update(Euc)
    supervisor.Euo.update(Euo)

    supervisor.events = plant.events.copy()

    if not supervisor_def:
        return supervisor


def search_VLPPO(
    G,
    Euc,
    Euo,
    PS,
    bad_states,
    sets_of_states,
    edge_labels,
    edge_pairs,
    ACT,
    event_ordering,
    eur_dict,
):
    """
    Executes VLPPO for a set of states PS
    BFS with queue (Q). Uses VLPPO algorithm with present
    state estimate (PS) and associated control decision (ACT) to compute next state estimate (NS) and
    new control decision set (ACT_new).

    G: system Automata.
    Euc, Euo: sets of uncontrollable/unobservable events.
    PS: initial best state estimate.

    Collects states and transitions for the resulting Automata:
    sets_of_states: stores frozenset's of state estimates.
    edge_labels: list of labels for transitions (parallel list to edge_pairs)
    edge_pairs: list of tuples as (source set, target set).

    ACT: initial control decision for the first state-estimate PS
    Note: ACT is encoded into states implicitly as the transitions allowed from each set of states
    (there will be a transition for all labels in ACT, although unobservable transitions only
    form self loops; observable and controllable transitions will execute VLPPO() and find a new
    state estimate to transition to).

    event_ordering: priority ordering of controllable events, with largest priorty going
        to the first element.
    """
    Q = list()
    Q.append((ACT, PS))
    while Q:
        (ACT, PS) = Q.pop(0)
        E_set = set(t[1] for v in PS for t in G.vs[v]["out"])

        for e in ACT:
            NS = PS
            if e not in Euo and e in E_set:
                # Only check observable & valid neighbors (in active event set of PS) for more VLPPOCP computations
                ACT_new, NS = VLPPO(
                    G, Euc, Euo, PS, e, bad_states, event_ordering, eur_dict
                )
                if NS not in sets_of_states:
                    sets_of_states.add(NS)
                    Q.append((ACT_new, NS))
                # some transition(s) still possible, target already exists
            edge_labels.append(e)
            edge_pairs.append((PS, NS))

    return


def VLPPO(G, Euc, Euo, PS, event, bad_states, event_ordering, eur_dict):
    """
    Implementation of VLPPO algorithm:
    G: system automata
    Euc: set of uncontrollable events
    Euo: set of unobservable events
    PS: set of possible states system could be in upon execution of this iteration
    event: observable event that occured last
    good_states: set of states in G that are legal (0 cost); states not in this list are illegal (inf cost)

    Returns a list [ACT, PS_new] as the new control decision set & new best estimate of the
    present state, respectively.
    """
    # 1. Determine set of next states NS
    #       Unobservable reach from current state

    NS = get_N(event, PS, G, Euo)
    # If no event ordering is provided,
    # assume event ordering is whatever the random order of the set of labels is

    # 2. Determine the control action ACT
    ACT = control_action(G, NS, event_ordering.copy(), Euc, Euo, bad_states, eur_dict)
    # 3. Determine UR of states in PS via unobservable events in ACT

    events = frozenset(l for l in ACT if l in Euo)

    PS_new = G.UR.from_set(NS, events, freeze_result=True)
    return ACT, frozenset(PS_new)


def control_action(G, NS, E_list, Euc, Euo, bad_states, eur_dict):
    """
    Given event ordering and set of next states, determine control action ACT
    G: system Automata
    NS: best estimate of the next set of states under the potential new control decision.
    E_list: ordered set of controllable events (priority ordering as first element
        has the highest priority.)
    Euc: set of uncontrollable events
    Euo: set of unobservable events
    bad_states: states with infinite cost

    Returns ACT, the next set of control decisions.
    """
    ACT = Euc.copy()
    Pt = 0
    unobs_ACT = ACT.intersection(Euo)

    UR_set_ACT = G.UR.from_set(NS, unobs_ACT, freeze_result=True)
    ACT_eur = ext_ur_from_set(UR_set_ACT, G, ACT, Euo, eur_dict)

    ACT_eur_labels = {t[1] for v in ACT_eur for t in G.vs[v]["out"]}

    # 2. available controllable events list isn't empty:
    while E_list:
        bad_state_found = False
        # 2.1
        if Pt >= len(E_list):
            return ACT.union(E_list)

        # 2.2: If for ALL x in ure(S from ACT), f(x, E_list[Pt]) does not exist

        event = E_list[Pt]
        if event not in ACT_eur_labels:
            Pt += 1
            continue

        # 2.3:

        # constant time to add/delete; possibly faster than union or copy+add
        ACT.add(event)
        if event in Euo:
            unobs_ACT.add(event)

        UR_set = G.UR.from_set(UR_set_ACT, unobs_ACT, freeze_result=True)

        ure_ACT_E_list = ext_ur_from_set(UR_set, G, ACT, Euo, eur_dict)

        ACT.remove(event)
        if event in Euo:
            unobs_ACT.remove(event)

        if any(True if x in bad_states else False for x in ure_ACT_E_list):
            E_list.remove(event)
            continue

        # 2.4:
        x = E_list.pop(Pt)

        ACT.add(x)

        Pt = 0
    return ACT


def get_N(event, S, G, Euo):
    """
    N_sigma operator defined in paper, to be used in main algorithm step 1
    Given present set of states PS, returns next set of states NS
    where NS are states {x exists in X: x = delta(y, event) for y exists on S}
    Event must be within the event set or null-event (condition comes from N-function definition)
    """
    if event is None:
        return S
    # Otherwise, find the next set of states:
    return frozenset(t[0] for v in S for t in G.vs[v]["out"] if t[1] == event)


def convert_to_graph(P, sets_of_states, edge_pairs, edge_labels, Euc, Euo, init_set):
    """
    Convert graph info into igraph graph P
    Euc, Euo to add attributes to edges in P
    initial_set: the unobservable-reach from state 0 in G (which set of states the system starts in)
    Assumed that P is non-empty
    """

    P.add_vertices(len(sets_of_states))

    sets_of_states.remove(init_set)
    states_dict = {s: i for i, s in enumerate(sets_of_states, 1)}
    states_dict[init_set] = 0
    out = [[] for _ in range(P.vcount())]
    new_edge_pairs = []
    for p, l in zip(edge_pairs, edge_labels):
        source = states_dict[p[0]]
        target = states_dict[p[1]]
        new_edge_pairs.append((source, target))
        out[source].append(P.Out(target, l))

    P.add_edges(new_edge_pairs, edge_labels, fill_out=False)
    P.vs["out"] = out


def ext_ur_from_set(set_of_states, g, ACT, Euo, eur_dict):
    """
    Find extended_ureach for each state in set_of_states.

    set_of_states: states to begin from
    g: igraph Graph object
    ACT: events to consider
    Euo: set of unobservable events in g
    """

    key = (set_of_states, frozenset(ACT))
    if key in eur_dict:
        return eur_dict[key]

    new_set = set(set_of_states)
    for state in set_of_states:
        for t in g.vs[state]["out"]:
            if t[1] in ACT and t[1] not in Euo:
                new_set.add(t[0])

    new_set = frozenset(new_set)
    eur_dict[key] = new_set
    return new_set
    # return x_set.union(t[0] for state in x_set for t in g.vs[state]["out"] if t[1] in e and t[1] not in Euo)
