"""
Functions related to computing a maximal controllable and observable supervisor
for a given system & specification automaton.

offline_VLPPO(), implemented here, is used in an interface to Automata objects
in the Automata class declaration (Automata/Automata.py)
"""

import igraph as ig

from ..basic.construct_subautomata import construct_subautomata
from ..basic.parallel_comp import parallel_comp
from ..basic.refine_product import refine_product_SCS
from ..basic.ureach import *


def offline_VLPPO(
    G,
    H,
    Euc=set(),
    Euo=set(),
    event_ordering=None,
    G_bad_states=None,
    construct_SA=True,
):
    """
    Returns an Automata object which is a maximal controllable & observable supervisor of
        the given system and specification Automata.

    Parameters:
    system: Automata representing the plant/system.
    specification: Automata representing the desired specification.
    event_ordering: optionally provide a priority list of controllable events;
        if not provided, an arbitrary ordering will be used (the set of controllable
        events will be found as a python set(), and then casting the set into a list()).
    G_bad_states (default None): if the specification only intends to disable states in the plant,
        those vertices can be provided directly (slightly more efficient, as the specification
        associated with a list of bad states would already be a subautomaton of the system,
        skipping the step in offline_VLPPO_i where the system & spec are constructed again as
        subautomata). Can be provided as a list or iterable of vertices (as indices, NOT names)
        in the system.
    construct_SA (default True): flag to construct an equivalent G', H' from the system G and
        specification H such that H' is a subautomata of G'. Set to False if the input spec is
        already a subautomata of the input system or G_bad_states was provided (the specification
        is just a disabling of certain states in the system).

    The sets of uncontrollable and unobservable events, Euc and Euo respectively,
    are found as the unions of the Euc & Euo sets in the plant & specification.

    Depends on offline_VLPPO_i, implemented in automata_operations/VLPPO/VLPPO as
    offline_VLPPO().
    """

    # TODO: Find uncontrollable events (if not provided)
    if isinstance(Euo, list):
        Euo = set(Euo)
    # Accumlate sets of states for final control policy in sets_of_states var
    sets_of_states = set()

    if construct_SA:
        G_SA = ig.Graph(directed=True)
        H_SA = ig.Graph(directed=True)
        construct_subautomata(H, G, H_SA, G_SA)
        # To keep names simple, reassign H, G to their SA counterparts.
        H = H_SA
        G = G_SA

    if not G_bad_states:
        # Need to construct H_o as refined product of GxH to determine infinite-cost states
        H_o = ig.Graph(directed=True)
        parallel_comp(H_o, [G, H], save_state_names=True)
        G_bad_states = [
            v["name"][0] for v in H_o.vs if invalid_state(G, H_o, Euc, v["name"][1])
        ]
        comp_G_names = {i[0] for i in H_o.vs["name"]}
        G_bad_states.extend([i.index for i in G.vs if i.index not in comp_G_names])
    else:
        # H_o is equal to H if H is already the intial specification
        H_o = H
    bad_states = compute_state_costs(G, G_bad_states, Euc)
    # State is illegal if in bad_states

    if not event_ordering:
        event_ordering = [label for label in set(G.es["label"]) if label not in Euc]

    edge_labels = list()
    edge_pairs = list()
    # Compute next set of 'present' states PS, and control policy ACT
    [ACT, PS] = VLPPO(G, H_o, Euc, Euo, {0}, {}, bad_states, event_ordering)
    init_set = frozenset(PS)
    P = ig.Graph(directed=True)

    # If the first VLPPO computation found a possible next set of states, use recursive depth-search to traverse all sets of states
    if PS:
        sets_of_states.add(init_set)
        search_VLPPO(
            G,
            H_o,
            Euc,
            Euo,
            PS,
            bad_states,
            sets_of_states,
            edge_labels,
            edge_pairs,
            ACT,
            event_ordering,
        )

        # Create graph P using sets_of_states, edge_labels & edge_pairs
        # modifies sets_of_states
        convert_to_graph(P, sets_of_states, edge_pairs, edge_labels, Euc, Euo, init_set)
    # Otherwise, P will be an empty graph?
    return P


def search_VLPPO(
    G,
    H,
    Euc,
    Euo,
    PS,
    bad_states,
    sets_of_states,
    edge_labels,
    edge_pairs,
    ACT,
    event_ordering,
):
    """
    Executes VLPPO for a set of states PS
    Uses a breadth-first search with a list-style queue (Q). Uses the VLPPO algorithm with present
    state estimate (PS) and associated control decision (ACT) to compute next state estimate (NS) and
    new control decision set (ACT_new).

    G: system Automata.
    H: specification Automata.
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
        E_set = set(G.es(_source_in=PS)["label"])
        for e in ACT:
            NS = PS
            if e not in Euo and e in E_set:
                # Only check observable & valid neighbors (in active event set of PS) for more VLPPOCP computations
                [ACT_new, NS] = VLPPO(G, H, Euc, Euo, PS, e, bad_states, event_ordering)
                if NS not in sets_of_states:
                    sets_of_states.add(frozenset(NS))
                    Q.append((ACT_new, NS))
                # some transition(s) still possible, target already exists
            edge_labels.append(e)
            edge_pairs.append((frozenset(PS), frozenset(NS)))

    return


def VLPPO(G, H, Euc, Euo, PS, event, bad_states, event_ordering):
    """
    Implementation of VLPPO algorithm:
    G: system automata
    H: control policy automata
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
    NS = N(event, PS, G, Euo)

    # If no event ordering is provided,
    # assume event ordering is whatever the random order of the set of labels is

    # 2. Determine the control action ACT
    ACT = control_action(G, H, NS, event_ordering.copy(), Euc, Euo, bad_states)

    # 3. Determine UR of states in PS via unobservable events in ACT (not necessarily Euc?)
    PS_new = set()

    ureach_from_set(PS_new, NS, G, ACT & Euo)
    return [ACT, PS_new]


def control_action(G, H, NS, E_list, Euc, Euo, bad_states):
    """
    Given event ordering and set of next states, determine control action ACT
    G: system Automata
    H: specification Automata
    NS: best estimate of the next set of states under the potential new control decision.
    E_list: ordered set of controllable events (priority ordering as first element
        has the highest priority.)
    Euc: set of uncontrollable events
    Euo: set of unobservable events
    bad_states: states with infinite cost

    Returns ACT, the next set of control decisions.
    """
    ACT = set()
    ACT.update(Euc)
    Pt = 0

    ACT_eur = set()
    ACT_eur.update(NS)
    extended_ureach_from_set(ACT_eur, NS, G, ACT, Euo)

    # 2. available controllable events list isn't empty:
    while E_list:
        bad_state_found = False
        # 2.1
        if Pt > len(E_list) - 1:
            if not ACT:
                return set(E_list)
            return ACT.union(E_list)
        # 2.2: If for ALL x in ure(S from ACT), f(x, E_list[Pt]) does not exist

        if E_list[Pt] not in G.es(_source_in=ACT_eur)["label"]:
            Pt = Pt + 1
            continue

        ure_ACT_E_list = set()
        a = ACT.copy()
        a.add(E_list[Pt])
        extended_ureach_from_set(ure_ACT_E_list, NS, G, a, Euo)
        if any([True if x in bad_states else False for x in ure_ACT_E_list]):
            E_list.remove(E_list[Pt])
            continue

        # 2.4:
        ACT.add(E_list[Pt])
        E_list.remove(E_list[Pt])
        Pt = 0
    return ACT


def N(event, S, G, Euo):
    """
    N_sigma operator defined in paper, to be used in main algorithm step 1
    Given present set of states PS, returns next set of states NS
    where NS are states {x exists in X: x = delta(y, event) for y exists on S}
    Event must be within the event set or null-event (condition comes from N-function definition)
    """
    if not event:
        return S
    # Otherwise, find the next set of states:
    NS = set()
    return {t.target for t in G.es(_source_in=S) if t["label"] == event}


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

    new_edge_pairs = [(states_dict[p[0]], states_dict[p[1]]) for p in edge_pairs]

    # Below required to name states (currently just using generic names)

    # Replace indices in sets (in sets_of_states) w/ their respective names in G
    # sets_of_states = {frozenset({G.vs["name"][i] if not isinstance(i,Event) else G.vs["name"][i].tuple() for i in s}) for s in sets_of_states}
    # init_set = frozenset({G.vs["name"][i] for i in init_set})

    # vs_names = list()
    # vs_names.append(init_set)
    # vs_names.extend(sets_of_states)

    # Rm.vs["name"] = vs_names
    P.add_edges(new_edge_pairs)
    P.es["label"] = edge_labels
    P.vs["name"] = [i for i in range(0, P.vcount())]


def compute_state_costs(G, states_removed, Euc):
    bad_states = set()
    states_to_check = states_removed
    while states_to_check:
        bad_states.update(states_to_check)
        # Back out the next potentially infinite-cost states as those with uncontrollable transitions
        # to the most recent set of infinite cost states (states_to_check on the RHS).
        states_to_check = {
            e.source
            for e in G.es(_target_in=states_to_check)
            if e["label"] in Euc and e.source not in bad_states
        }
    return bad_states


def invalid_state(G, H, Euc, H_state):
    H_uc_count = len([e for e in H.es(_source=H_state) if e["label"] in Euc])
    G_assoc_state = H.vs["name"][H_state][0]
    G_uc_count = len([e for e in G.es(_source=G_assoc_state) if e["label"] in Euc])
    return H_uc_count < G_uc_count
