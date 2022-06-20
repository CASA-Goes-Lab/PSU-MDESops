# pylint: disable=C0103
"""
Functions related to the mapping-based method of verifying K-step opacity
"""
from DESops.automata.DFA import DFA
from DESops.opacity.contract_secret_traces import contract_secret_traces

# TODO refactor this file to use new Automata conventions (secret and inital state labels)
def verify_k_step_opacity_trajectory_based(
    g, k, joint=True, secret_type=None, return_num_states=False
):
    """
    Returns whether the given automaton with unobservable events and secret states is k-step opaque

    :param g: the automaton
    :type g: Automaton
    :param k: the number of steps
    :type k: int
    :param joint: Whether or not to verify joint opacity
    :type joint: bool
    :param secret_type: Type 1 or type 2
    :type secret_type: int
    :param return_num_states: if True, the number of states in the product used for checking language inclusion is returned as an additional value
    :type return_num_states: bool
    :return: is_opaque (, num_states)
    :rtype: tuple
    """
    if secret_type is None:
        if joint:
            secret_type = 1
        else:
            secret_type = 2

    g_c = contract_secret_traces(g, secret_type)
    secret_states = g_c.vs.select(secret=True).indices

    traj_auto, induced_trajectories = construct_k_delay_estimator(g_c, k)

    opaque = _verify_k_step_opacity_from_estimator(
        induced_trajectories, secret_states, k, joint
    )

    if return_num_states:
        return opaque, traj_auto.vcount()

    return opaque


def construct_k_delay_estimator(g, k):
    """
    Construct the k-delay estimator for automaton g with the specified secret type

    :param g: The automaton
    :type g: Automata
    :param k: The number of steps
    :type k: int
    :return: The k-delay estimator
    :rtype: DFA
    """
    traj_auto = DFA()
    induced_trajectories = []
    num_steps = k
    events = set(g.es["label"])
    state_mappings = _construct_induced_state_mappings(g, events)
    initial_states = g.vs.select(init=True).indices
    _construct_induced_state_trajectory_automata(
        traj_auto, induced_trajectories, num_steps, state_mappings, initial_states
    )

    return traj_auto, induced_trajectories


def _verify_k_step_opacity_from_estimator(
    induced_trajectories, secret_states, k, joint=True
):
    """
    Returns whether the automaton that produced the induced trajectories is k-step opaque with respect to the given secret states

    :param induced_trajectories: The list of estimator trajectories returned by the construct_k_delay_estimator function
    :type induced_trajectories: list
    :param secret_states: the list of indices that were secret in the contracted automaton
    :type secret_states: list
    :param k: The number of steps
    :type k: int
    :param joint: Whether or not to verify joint opacity
    :type joint: bool
    :return: Whether or not the system is opaque
    :rtype: bool
    """
    if joint:
        # opacity requires that every trajectory contains a path that does not visit any secret state
        for traj in induced_trajectories:
            nonsecret_found = False
            for path in traj:
                if all([(i not in secret_states) for i in path]):
                    nonsecret_found = True
                    # if we find any path containing no secret states, then this trajectory is good
                    break
            if not nonsecret_found:
                return False
        return True

    else:
        # opacity requires that for every step in every trajectory, some path visits a nonsecret state at that step
        for traj in induced_trajectories:
            for step in range(k + 1):
                if not any([(path[step] not in secret_states) for path in traj]):
                    return False
        return True


def _construct_induced_state_mappings(g, events):
    """
    Construct the state mappings induced by the given automata for each of the given events.
    Each state mapping is a dictionary that maps a source vertex to a set of target vertices.
    Returns a dictionary of state mappings indexed by events.

    :param g: The automaton
    :type g: Automaton
    :param events: the events of the automata to compute induced state mappings for
    :type events: set
    :return: The induced state mapping
    :rtype: set
    """
    sm = dict()
    for e in events:
        sm[e] = dict()
    for t in g.es:
        if t.source in sm[t["label"]]:
            sm[t["label"]][t.source].add(t.target)
        else:
            sm[t["label"]][t.source] = {t.target}
    return sm


def _construct_induced_state_trajectory_automata(
    traj_auto, induced_trajectories, num_steps, state_mappings, initial_states
):
    """
    Construct the induced state trajectory automaton from the provided state mapping dictionary.

    :param traj_auto: the automaton to store the resulting automaton in
    :type traj_auto: Automaton
    :param induced_trajectories: a list of induced trajectories indexed by the states of traj_auto
    :type induced_trajectories: list
    :param num_steps: the number of steps in the trajectories considered
    :type num_steps: int
    :param state_mappings: a dictionary of state_mappings of the original system indexed by events
    :type state_mappings: dict
    :param initial_states: a collection of initial states of the original system
    :type initial_states: set
    :return: None
    :rtype: NoneType
    """
    initial_trajectory = set()
    for i in initial_states:
        initial_trajectory.add(tuple([i] * (num_steps + 1)))

    induced_trajectories.append(initial_trajectory)
    traj_auto.add_vertex()
    events = state_mappings
    if not events:
        return

    unexplored = {0}
    while unexplored:
        current_index = unexplored.pop()
        for event in events:
            new_traj = _compose_state_trajectory_and_mapping(
                induced_trajectories[current_index], state_mappings[event], num_steps
            )
            if not new_traj:
                continue
            try:
                new_index = induced_trajectories.index(new_traj)
            except ValueError:
                new_index = len(induced_trajectories)
                traj_auto.add_vertex()
                induced_trajectories.append(new_traj)
                unexplored.add(new_index)
            traj_auto.add_edge(current_index, new_index, label=event)


def _compose_state_trajectory_and_mapping(st, sm, num_steps):
    """
    Return the composition of a state trajectory and a state mapping. The resulting state trajectory structure consists
    of trajectories of the original state trajectory structure followed by a transition from the state mapping, with the
    original step pruned to preserve the number of steps.

    :param st: The state trajectory to compose
    :type st: set
    :param sm: The state mapping to compose
    :type sm: dict
    :param num_steps:
    :type num_steps:
    :return: The trajectories resulting from the composition
    :rtype: set
    """
    new_traj = set()
    for path in st:
        if path[num_steps] in sm:
            for target in sm[path[num_steps]]:
                new_traj.add(path[1:] + (target,))
    return new_traj
