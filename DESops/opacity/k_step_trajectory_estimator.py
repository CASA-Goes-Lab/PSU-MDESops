# pylint: disable=C0103
"""
Functions related to the mapping-based method of verifying K-step opacity
"""
from DESops.automata.DFA import DFA
from DESops.opacity.contract_secret_traces import contract_secret_traces


def verify_k_step_opacity_trajectory_based(
    g, k, joint=True, secret_type=None, return_num_states=False
):
    """
    Returns whether the given automaton with unobservable events and secret states is k-step opaque

    Returns opaque(, num_states)

    Parameters:
    g: the automaton
    k: the number of steps
    return_num_states: if True, the number of states in the constructed estimator is returned as an additional value
    """
    if secret_type is None:
        if joint:
            secret_type = 1
        else:
            secret_type = 2

    g_c = contract_secret_traces(g, secret_type)
    secret_states = g_c.vs.select(secret=True).indices

    traj_auto, induced_trajectories = construct_k_delay_estimator(g_c, k)

    opaque = verify_k_step_opacity_from_estimator(
        induced_trajectories, secret_states, k, joint
    )

    if return_num_states:
        return opaque, traj_auto.vcount()

    return opaque


def construct_k_delay_estimator(g, k):
    """
    Construct the k-delay estimator for automaton g with the specified secret type

    g: the contracted automaton
    k: the number of steps

    secret_type: what behavior marks an observation period as secret
        1: an observation period is secret if it contains ANY secret state
        2: an observation period is secret if it contains ONLY secret states
    default is type 1 for joint opacity and type 2 for separate opacity
    """
    traj_auto = DFA()
    induced_trajectories = []
    num_steps = k
    events = set(g.es["label"])
    state_mappings = construct_induced_state_mappings(g, events)
    initial_states = g.vs.select(init=True).indices
    construct_induced_state_trajectory_automata(
        traj_auto, induced_trajectories, num_steps, state_mappings, initial_states
    )

    return traj_auto, induced_trajectories


def verify_k_step_opacity_from_estimator(
    induced_trajectories, secret_states, k, joint=True
):
    """
    Returns whether the automaton that produced the induced trajectories is k-step opaque with respect to the given secret states

    Parameters:
    induced_trajectories: the list of estimator trajectories returned by the construct_k_delay_estimator function
    secret_states: the list of indices that were secret in the contracted automaton
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


def construct_induced_state_mappings(g, events):
    """
    Construct the state mappings induced by the given automata for each of the given events.
    Each state mapping is a dictionary that maps a source vertex to a set of target vertices.
    Returns a dictionary of state mappings indexed by events.

    Parameters:
    g: the contracted automata to compute the induced state mappings for
    events: the events of the automata to compute induced state mappings for
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


def construct_induced_state_trajectory_automata(
    traj_auto, induced_trajectories, num_steps, state_mappings, initial_states
):
    """
    Construct the induced state trajectory automaton from the provided state mapping dictionary.

    Parameters:
    traj_auto: the automaton to store the resulting automaton in
    induced_trajectories: a list of induced trajectories indexed by the states of traj_auto
    num_steps: the number of steps in the trajectories considered
    state_mappings: a dictionary of state_mappings of the original system indexed by events
    initial_states: a collection of initial states of the original system
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
            new_traj = compose_state_trajectory_and_mapping(
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


def compose_state_trajectory_and_mapping(st, sm, num_steps):
    """
    Return the composition of a state trajectory and a state mapping. The resulting state trajectory structure consists
    of trajectories of the original state trajectory structure followed by a transition from the state mapping, with the
    original step pruned to preserve the number of steps.

    Parameters:
    st: the state trajectory to compose
    sm: the state mapping to compose
    """
    new_traj = set()
    for path in st:
        if path[num_steps] in sm:
            for target in sm[path[num_steps]]:
                new_traj.add(path[1:] + (target,))
    return new_traj
