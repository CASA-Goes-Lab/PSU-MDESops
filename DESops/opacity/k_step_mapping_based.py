# pylint: disable=C0103
"""
Methods for opacity verification for automata
"""
import DESops.opacity.state_estimation as state_estimation
from DESops.automata.automata import _Automata
from DESops.opacity.contract_secret_traces import contract_secret_traces


def verify_joint_k_step_opacity_mapping_based(g, k, return_num_states=False):
    """
    Determine if the given automaton with unobservable events and secret states is joint k-step opaque

    Parameters:
    g: the automaton
    k: the number of steps
    return_num_states: used for testing space usage: causes the return value to be the number of states in the constructed automaton
    """
    h = _Automata()
    contract_secret_traces(g, h, g.Euo, False)
    return verify_joint_k_step_opacity_from_NFA(h, k, return_num_states)


def verify_joint_k_step_opacity_from_NFA(g, k, return_num_states=False):
    """
    Determine if the given NFA with secret states is joint k-step opaque

    Parameters:
    g: the automaton
    k: the number of steps
    """
    traj_auto = _Automata()
    induced_trajectories = []
    num_steps = k
    events = set(g.es["label"])
    state_mappings = construct_induced_state_mappings(g, events)
    initial_states = g.vs.select(init=True).indices
    construct_induced_state_trajectory_automata(
        traj_auto, induced_trajectories, num_steps, state_mappings, initial_states
    )

    if return_num_states:
        return traj_auto.vcount()

    secret_states = g.vs.select(secret=True).indices
    for traj in induced_trajectories:
        nonsecret_found = False
        for path in traj:
            if all([(i not in secret_states) for i in path]):
                nonsecret_found = True
                break
        if not nonsecret_found:
            return False
    return True


def construct_induced_state_mappings(g, events):
    """
    Construct the state mappings induced by the given automata for each of the given events.
    Each state mapping is a dictionary that maps a source vertex to a set of target vertices.
    Returns a dictionary of state mappings indexed by events.

    Parameters:
    g: the original automata to compute the induced state mappings for
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


def verify_joint_k_step_opacity_mapping_based_old(g, k, return_num_states=False):
    """
    Determine if the given automaton with unobservable events and secret states is joint k-step opaque

    Parameters:
    g: the automaton
    k: the number of steps
    return_num_states: used for testing space usage: causes the return value to be the number of states in traj_auto
    """
    h = _Automata()
    contract_secret_traces(g, h, g.Euo, False)
    return verify_joint_k_step_opacity_from_NFA_old(h, k, return_num_states)


def verify_joint_k_step_opacity_from_NFA_old(g, k, return_num_states=False):
    """
    Determine if the given NFA with secret states is joint k-step opaque

    Parameters:
    g: the automaton
    k: the number of steps
    """
    traj_auto = _Automata()
    induced_trajectories = []
    num_states = g.vcount()
    num_steps = k
    events = set(g.es["label"])
    state_mappings = state_estimation.construct_induced_state_mappings(g, events)
    initial_states = g.vs.select(init=True).indices
    state_estimation.construct_induced_state_trajectory_automata(
        traj_auto,
        induced_trajectories,
        num_states,
        num_steps,
        state_mappings,
        initial_states,
    )

    if return_num_states:
        return traj_auto.vcount()

    secret_states = g.vs.select(secret=True).indices
    for traj in induced_trajectories:
        if not traj.exists_avoiding_trajectory(secret_states):
            return False
    return True


def verify_separate_k_step_opacity_mapping_based(g, k):
    """
    Determine if the given automaton with unobservable events and secret states is separate k-step opaque

    Parameters:
    g: the automaton
    k: the number of steps
    """
    h = _Automata()
    contract_secret_traces(g, h, g.Euo, True)
    return verify_separate_k_step_opacity_from_NFA(h, k)


def verify_separate_k_step_opacity_from_NFA(g, k):
    """
    Determine if the given NFA with secret states is separate k-step opaque

    Parameters:
    g: the automaton
    k: the number of steps
    """
    traj_auto = _Automata()
    induced_trajectories = []
    num_states = g.vcount()
    num_steps = k
    events = set(g.es["label"])
    state_mappings = state_estimation.construct_induced_state_mappings(g, events)
    initial_states = g.vs.select(init=True).indices
    state_estimation.construct_induced_state_trajectory_automata(
        traj_auto,
        induced_trajectories,
        num_states,
        num_steps,
        state_mappings,
        initial_states,
    )
    nonsecret_states = g.vs.select(secret=False).indices
    for traj in induced_trajectories:
        if not all([traj.can_visit(nonsecret_states, step) for step in range(k + 1)]):
            return False
    return True
