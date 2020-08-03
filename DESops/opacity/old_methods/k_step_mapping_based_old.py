from DESops.automata.automata import _Automata
from DESops.opacity import state_estimation
from DESops.opacity.contract_secret_traces import contract_secret_traces


def verify_joint_k_step_opacity_mapping_based_old(
    g, k, secret_type=1, return_num_states=False
):
    """
    Determine if the given automaton with unobservable events and secret states is joint k-step opaque

    Parameters:
    g: the automaton
    k: the number of steps
    return_num_states: used for testing space usage: causes the return value to be the number of states in traj_auto
    """
    h = _Automata()
    contract_secret_traces(g, secret_type, h, g.Euo)
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


def verify_separate_k_step_opacity_mapping_based_old(g, k, secret_type=2):
    """
    Determine if the given automaton with unobservable events and secret states is separate k-step opaque

    Parameters:
    g: the automaton
    k: the number of steps
    """
    h = _Automata()
    contract_secret_traces(g, secret_type, h, g.Euo)
    return verify_separate_k_step_opacity_from_NFA_old(h, k)


def verify_separate_k_step_opacity_from_NFA_old(g, k):
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
