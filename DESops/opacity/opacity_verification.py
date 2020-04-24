# pylint: disable=C0103
"""
Methods for opacity verification for automata
"""
from DESops.Automata import Automata
import DESops.opacity.state_estimation as state_estimation
from DESops.opacity.contract_secret_traces import contract_secret_traces


def verify_joint_k_step_opacity(g, k):
    """
    Determine if the given automaton with unobservable events and secret states is joint k-step opaque

    Parameters:
    g: the automaton
    k: the number of steps
    """
    h = Automata()
    contract_secret_traces(g, h, g.Euo, False)
    return verify_joint_k_step_opacity_from_NFA(h, k)


def verify_joint_k_step_opacity_from_NFA(g, k):
    """
    Determine if the given NFA with secret states is joint k-step opaque

    Parameters:
    g: the automaton
    k: the number of steps
    """
    traj_auto = Automata()
    induced_trajectories = []
    num_states = g.vcount()
    num_steps = k
    events = set(g.es["label"])
    state_mappings = state_estimation.construct_induced_state_mappings(g, events)
    initial_states = g.vs.select(init=True).indices
    state_estimation.construct_induced_state_trajectory_automata(traj_auto, induced_trajectories, num_states, num_steps,
                                                                 state_mappings, initial_states)
    secret_states = g.vs.select(secret=True).indices
    for traj in induced_trajectories:
        if not traj.exists_avoiding_trajectory(secret_states):
            return False
    return True


def verify_separate_k_step_opacity(g, k):
    """
    Determine if the given automaton with unobservable events and secret states is separate k-step opaque

    Parameters:
    g: the automaton
    k: the number of steps
    """
    h = Automata()
    contract_secret_traces(g, h, g.Euo, True)
    return verify_separate_k_step_opacity_from_NFA(h, k)


def verify_separate_k_step_opacity_from_NFA(g, k):
    """
    Determine if the given NFA with secret states is separate k-step opaque

    Parameters:
    g: the automaton
    k: the number of steps
    """
    traj_auto = Automata()
    induced_trajectories = []
    num_states = g.vcount()
    num_steps = k
    events = set(g.es["label"])
    state_mappings = state_estimation.construct_induced_state_mappings(g, events)
    initial_states = g.vs.select(init=True).indices
    state_estimation.construct_induced_state_trajectory_automata(traj_auto, induced_trajectories, num_states, num_steps,
                                                                 state_mappings, initial_states)
    nonsecret_states = g.vs.select(secret=False).indices
    for traj in induced_trajectories:
        if not all([traj.can_visit(nonsecret_states, step) for step in range(k + 1)]):
            return False
    return True
