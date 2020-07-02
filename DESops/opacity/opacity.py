"""
Methods for opacity verification of automata
"""
from DESops.basic_operations.observer_comp import observer_comp_old
from DESops.opacity.k_step_language_based import (
    verify_joint_infinite_step_opacity_language_based,
    verify_k_step_opacity_language_based,
)
from DESops.opacity.k_step_mapping_based import verify_k_step_opacity_mapping_based
from DESops.opacity.k_step_state_based import verify_joint_k_step_opacity_state_based
from DESops.opacity.unified_framework import verify_k_step_opacity_unified


def verify_current_state_opacity(g, return_num_states=False):
    """
    Returns whether the given automaton with unobservable events and secret states is current-state opaque

    Parameters:
    g: the automaton
    return_num_states: if true, the function will return a (bool, int) tuple where:
        first return value tells whether g is current state opaque
        second return value is the number of states in the constructed observer
    """
    g_det = observer_comp_old(g, Euo=g.Euo)

    opaque = True
    for estimate in g_det.vs:
        if all([g.vs[i]["secret"] for i in estimate["name"]]):
            opaque = False

    if return_num_states:
        return opaque, g_det.vcount()

    return opaque


def verify_k_step_opacity(
    g, k, joint=True, secret_type=None, method="unified", return_num_states=False
):
    """
    Returns whether the given automaton with unobservable events and secret states is k-step opaque

    Parameters:
    g: the automaton
    k: the number of steps

    joint: whether joint or separate opacity will be determined:
        joint opacity is violated if an observer can determine that secret behavior occurred
        separate opacity is violated if an observer can determine WHEN the secret behavior occurred
    default is joint

    secret_type: what behavior marks an observation period as secret
        type 1: an observation period is secret if it contains ANY secret state
        type 2: an observation period is secret if it contains ONLY secret states
    default is type 1 for joint opacity and type 2 for separate opacity

    method: the method by which opacity will be determined:
        "language" uses the language-inclusion method
        "mapping" uses the state-mapping estimator method
        "state" uses the state-marking method
        "unified" uses the unified framework method
    default is "unified"

    return_num_states: if true, the function will return a (bool, int) tuple where:
        first return value tells whether g is k-step opaque
        second return value is the number of states in the final automaton constructed by the function
    """
    if secret_type is None:
        if joint:
            secret_type = 1
        else:
            secret_type = 2

    if method == "unified":
        return verify_k_step_opacity_unified(
            g, k, joint, secret_type, return_num_states
        )

    if method == "language":
        return verify_k_step_opacity_language_based(
            g, k, joint, secret_type, return_num_states
        )

    if method == "mapping":
        return verify_k_step_opacity_mapping_based(
            g, k, joint, secret_type, return_num_states
        )

    if method == "state":
        if joint and secret_type == 1:
            return verify_joint_k_step_opacity_state_based(g, k, return_num_states)
        else:
            raise ValueError(
                "State-based method is only implemented for joint opacity with type 1 secrets"
            )

    raise ValueError("method must be one of: 'language', 'mapping', 'state', 'unified'")


def verify_infinite_step_opacity(g, joint=True, secret_type=None):
    """
    Returns whether the given automaton with unobservable events and secret states is joint infinite-step opaque

    Parameters:
    g: the automaton
    joint: not yet implemented

    secret_type: what behavior marks an observation period as secret
        type 1: an observation period is secret if it contains ANY secret state
        type 2: an observation period is secret if it contains ONLY secret states
    default is type 1 for joint opacity and type 2 for separate opacity

    return_num_states: if true, the function will return a (bool, int) tuple where:
        first return value tells whether g is k-step opaque
        second return value is the number of states in the final automaton constructed by the function
    """
    if secret_type is None:
        if joint:
            secret_type = 1
        else:
            secret_type = 2

    if joint:
        return verify_joint_infinite_step_opacity_language_based(g, secret_type)

    raise ValueError(
        "Infinite step opacity is currently only implemented for joint opacity"
    )
