"""
Methods for opacity verification for automata
"""
from DESops.basic_operations.observer_comp import observer_comp_old
from DESops.opacity.k_step_language_based import (
    verify_joint_infinite_step_opacity_language_based,
    verify_joint_k_step_opacity_language_based,
    verify_separate_k_step_opacity_language_based,
)
from DESops.opacity.k_step_mapping_based import (
    verify_joint_k_step_opacity_mapping_based,
    verify_separate_k_step_opacity_mapping_based,
)
from DESops.opacity.k_step_state_based import verify_joint_k_step_opacity_state_based


def verify_current_state_opacity(g):
    """
    Returns whether the given automaton with unobservable events and secret states is current-state opaque

    Parameters:
    g: the automaton
    """
    g_det = observer_comp_old(g, Euo=g.Euo)
    for estimate in g_det.vs:
        if all([g.vs[i]["secret"] for i in estimate["name"]]):
            return False
    return True


def verify_joint_k_step_opacity(g, k, method="language"):
    """
    Returns whether the given automaton with unobservable events and secret states is joint k-step opaque

    Parameters:
    g: the automaton
    k: the number of steps
    method: the method by which opacity will be determined:
        "language" for language-based
        "mapping" for mapping-based
        "state" for state-based
    """
    if method == "language":
        return verify_joint_k_step_opacity_language_based(g, k)
    if method == "mapping":
        return verify_joint_k_step_opacity_mapping_based(g, k)
    if method == "state":
        return verify_joint_k_step_opacity_state_based(g, k)
    else:
        raise ValueError("method must be one of 'mapping', 'language', or 'state'")


def verify_joint_infinite_step_opacity(g):
    """
    Returns whether the given automaton with unobservable events and secret states is joint infinite-step opaque

    Parameters:
    g: the automaton
    """
    return verify_joint_infinite_step_opacity_language_based(g)


def verify_separate_k_step_opacity(g, k, method="language"):
    """
    Returns whether the given automaton with unobservable events and secret states is separate k-step opaque

    Parameters:
    g: the automaton
    k: the number of steps
    method: the method by which opacity will be determined:
        "language" for language-based
        "mapping" for mapping-based
    """
    if method == "language":
        return verify_separate_k_step_opacity_language_based(g, k)
    if method == "mapping":
        return verify_separate_k_step_opacity_mapping_based(g, k)
    else:
        raise ValueError("method must be one of 'mapping' or 'language'")
