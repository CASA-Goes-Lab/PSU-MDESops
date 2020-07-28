"""
Methods for opacity verification of automata
"""
from DESops.basic_operations.observer_comp import observer_comp
from DESops.opacity.k_step_language_based import (
    verify_joint_infinite_step_opacity_language_based,
    verify_k_step_opacity_language_based,
)
from DESops.opacity.k_step_mapping_based import verify_k_step_opacity_mapping_based
from DESops.opacity.k_step_state_based import verify_joint_k_step_opacity_state_based
from DESops.opacity.k_step_two_way_observer import verify_separate_k_step_opacity_TWO
from DESops.opacity.language_functions import find_path_between
from DESops.opacity.unified_framework import (
    verify_k_step_opacity_state_observer,
    verify_k_step_opacity_unified_language,
)


def verify_current_state_opacity(
    g, return_num_states=False, return_violating_path=False
):
    """
    Returns whether the given automaton with unobservable events and secret states is current-state opaque

    Returns: opaque(, num_states)(, violating_path)

    Parameters:
    g: the automaton
    return_num_states: if True, the number of states in the constructed observer is returned as an additional value
    return_violating_path: if True, a list of edge IDs representing a path that violates opacity is returned as an additional value
    """
    # names need to be indices so we can find them from observer
    g.vs["name"] = g.vs.indices
    g_det = observer_comp(g)

    opaque = True
    for estimate in g_det.vs:
        if all([g.vs[i]["secret"] for i in estimate["name"]]):
            opaque = False
            violating_id = estimate.index
            break

    return_list = [opaque]
    if return_num_states:
        return_list.append(g_det.vcount())
    if return_violating_path:
        if opaque:
            return_list.append(None)
        else:
            return_list.append(find_path_between(g_det, 0, violating_id))

    if len(return_list) == 1:
        return return_list[0]
    else:
        return tuple(return_list)


def verify_k_step_opacity(
    g,
    k,
    joint=True,
    secret_type=None,
    method="unified",
    return_num_states=False,
    return_violating_path=False,
):
    """
    Returns whether the given automaton with unobservable events and secret states is k-step opaque

    Returns: opaque(, num_states)(, violating_path)

    Parameters:
    g: the automaton
    k: the number of steps. If k == "infinite", then infinite-step opacity will be checked

    joint: whether joint or separate opacity will be determined:
        joint opacity is violated if an observer can determine that secret behavior occurred
        separate opacity is violated if an observer can determine WHEN the secret behavior occurred
    default is joint

    secret_type: what behavior marks an observation period as secret
        1: an observation period is secret if it contains ANY secret state
        2: an observation period is secret if it contains ONLY secret states
    default is 1 for joint opacity and 2 for separate opacity

    method: the method by which opacity will be determined:
        "language" uses the language-inclusion method
        "mapping" uses the state-mapping estimator method
        "state" uses the state-marking method
        "state-observer" uses the state observer method
        "TWO" uses the two-way observer method
        "unified" uses the unified language method
    default is "unified"

    return_num_states: if True, the number of states in the constructed observer is returned as an additional value

    return_violating_path: if True, a list of observable events representing an opacity-violating path is returned as an additional value
    """
    if k == "infinite":
        return verify_infinite_step_opacity(
            g, joint, secret_type, method, return_num_states, return_violating_path
        )

    if secret_type is None:
        if joint:
            secret_type = 1
        else:
            secret_type = 2

    if method == "unified":
        return verify_k_step_opacity_unified_language(
            g, k, joint, secret_type, return_num_states, return_violating_path
        )

    if method == "language":
        return verify_k_step_opacity_language_based(
            g, k, joint, secret_type, return_num_states, return_violating_path
        )

    if method == "mapping":
        return verify_k_step_opacity_mapping_based(
            g, k, joint, secret_type, return_num_states
        )

    if method == "state":
        if joint and secret_type == 1:
            return verify_joint_k_step_opacity_state_based(
                g, k, return_num_states, return_violating_path
            )
        raise ValueError(
            "State-based method is only implemented for joint opacity with type 1 secrets"
        )

    if method == "state-observer":
        return verify_k_step_opacity_state_observer(
            g, k, joint, secret_type, return_num_states, return_violating_path
        )

    if method == "TWO":
        if not joint:
            return verify_separate_k_step_opacity_TWO(
                g, k, secret_type, return_num_states, return_violating_path
            )
        raise ValueError(
            "Two-way observer method is only implemented for separate opacity"
        )

    raise ValueError(
        "method must be one of: 'language', 'mapping', 'state', 'state-observer', 'TWO', 'unified'"
    )


def verify_infinite_step_opacity(
    g,
    joint=True,
    secret_type=None,
    method="unified",
    return_num_states=False,
    return_violating_path=False,
):
    """
    Returns whether the given automaton with unobservable events and secret states is joint infinite-step opaque

    Returns: opaque(, num_states)(, violating_path)

    Parameters:
    g: the automaton

    joint: not implemented

    secret_type: what behavior marks an observation period as secret
        1: an observation period is secret if it contains ANY secret state
        2: an observation period is secret if it contains ONLY secret states
    default is 1 for joint opacity and 2 for separate opacity

    method: the method by which opacity will be determined:
        "language" uses the language-inclusion method
        "unified" uses the unified framework method
    default is "unified"

    return_num_states: if True, the number of states in the constructed observer is returned as an additional value

    return_violating_path: if True, a list of edge IDs representing a path that violates opacity is returned as an additional value
    """
    if secret_type is None:
        if joint:
            secret_type = 1
        else:
            secret_type = 2

    if method == "unified":
        if joint:
            return verify_k_step_opacity_unified_language(
                g,
                "infinite",
                True,
                secret_type,
                return_num_states,
                return_violating_path,
            )
        raise ValueError(
            "Unified framework method is only implemented for joint opacity"
        )

    if method == "language":
        if joint:
            return verify_joint_infinite_step_opacity_language_based(
                g, secret_type, return_num_states, return_violating_path
            )
        raise ValueError("Language-based method is only implemented for joint opacity")

    if method == "TWO":
        if not joint:
            return verify_separate_k_step_opacity_TWO(
                g, "infinite", secret_type, return_num_states
            )
        raise ValueError(
            "Two-way observer method is only implemented for separate opacity"
        )

    raise ValueError("method must be one of: 'language', 'unified'")
