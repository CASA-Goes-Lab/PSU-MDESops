"""
Methods for opacity verification of automata
"""
from DESops.basic_operations import composition
from DESops.basic_operations.construct_reverse import reverse
from DESops.opacity.k_step_language_comparison import (
    verify_k_step_opacity_language_comparison,
)
from DESops.opacity.k_step_state_observer import verify_k_step_opacity_state_observer
from DESops.opacity.k_step_trajectory_estimator import (
    verify_k_step_opacity_trajectory_based,
)
from DESops.opacity.k_step_two_way_observer import verify_separate_k_step_opacity_TWO
from DESops.opacity.language_functions import find_path_between
# from DESops.opacity.secret_specification import OpacityNotion


def verify_current_state_opacity(
    g, return_num_states=False, return_violating_path=False
):
    """Returns whether the given automaton with unobservable events and secret states is current-state opaque

    Parameters
    ----------
    g : Automata
        The automaton
    return_num_states : bool
        if True, the number of states in the constructed observer is returned as an additional value (Default value = False)
    return_violating_path : bool
        if True, a list of edge IDs representing a path that violates opacity is returned as an additional value (Default value = False)

    Returns
    -------
    tuple
        opaque(, num_states)(, violating_path)

    """
    # names need to be indices so we can find them from observer
    g.vs["name"] = g.vs.indices
    g_det = composition.observer(g)

    opaque = True
    # opacity violated if all states in any estimate are secret
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


def verify_initial_state_opacity(g):
    """Returns whether the given automaton with unobservable events and secret states is inital-state opaque

    Parameters
    ----------
    g : Automata
        The automaton

    Returns
    -------
    bool
        Whether the given automaton is opaque

    """
    g_r = reverse(g, use_marked_states=False)
    # names need to be indices so we can find them from observer
    g_r.vs["name"] = g.vs.indices
    g_r_obs = composition.observer(g_r)

    opaque = True
    # opacity violated if all initial states in any estimate are secret
    for estimate in g_r_obs.vs["name"]:
        if all([g.vs[i]["secret"] for i in estimate if g.vs[i]["init"]]):
            opaque = False
            break

    return opaque


def verify_k_step_opacity(
    g,
    k,
    joint=True,
    secret_type=None,
    method="language",
    return_num_states=False,
    return_violating_path=False,
):
    """Returns whether the given automaton with unobservable events and secret states is k-step opaque
    Uses given method for verification (default is "language")

    Parameters
    ----------
    g : Automata
        The automaton
    k : int or str
        The number of steps (or "infinite")
    joint : bool
        Whether or not to consider joint opacity (Default value = True)
    secret_type : int
        Type 1 or type 2 (Default value = None)
    method : str
        The verification method
        "language" uses the language-comparison method
        "trajectory" uses the trajectory estimator method
        "state" uses the state observer method
        "TWO" uses the two-way observer method (Default value = "language")
    return_num_states : bool
        if True, the number of states in the constructed observer is returned as an additional value (Default value = False)
    return_violating_path : bool
        if True, a list of edge IDs representing a path that violates opacity is returned as an additional value (Default value = False)

    Returns
    -------
    tuple
        opaque(, num_states)(, violating_path)

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

    if method == "language":
        return verify_k_step_opacity_language_comparison(
            g, k, joint, secret_type, return_num_states, return_violating_path
        )

    if method == "state":
        return verify_k_step_opacity_state_observer(
            g, k, joint, secret_type, return_num_states, return_violating_path
        )

    if method == "trajectory":
        return verify_k_step_opacity_trajectory_based(
            g, k, joint, secret_type, return_num_states
        )

    if method == "TWO":
        if not joint:
            return verify_separate_k_step_opacity_TWO(
                g, k, secret_type, return_num_states, return_violating_path
            )
        raise ValueError("Two-way observer can only verify separate opacity")

    if method == "forward-language":
        return verify_k_step_opacity_language_comparison(
            g, k, joint, secret_type, return_num_states, return_violating_path, False
        )

    raise ValueError(
        "method must be one of: 'language', 'state', 'trajectory', 'TWO', 'forward-language'"
    )


def verify_infinite_step_opacity(
    g,
    joint=True,
    secret_type=None,
    method="unified",
    return_num_states=False,
    return_violating_path=False,
):
    """Returns whether the given automaton with unobservable events and secret states is joint infinite-step opaque
    Uses given method for verification (default is "unified")

    Parameters
    ----------
    g : Automata
        The automaton
    joint : bool
        Whether or not to consider joint opacity (separate is not implemented) (Default value = True)
    secret_type : int
        Type 1 or type 2 (Default value = None)
    method : str
        The verification method
        "language" uses the language-inclusion method
        "unified" uses the unified framework method (Default value = "unified")
    return_num_states : bool
        if True, the number of states in the constructed observer is returned as an additional value (Default value = False)
    return_violating_path : bool:return: opaque(, num_states)(, violating_path)
        if True, a list of edge IDs representing a path that violates opacity is returned as an additional value (Default value = False)

    Returns
    -------

    """
    if secret_type is None:
        if joint:
            secret_type = 1
        else:
            secret_type = 2

    if method == "language":
        if joint:
            return verify_k_step_opacity_language_comparison(
                g,
                "infinite",
                True,
                secret_type,
                return_num_states,
                return_violating_path,
            )
        raise ValueError("Language comparison can only verify joint opacity")

    if method == "state":
        if joint:
            return verify_k_step_opacity_state_observer(
                g,
                "infinite",
                True,
                secret_type,
                return_num_states,
                return_violating_path,
            )
        raise ValueError("Language comparison can only verify joint opacity")

    if method == "TWO":
        if not joint:
            return verify_separate_k_step_opacity_TWO(
                g, "infinite", secret_type, return_num_states, return_violating_path
            )
        raise ValueError(
            "Two-way observer method is only implemented for separate opacity"
        )

    if method == "forward-language":
        if joint:
            return verify_k_step_opacity_language_comparison(
                g,
                "infinite",
                True,
                secret_type,
                return_num_states,
                return_violating_path,
                False,
            )
        raise ValueError("Language comparison can only verify joint opacity")

    raise ValueError(
        "method must be one of: 'language', 'state', 'TWO', 'forward-language'"
    )
