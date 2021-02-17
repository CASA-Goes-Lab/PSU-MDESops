'''
Functions related to the secret observer construction for opacity
'''
from DESops.basic_operations import composition
from DESops.basic_operations.product_NFA import product_NFA


def construct_secret_observer(
    g,
    h_ns,
    ns_state_sets,
    joint,
    obs_map
):
    """
    Constructs the secret observer of the system, an automaton marking admissible observations

    Parameters:
    g: the automaton modeling the original system
    h_ns: the nonsecret specification automaton
    ns_state_sets: sets of states of h_ns corresponding to the different notions of nonsecrecy
    secret_type: "joint" or "separate"
    obs_map: the observation map

    Returns:
    g_so: The secret observer automaton
    """
    '''
    Here state markings represent behavior that we want to consider.
    Runs that do not end at marked states in both g and h_ns are not used as
    counterexamples or explanations for opacity.
    Most of the time this means that all states of g and h_ns should be marked.
    The secrecy of runs is defined entirely by ns_state_sets.

    The marking of g_so on the other hand represents observations that violate opacity.
    '''
    g_ns = product_NFA([g, h_ns], save_marked_states=True)

    g_ns_obs = apply_obs_map(g_ns, obs_map)

    g_so = composition.observer(g_ns_obs)

    if not joint:
        '''
        For separate opacity, a state of the secret observer is marked if
        it is relevant behavior, i.e., it is marked in the observer construction,
        and there is a type of secret such that for all pairs in the state,
        the pair is not marked or the h component is not nonsecret.
        '''
        for state in g_so.vs:
            state["marked"] = state['marked'] and any([all([
                not g_ns_obs.vs.select(name=pair)["marked"]
                or (pair[1] not in ns_states)
                for pair in state["name"]])
                for ns_states in ns_state_sets])
    else:
        '''
        For joint opacity, a state of the secret observer is marked if
        it is relevant behavior, i.e., it is marked in the observer construction,
        and for every state of g in the observer state, there is some secret type
        such that for every pair corresponding to the given state of g,
        the pair is either not marked or the h component is not nonsecret.
        '''
        for state in g_so.vs:
            state["marked"] = state['marked'] and all([any([all([
                not g_ns_obs.vs.select(name=pair)["marked"]
                or (pair[1] not in ns_states)
                for pair in state["name"] if pair[0] == q])
                for ns_states in ns_state_sets])
                for q in [pair[0] for pair in state["name"]]])

    g_so.generate_out()
    return g_so


def apply_obs_map(g, obs_map):
    '''
    Construct an automaton marking observations of the given system.

    Parameters:
    g: The automaton under observation
    obs_map: The static mask observation map

    Returns: An automaton marking observations of g with obs_map
    '''
    g_obs = g.copy()
    g_obs.es['label'] = [obs_map[e["label"]] for e in g_obs.es]
    g_obs.events = set(g_obs.es['label'])
    g_obs.Euo = {""}
    g_obs.generate_out()
    return g_obs

def verify_opacity_secret_observer(g_so):
    '''
    Verify the system corresponding to the given secret observer is opaque

    Parameters:
    g_so: The secret observer automaton marking secrets

    Returns:
    is_opaque: whether the system is opaque or not
    violating_index: the index of a state violating opacity if one exists
    '''
    violating_state = next(v for v in g_so.vs if v["marked"])
    if violating_state:
        return False, violating_state.index
    else:
        return True, violating_state.index
