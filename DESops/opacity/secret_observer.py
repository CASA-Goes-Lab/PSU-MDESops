'''
Functions related to the secret observer construction for opacity
'''
from DESops.basic_operations import composition
from DESops.basic_operations.product_NFA import product_NFA

from DESops.opacity.secret_specification import construct_nonsecret_spec
from DESops.opacity.label_transform import transform_secret_labels, induced_observation_map
from DESops.opacity.observation_map import observable_projection_map, StaticMask, SetValuedStaticMask, NonDetDynamicMask
from DESops.opacity.language_functions import language_inclusion
from DESops.basic_operations.transducers import transducer_input_automaton

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
    g_ns_obs = obs_map.apply_obs_map(g_ns)
    g_so = composition.observer(g_ns_obs)
    '''
    if not joint:
        """
        For separate opacity, a state of the secret observer is marked if
        it is relevant behavior, i.e., it is marked in the observer construction,
        and there is a type of secret such that for all pairs in the state,
        the pair is not marked or the h component is not nonsecret.
        """
        for state in g_so.vs:
            state["marked"] = state['marked'] and any([all([
                not g_ns_obs.vs.select(name=pair)["marked"]
                or (pair[1] not in ns_states)
                for pair in state["name"]])
                for ns_states in ns_state_sets])
    else:
        """
        For joint opacity, a state of the secret observer is marked if
        it is relevant behavior, i.e., it is marked in the observer construction,
        and for every state of g in the observer state, there is some secret type
        such that for every pair corresponding to the given state of g,
        the pair is either not marked or the h component is not nonsecret.
        """
        for state in g_so.vs:
            state["marked"] = state['marked'] and all([any([all([
                not g_ns_obs.vs.select(name=pair)["marked"]
                or (pair[1] not in ns_states)
                for pair in state["name"] if pair[0] == q])
                for ns_states in ns_state_sets])
                for q in [pair[0] for pair in state["name"]]])
    '''
    for state in g_so.vs:
        state['marked'] = is_obs_state_secret(state, ns_state_sets, joint)

    g_so.generate_out()
    return g_so


def verify_opacity_secret_observer(g_so):
    """
    Verify the system corresponding to the given secret observer is opaque

    Parameters:
    g_so: The secret observer automaton marking secrets

    Returns:
    is_opaque: whether the system is opaque or not
    violating_index: the index of a state violating opacity if one exists
    """
    try:
        violating_state = next(v for v in g_so.vs if v["marked"])
        return False, violating_state.index
    except StopIteration:
        return True, -1


def construct_secret_observer_label_transform(g, obs_map=None, notion='CSO', joint=False, **spec_kwargs,):
    '''
    Parameters:
    g: The automaton modeling the system
    obs_map: The static mask observation map used for the system
    '''

    a, Ens, Einit = transform_secret_labels(g)
    if not obs_map:
        obs_map = observable_projection_map(g)
    if not isinstance(obs_map, StaticMask) and not isinstance(obs_map, SetValuedStaticMask):
        raise NotImplementedError('The secret observer construction for label transformed systems is not yet '
                                  'implemented for this type observation map.')
    obs_map_a = induced_observation_map(a, obs_map)

    E = a.events
    Eo = E - obs_map_a.unobservable_events()
    h_ns, ns_state_sets = construct_nonsecret_spec(notion, E, Ens=Ens, Eo=Eo, joint=joint, **spec_kwargs)

    a_so = construct_secret_observer(a, h_ns, ns_state_sets, joint, obs_map_a)

    # Delete artificial initial state introduced by label transform
    so_init = a_so.vs.select(init=True)
    for e in a_so.es.select(_source_in=so_init.indices):
        a_so.vs[e.target]['init'] = True
    a_so.delete_vertices(so_init)
    a_so.events = a_so.events - {'e_init'}
    a_so.generate_out()

    return a_so


def is_obs_state_secret(state, ns_state_sets, joint):
    if joint:
        return state['marked'] and all([any([all([
            (pair[1] not in ns_states)
            for pair in state["name"] if pair[0] == q])
            for ns_states in ns_state_sets])
            for q in [pair[0] for pair in state["name"]]])
    else:
        return state['marked'] and any([all([
                (pair[1] not in ns_states)
                for pair in state["name"]])
                for ns_states in ns_state_sets])


def tmp_verify_edit_opacity(g, edit, public=False, obs_map=None, notion='CSO', joint=False,
                            k=1, **spec_kwargs):

    a_so_list = []
    if joint or notion != 'KSTEP':
        a_so_list.append(construct_secret_observer_label_transform(g, obs_map=obs_map, notion=notion,
                                                                   joint=joint, k=k, **spec_kwargs))
    else:
        for i in range(k+1):
            a_so_list.append(construct_secret_observer_label_transform(g, obs_map=obs_map,
                                                                       notion='KDELAY', joint=joint,
                                                                       k=i, **spec_kwargs))
    edit_map = NonDetDynamicMask(edit)
    edited_obs_map = obs_map.compose(edit_map)

    for a_so in a_so_list:
        violated = False
        if public:
            a_so.vs['marked'] = [not x for x in a_so.vs['marked']]
            edited_ns = edited_obs_map.apply_obs_map(a_so)
            a_so.vs['marked'] = True
            edited_reg = edited_obs_map.apply_obs_map(a_so)
            violated = not language_inclusion(edited_reg, edited_ns, edited_reg.events - edited_reg.Euo)
        else:
            a_so.vs['marked'] = [not x for x in a_so.vs['marked']]
            tmp = a_so.copy()
            tmp.vs['marked'] = True
            edited_reg = edited_obs_map.apply_obs_map(tmp)
            violated = not language_inclusion(edited_reg, a_so, edited_reg.events - edited_reg.Euo)
        if violated:
            return False
    return True
