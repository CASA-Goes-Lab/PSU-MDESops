"""
Functions related to specification of secrets for opacity
"""
import warnings

from DESops.automata.event import Event
from DESops.automata.NFA import NFA


def transform_secret_state_based(g, orig_obs_map=None):
    '''
    Transform an automaton with secret state labels to an automaton with secret events.
    Additionally transform or construct the corresponding observation map.

    Parameters:
    g: The automaton with secret states to transform
    orig_obs_map: The static mask observation map for g, if None is provided then projection of unobservable events is used

    Returns:
    a: The transformed automaton
    Ens: The nonsecret events of a
    Eo: The observable events of a
    obs_map: The static mask observation map for a
    '''
    a = NFA()
    a.add_vertices(g.vcount() + 1)
    obs_map = {}
    Ens = set()

    if not orig_obs_map:
        orig_obs_map = {e: '' if e in g.Euo else e for e in g.events}

    a.vs["init"] = False
    a.vs[0]["init"] = True

    a.vs['name'] = ['q_init'] + g.vs['name']

    # create new initial state that leads to old initial states via e_init
    # this means that vertex i in g is vertex i+1 in h
    for v in g.vs:
        if v["init"]:
            label = (Event("e_init"), v["secret"])
            if not v['secret']:
                Ens.add(label)
            obs_map[label] = 'e_init'

            a.add_edge(0, v.index + 1, label)

    # all vertices except the initial one should be marked, because we should always have an e_init event
    a.vs['marked'] = [False]+g.vs['marked']

    for t in g.es:
        label = (t["label"], t.target_vertex["secret"])
        if not t.target_vertex["secret"]:
            Ens.add(label)
        obs_map[label] = orig_obs_map[t['label']]
        a.add_edge(t.source + 1, t.target + 1, label)

    a.Euo = {e for e in obs_map.keys() if obs_map[e] == ''}
    a.generate_out()
    Eo = a.events - a.Euo
    return a, Ens, Eo, obs_map


def current_state_spec(Ens, E):
    '''
    Construct a current-state opacity specification automaton over the given event sets

    Parameters:
    Ens: The nonsecret events
    E: All events

    Returns: a current-state opacity nonsecret specification automaton
    '''
    Es = E - Ens

    h = NFA()

    h.add_vertices(2)
    h.vs["init"] = [True, False]
    h.vs["marked"] = True
    ns_state_sets = [{1}]

    h.add_edges([(0, 0)]*len(Es), Es)
    h.add_edges([(1, 0)]*len(Es), Es)
    h.add_edges([(0, 1)]*len(Ens), Ens)
    h.add_edges([(1, 1)]*len(Ens), Ens)

    h.generate_out()
    return h, ns_state_sets


def initial_state_spec(Ens, E):
    '''
    Construct an initial-state opacity specification automaton over the given event sets

    Parameters:
    Ens: The nonsecret events
    E: All events

    Returns: an initial-state opacity nonsecret specification automaton
    '''
    Es = E - Ens

    h = NFA()

    h.add_vertices(3)
    h.vs["init"] = [True, False, False]
    ns_state_sets = [{1}]

    h.add_edges([(0, 1)]*len(Ens), Ens)
    h.add_edges([(0, 2)]*len(Es), Es)
    h.add_edges([(1, 1)]*len(E), E)
    h.add_edges([(2, 2)]*len(E), E)

    h.vs['marked'] = True
    h.generate_out()
    return h, ns_state_sets

def k_step_spec(secret_type, k, Ens, Eo, E):
    '''
    Construct a specification automaton over the given event sets
    for the k-delayed nonsecret language

    Parameters:
    secret_type: 1 or 2
    k: The 'delay'
    Ens: The nonsecret events
    Eo: The observable events
    E: All events

    Returns: a k-delayed nonsecret specification automaton
    '''
    h = H_star(E)
    ns_state_sets = []

    # nonsecret bahvaior must occur K epochs ago
    ns_state_sets.append(concatenate_union(h, H_epoch_NS(secret_type, Ens, Eo, E)))
    # epochs 0 to K-1 steps ago don't matter
    for _ in range(0, k):
        ns_state_sets.append(concatenate_union(h, H_epoch_all(Eo, E)))

    h.vs["marked"] = True

    return h, ns_state_sets


def joint_infinite_step_spec(secret_type, Ens, Eo, E):
    '''
    Construct a joint infinite step opacity specification automaton over the given event sets

    Parameters:
    secret_type: 1 or 2
    Ens: The nonsecret events
    Eo: The observable events
    E: All events

    Returns: a current-state opacity nonsecret specification automaton
    '''
    Es = E - Ens
    Euo = E - Eo
    Enso = Ens & Eo
    Ensuo = Ens & Euo

    h = NFA()
    ns_state_sets = None
    if secret_type == 1:
        h.add_vertices(3)
        h.vs["init"] = [True, False, False]

        ns_state_sets = [{2}]

        h.add_edges([(1, 1)]*len(E), E)
        h.add_edges([(2, 1)]*len(E), E)
        h.add_edges([(2, 2)]*len(Ens), Ens)
        h.add_edges([(0, 2)]*len(Enso), Enso)
        h.add_edges([(0, 1)]*len(Eo), Eo)

    else:
        h.add_vertices(4)
        h.vs["init"] = [True, False, False, False]

        ns_state_sets = [{3}]

        h.add_edges([(1, 2)]*len(E), E)
        h.add_edges([(2, 2)]*len(E), E)
        h.add_edges([(1, 1)]*len(Euo), Euo)
        h.add_edges([(3, 3)]*len(Euo), Euo)
        h.add_edges([(1, 3)]*len(Ensuo), Ensuo)
        h.add_edges([(0, 1)]*len(Eo), Eo)
        h.add_edges([(3, 1)]*len(Eo), Eo)
        h.add_edges([(0, 3)]*len(Enso), Enso)
        h.add_edges([(3, 3)]*len(Enso), Enso)

    h.vs["marked"] = True
    h.generate_out()
    return h, ns_state_sets


def concatenate_union(g, h):
    """
    Constructs an automaton that marks any string in either in h, or in the concatenation of g and h

    The resulting automaton overwrites the original g

    Parameters:
    g: The first automaton
    h: The second automaton

    Returns: the resulting marked states
    """
    offset = g.vcount() - 1
    g.add_vertices(h.vcount() - 1)

    for t in h.es:
        if t.source == 0:
            # transitions from the initial state of h use marked states of g as their source
            for v in g.vs:
                if v["marked"]:
                    g.add_edge(v.index, t.target + offset, t["label"], fill_out=True)
        else:
            g.add_edge(t.source + offset, t.target + offset, t["label"], fill_out=True)

    # marked states correpsond to initial states in h
    for v in g.vs:
        if v["marked"]:
            v["init"] = True
        # fix vertices that didn't get marked as initial or non-initial
        if v["init"] is None:
            v["init"] = False

    # new marked states are those that are marked in h
    g.vs["marked"] = False
    ns_states = set()
    for v in h.vs:
        if v["marked"]:
            g.vs[v.index + offset]["marked"] = True
            ns_states.add(v.index + offset)
    return ns_states


def H_star(E):
    """
    Returns an automaton that marks all strings over the event set

    Parameters:
    E: The event set

    Returns: The universal automaton
    """
    h = NFA()
    h.add_vertex()
    h.vs["init"] = [True]
    h.vs["marked"] = [True]

    h.add_edges([(0, 0)] * len(E), E)

    h.generate_out()
    return h


def H_epoch_all(Eo, E):
    """
    Construct an automaton marking all epochs over the event sets

    Parameters:
    Eo: observable event set
    E: event set

    Returns: an automaton that marks any single epoch

    """
    Euo = E - Eo

    h = NFA()
    h.add_vertices(2)
    h.vs["init"] = [True, False]
    h.vs["marked"] = [False, True]

    h.add_edges([(0, 1)]*len(Eo), Eo)
    h.add_edges([(1, 1)]*len(Euo), Euo)

    h.generate_out()
    return h


def H_epoch_NS(secret_type, Ens, Eo, E):
    """
    Construct an automaton marking nonsecret epochs

    Parameters:
    Ens: nonsecret event set
    Eo: observable event set
    E: event set

    Returns: an automaton that marks any single epoch in which nonsecret behavior occurs

    """
    Euo = E - Eo
    Enso = Ens & Eo
    Ensuo = Ens & Euo

    h = NFA()

    if secret_type == 1:
        h.add_vertices(2)
        h.vs["init"] = [True, False]
        h.vs["marked"] = [False, True]
        h.add_edges([(0, 1)]*len(Enso), Enso)
        h.add_edges([(1, 1)]*len(Ensuo), Ensuo)

    else:
        h.add_vertices(3)
        h.vs["init"] = [True, False, False]
        h.vs["marked"] = [False, False, True]

        h.add_edges([(0, 1)]*len(Eo), Eo)
        h.add_edges([(0, 2)]*len(Enso), Enso)
        h.add_edges([(1, 1)]*len(Euo), Euo)
        h.add_edges([(2, 2)]*len(Euo), Euo)
        h.add_edges([(1, 2)]*len(Ensuo), Ensuo)

    h.generate_out()
    return h
