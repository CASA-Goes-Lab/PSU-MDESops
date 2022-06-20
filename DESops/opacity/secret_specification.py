"""
Functions related to specification of secrets for opacity

Construction of specification automata as described in
"A general language-based framework for specifying and verifying notions of opacity"
by Andrew Wintenberg, Matthew Blischke, Stéphane Lafortune, Necmiye Ozay
"""
from DESops.automata.NFA import NFA
from DESops.opacity.opacity import OpacityNotion

initial_event = 'e_init'

def current_state_spec(Ens, E):
    """
    Construct a current-state opacity specification automaton over the given event sets

    :param Ens: The nonsecret events
    :type Ens: set
    :param E: All events
    :type E: set
    :return: An automaton encoding nonsecret behavior
    :rtype: NFA
    """
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
    """
    Construct an initial-state opacity specification automaton over the given event sets

    :param Ens: The nonsecret events
    :type Ens: set
    :param E: All events
    :type E: set
    :return: An automaton encoding nonsecret behavior
    :rtype: NFA
    """
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


def k_delay_spec(secret_type, k, Ens, Eo, E):
    """
    Construct a specification automaton over the given event sets for the k-delayed nonsecret language

    :param secret_type: type 1 or type 2
    :type secret_type: int
    :param k: the delay
    :type k: int
    :param Ens: The nonsecret events
    :type Ens: set
    :param Eo: The observable events
    :type Eo: set
    :param E: All events
    :type E: set
    :return: An automaton encoding nonsecret behavior
    :rtype: NFA
    """

    h = _H_star(E)
    ns_state_sets = []

    # nonsecret bahvaior must occur K epochs ago
    ns_state_sets.append(_concatenate_union(h, _H_epoch_NS(secret_type, Ens, Eo, E)))
    # epochs 0 to K-1 steps ago don't matter
    for _ in range(0, k):
        ns_state_sets.append(_concatenate_union(h, _H_epoch_all(Eo, E)))

    h.vs["marked"] = True

    return h, ns_state_sets


def joint_infinite_step_spec(secret_type, Ens, Eo, E):
    """
    Construct a joint infinite step opacity specification automaton over the given event sets

    :param secret_type: type 1 or type 2
    :type secret_type: int
    :param Ens: The nonsecret events
    :type Ens: set
    :param Eo: The observable events
    :type Eo: set
    :param E: All events
    :type E: set
    :return: An automaton encoding nonsecret behavior
    :rtype: NFA
    """

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


def _concatenate_union(g, h):
    """
    Constructs an automaton that marks any string in either in h, or in the concatenation of g and h

    The resulting automaton overwrites the original g

    :param g: The first automaton
    :type g: Automata
    :param h: The second automaton
    :type h: Automata
    :return: The marked states of the resulting automaton
    :rtype: set
    """
    offset = g.vcount() - 1
    g.add_vertices(h.vcount() - 1)

    # TODO - can vectorize/group igraph commands for speedup
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


def _H_star(E):
    """
    Returns an automaton with a single state that marks all strings over the given event set

    :param E: All events
    :type E: set
    :return: The universal automaton
    :rtype: NFA
    """
    h = NFA()
    h.add_vertex()
    h.vs["init"] = [True]
    h.vs["marked"] = [True]

    h.add_edges([(0, 0)] * len(E), E)

    h.generate_out()
    return h


def _H_epoch_all(Eo, E):
    """
    Construct an automaton marking all epochs over the event sets

    :param Eo: The observable events
    :type Eo: set
    :param E: All events
    :type E: set
    :return: An automaton that marks any single epoch
    :rtype: NFA
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


def _H_epoch_NS(secret_type, Ens, Eo, E):
    """
    Construct an automaton marking nonsecret epochs

    :param secret_type: type 1 or type 2
    :type secret_type: int
    :param Ens: The nonsecret events
    :type Ens: set
    :param Eo: The observable events
    :type Eo: set
    :param E: All events
    :type E: set
    :return: an automaton that marks any single epoch in which nonsecret behavior occurs
    :rtype: NFA
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


# TODO - need to clean up interface for opacity
# functions are spread out between this file and language_functions.py
def construct_nonsecret_spec(notion, E, Ens=None, Eo=None,
                             joint=False, k=1, secret_type=1):
    """
    Construct a specification automaton for the given notion of nonsecret behavior and other parameters

    :param notion: The corresponding type of opacity
    :type notion: OpacityNotion
    :param Ens: The nonsecret events
    :type Ens: set
    :param Eo: The observable events
    :type Eo: set
    :param E: All events
    :type E: set
    :param joint: Whether or not to interpret classes jointly (vs. separately)
    :type joint: bool
    :param k: the number of steps for K-step or k-delay opacity
    :type k: int
    :param secret_type: type 1 or type 2 (for K-step and infinite step opacity)
    :type secret_type: int
    :return: The nonsecret specification automaton
    :rtype: NFA
    """
    h_ns = None
    ns_state_sets = None
    if notion == OpacityNotion.CSO:
        h_ns, ns_state_sets = current_state_spec(Ens, E)
    elif notion == OpacityNotion.ISO:
        h_ns, ns_state_sets = initial_state_spec(Ens, E)
    elif notion == OpacityNotion.KSTEP:
        h_ns, ns_state_sets = k_delay_spec(secret_type, k, Ens, Eo, E)
    elif notion == OpacityNotion.KDELAY:
        if joint:
            print("Warning: K-delayed secrets should be used for separate opacity.")
        h_ns, ns_state_sets = k_delay_spec(secret_type, k, Ens, Eo, E)
        ns_state_sets = [ns_state_sets[-1]]
    elif notion == OpacityNotion.INFSTEP:
        if not joint:
            raise ValueError("Separate infinite-step opacity is not implemented")
        h_ns, ns_state_sets = joint_infinite_step_spec(secret_type, Ens, Eo, E)
    else:
        raise ValueError("Unrecognized notion of opacity")

    return h_ns, ns_state_sets
