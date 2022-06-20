from DESops.automata.NFA import NFA
from DESops.opacity.observation_map import StaticMask

initial_event = 'e_init'


def label_transform(g, attribute_list, attributes_to_label):
    """
    Transform an automaton with state attributes to an automaton with events augmented by these labels

    :param g: The automaton with secret states to transform
    :type g: Automata
    :param attribute_list: Vertex attributes of the automaton to transform
    :type attribute_list: list
    :param attributes_to_label: Function mapping attribute values to label
    :type attributes_to_label: Callable
    :return: The transformed automaton
    :rtype: NFA
    """
    a = NFA()
    a.add_vertices(g.vcount() + 1)

    a.vs["init"] = False
    a.vs[g.vcount()]["init"] = True

    a.vs['name'] = ['q_init'] + g.vs['name']

    # create new initial state that leads to old initial states via e_init
    init_pairs = [(g.vcount(), v.index) for v in g.vs.select(init=True)]
    init_labels = [(initial_event, attributes_to_label(*[v[attr] for attr in attribute_list])) for v in g.vs.select(init=True)]
    a.add_edges(init_pairs, init_labels)

    # all vertices except the initial one should be marked, because we should always have an e_init event
    a.vs['marked'] = [False] + g.vs['marked']

    new_pairs = [(e.source, e.target) for e in g.es]
    new_labels = [(e['label'], attributes_to_label(*[g.vs[e.target][attr] for attr in attribute_list])) for e in g.es]
    a.add_edges(new_pairs, new_labels)

    a.generate_out()
    return a


def transform_secret_labels(g):
    """
    Transform the secret state labels of an automaton to its events

    :param g: The automaton with secret states to transform
    :type g: Automata
    :return: The transformed automaton, nonsecret events, and initial events
    :rtype: (NFA, set, set)
    """

    a = label_transform(g, ['secret'], lambda secret: 'S' if secret else 'NS')
    Ens = {e for e in a.es['label'] if e[1] == 'NS'}
    Einit = {e for e in a.es['label'] if e[0] == initial_event}
    return a, Ens, Einit


def induced_observation_map(a, obs_map):
    """
    Map an observation map on an automaton g to an observation map on it label transform a

    The provided observation map on g is assumed to only depend on events of g

    :param a: The label transform of the system
    :type a: Automata
    :param obs_map: The observation map of the original system
    :type obs_map: ObservationMap
    :return: An induced observation map on the label transformed system
    :rtype: ObservationMap
    """
    input_projection = StaticMask({e: e[0] for e in a.es['label']})
    tmp = obs_map.copy()
    tmp.prepend_observation(initial_event, initial_event)
    comp = input_projection.compose(tmp)
    return comp
