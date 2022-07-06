"""
Operations involving transducer automata with events represented by pairs (e_in, e_out)
"""
from DESops.automata import NFA
from DESops.basic_operations.unary import find_inacc

# TODO use new convention for empty event/string when one is developed

def generic_product(g, h, state_attr_list, state_attr_map, edge_label_map,
                    h_only_trans, g_only_trans, bfs=True):
    """
    Compute a generic product of two automata with the provided semantics.

    The product is computed with a breadth-first search over pairs of states of `g` and `h`,
    starting with the initial states of `g` and `h`.
    The attributes of the pair of states are computed by applying the provided map `state_attr_map`
    to the attributes in the `attr_list` of the states in the pair.
    Given an outgoing edge from each state in the current pair, an edge is added
    to the product system if it is allowed by the output of `edge_label_map` applied to the labels of each edge.
    The first component of this output is whether the edge should be added, while the second is the resulting label.
    Edges in the product system where only one system transitions are enabled with
    `allow_g_None_trans` and `allow_h_None_trans`.

    Transitions where neither system moves are never allowed

    Parameters:
    g: The first automaton for the product
    h: The second automaton for the product
    state_attr_list: The list of state attributes in the product
    state_attr_map: The map from the attributes of a state of g and a state of h to the attributes in the product state
    edge_label_map: The map from the pairs of labels of a transitions of g and of h to whether the product transition
                    should be allowed and what the corresponding product label is
    allow_g_None_trans: whether or not to allow a transition where g does not move but h does
    allow_h_None_trans: whether or not to allow a transition where h does not move but g does
    bfs: If True, then construct the product in a breadth-first search manner. If False, then in a parallel manner

    Returns: the product of g and h

    """
    if bfs:
        return _generic_product_bfs(g, h, state_attr_list, state_attr_map, edge_label_map,
                                    h_only_trans, g_only_trans)
    else:
        return _generic_product_parallel(g, h, state_attr_list, state_attr_map, edge_label_map,
                                         h_only_trans, g_only_trans)


def _generic_product_bfs(g, h, state_attr_list, state_attr_map, edge_label_map,
                         h_only_trans, g_only_trans):
    state_list = {}
    state_attr = {attr: [] for attr in state_attr_list}

    edge_list = []
    edge_labels = []

    next_states_to_check = []

    def add_state_pair(new_pair):
        if new_pair not in state_list:
            new_index = len(state_list)
            state_list[new_pair] = new_index
            new_attr = state_attr_map(g.vs[new_pair[0]], h.vs[new_pair[1]])
            for attr in state_attr_list:
                state_attr[attr].append(new_attr[attr])
            next_states_to_check.append(new_pair)
            return new_index
        else:
            return state_list[new_pair]

    def add_pair_edge(source_pair, dest_pair, g_label, h_label):
        add_edge, edge_label = edge_label_map(g_label, h_label)
        if add_edge:
            cur_ind = state_list[source_pair]
            new_ind = add_state_pair(dest_pair)
            edge_list.append((cur_ind, new_ind))
            edge_labels.append(edge_label)

    for v1 in g.vs.select(init=True):
        for v2 in h.vs.select(init=True):
            add_state_pair((v1.index, v2.index))

    # set next_states_to_check returns False when empty
    while next_states_to_check:
        vert_pair = next_states_to_check.pop()
        # Iterate through all new synchronized states found in last iteration, checking neighbors
        # select edges with source at current vertex
        g_es = g.es(_source=vert_pair[0])
        h_es = h.es(_source=vert_pair[1])

        for eg in g_es:
            for eh in h_es:
                dest_pair = (eg.target, eh.target)
                add_pair_edge(vert_pair, dest_pair, eg['label'], eh['label'])
            if g_only_trans:
                dest_pair = (eg.target, vert_pair[1])
                add_pair_edge(vert_pair, dest_pair, eg['label'], None)
        if h_only_trans:
            for eh in h_es:
                dest_pair = (vert_pair[0], eh.target)
                add_pair_edge(vert_pair, dest_pair, None, eh['label'])
            """
            # Transitions where neither system move are never allowed
            if allow_h_None_trans:
                add_pair_edge(vert_pair, vert_pair, None, None)
            """

    g_comp = NFA()

    g_comp.add_vertices(len(state_list), names=list(state_list.keys()), **state_attr)
    g_comp.add_edges(edge_list, edge_labels)
    g_comp.generate_out()
    return g_comp


def _generic_product_parallel(g, h, state_attr_list, state_attr_map, edge_label_map,
                              h_only_trans, g_only_trans):

    state_list = {(vg, vh): vg * h.vcount() + vh for vg in range(g.vcount()) for vh in range(h.vcount())}
    state_attr = {attr: [state_attr_map(vg, vh)[attr] for vg in g.vs for vh in h.vs] for attr in state_attr_list}

    edges = [((eg.source * h.vcount() + eh.source,
               eg.target * h.vcount() + eh.target), v[1])
             for eg in g.es for eh in h.es for v in (edge_label_map(eg["label"], eh["label"]),) if v[0]]
    if h_only_trans:
        edges += [((vg * h.vcount() + eh.source,
                    vg * h.vcount() + eh.target), v[1])
                  for vg in g.vs.indices for eh in h.es for v in (edge_label_map(None, eh["label"]),) if v[0]]
    if g_only_trans:
        edges += [((eg.source * h.vcount() + vh,
                    eg.target * h.vcount() + vh), v[1])
                  for eg in g.es for vh in h.vs.indices for v in (edge_label_map(eg["label"], None),) if v[0]]

    edge_list, edge_labels = tuple(zip(*edges))

    g_comp = NFA()

    g_comp.add_vertices(len(state_list), names=list(state_list.keys()), **state_attr)
    g_comp.add_edges(edge_list, edge_labels)
    g_comp.generate_out()

    # delete inaccessible states
    #g_comp.delete_vertices(g_comp.vs.select((list(find_inacc(g_comp, set())))))
    return g_comp


def transducer_auto_product(t, g, t_attr_list=None, g_attr_list=None,
                    allow_g_None_trans=True, allow_h_None_trans=True):
    """
    Compute an automaton where the labels of g are replaced according to the transducer t
    """
    if not t_attr_list:
        t_attr_list = set()
    if not g_attr_list:
        g_attr_list = set()
    state_attr_list = {'init', 'marked'} | t_attr_list | g_attr_list

    def state_attr_map(gs, hs):
        return {'marked': gs['marked'] and hs['marked'],
                'init': gs['init'] and hs['init']} | \
               {attr: gs[attr] for attr in t_attr_list} | \
               {attr: hs[attr] for attr in g_attr_list}

    def edge_label_map(ge, he):
        if not ge:
            return he == '', ''
        elif not he:
            return ge[0] == '', ge[1]
        else:
            return ge[0] == he, ge[1]

    return generic_product(t, g, state_attr_list, state_attr_map, edge_label_map,
                           allow_g_None_trans, allow_h_None_trans)


def transducer_transducer_product(t, g, t_attr_list=None, g_attr_list=None,
                    allow_g_None_trans=True, allow_h_None_trans=True):
    """
    Compute a transducer where the inputs of t are mapped to corresponding outputs in g
    """
    if not t_attr_list:
        t_attr_list = set()
    if not g_attr_list:
        g_attr_list = set()
    state_attr_list = {'init', 'marked'} | t_attr_list | g_attr_list

    def state_attr_map(gs, hs):
        return {'marked': gs['marked'] and hs['marked'],
                'init': gs['init'] and hs['init']} | \
               {attr: gs[attr] for attr in t_attr_list} | \
               {attr: hs[attr] for attr in g_attr_list}

    def edge_label_map(ge, he):
        if not ge:
            return he[0] == '' and he[1] == '', ('', '')
        elif not he:
            return ge[0] == '', ('', ge[1])
        else:
            return ge[0] == he[1], (he[0], ge[1])

    return generic_product(t, g, state_attr_list, state_attr_map, edge_label_map,
                           allow_g_None_trans, allow_h_None_trans)


def auto_auto_product(g, h, g_attr_list=None, h_attr_list=None,
                    allow_g_None_trans=True, allow_h_None_trans=True, bfs=True):
    """
    Compute the usual synchronous product of automata
    """
    if not h_attr_list:
        h_attr_list = set()
    if not g_attr_list:
        g_attr_list = set()
    state_attr_list = {'init', 'marked'} | h_attr_list | g_attr_list

    def state_attr_map(gs, hs):
        return {'marked': gs['marked'] and hs['marked'],
                'init': gs['init'] and hs['init']} | \
               {attr: gs[attr] for attr in g_attr_list} | \
               {attr: hs[attr] for attr in h_attr_list}

    def edge_label_map(ge, he):
        if not ge:
            return he == '', ''
        elif not he:
            return ge == '', ''
        else:
            return ge == he, ge

    return generic_product(g, h, state_attr_list, state_attr_map, edge_label_map,
                           allow_g_None_trans, allow_h_None_trans, bfs)


def auto_auto_parallel_comp(g, h, g_attr_list=None, h_attr_list=None,
                    allow_g_None_trans=True, allow_h_None_trans=True, bfs=True):
    """
    Compute the usual parallel composition or asynchronous product of automata
    """
    common_events = g.events & h.events
    if '' in common_events:
        common_events.remove('')

    if not h_attr_list:
        h_attr_list = set()
    if not g_attr_list:
        g_attr_list = set()
    state_attr_list = {'init', 'marked'} | h_attr_list | g_attr_list

    def state_attr_map(gs, hs):
        return {'marked': gs['marked'] and hs['marked'],
                'init': gs['init'] and hs['init']} | \
               {attr: gs[attr] for attr in g_attr_list} | \
               {attr: hs[attr] for attr in h_attr_list}

    def edge_label_map(ge, he):
        if not ge:
            return he not in common_events, he
        elif not he:
            return ge not in common_events, ge
        else:
            return ge == he, ge

    return generic_product(g, h, state_attr_list, state_attr_map, edge_label_map,
                           allow_g_None_trans, allow_h_None_trans, bfs)


def transducer_input_automaton(t):
    """
    Construct an automaton representing the input language of the transducer t
    """
    g = t.copy()
    g.events = set()
    g.es['label'] = [e[0] for e in g.es['label']]
    g.generate_out()
    return g


def transducer_output_automaton(t):
    """
    Construct an automaton representing the output language of the transducer t
    """
    g = t.copy()
    g.events = set()
    g.es['label'] = [e[1] for e in g.es['label']]
    g.generate_out()
    return g
