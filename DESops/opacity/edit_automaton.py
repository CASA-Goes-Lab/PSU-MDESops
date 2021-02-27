"""
Functions relating to edit automata
Depracated?!?!?!?!
"""
from DESops.automata.NFA import NFA
from DESops.opacity.secret_observer import verify_opacity_secret_observer
import DESops.SDA.event_extensions as ee
from DESops.opacity.language_functions import language_inclusion
from DESops.opacity.observation_map import StaticMask

'''
def construct_edited_system(g, edit, obs_map, editPriority=True):
    """

    """
    if not is_valid_edit_automaton(edit):
        raise ValueError('Not a valid edit automaton')

    g_comp = NFA()

    # Intermediate storage for g_comp vertices and edges

    index = 0

    # Storage for vertex pairs
    g_comp_vert = []
    g_comp_vert_mark = []
    g_comp_vert_init = []
    g_comp_vert_sec = []

    g_comp_edges = []
    g_comp_edge_labels = []

    next_states_to_check = []

    def add_state_pair(new_pair):
        if new_pair not in g_comp_vert:
            # this is a new vertex pair: add it to the dict with value 'index'
            # index just makes it easier later to map edge names from key to index
            g_comp_vert.append(new_pair)
            g_comp_vert_init.append(g.vs[new_pair[0]]["init"] and edit.vs[new_pair[1]]["init"])
            # check if this vertex pair should get marked
            g_comp_vert_mark.append(g.vs[new_pair[0]]["marked"] and edit.vs[new_pair[1]]["marked"])
            g_comp_vert_sec.append(g.vs[new_pair[0]]["secret"])
            # need to check the new states' neighbors
            new_index = len(g_comp_vert)-1
            next_states_to_check.append(new_index)
            return new_index
        else:
            return g_comp_vert.index(new_pair)

    def add_pair_edge(source_ind, dest_pair, label):
        new_ind = add_state_pair(dest_pair)
        g_comp_edges.append((source_ind, new_ind))
        g_comp_edge_labels.append(label)

    if "init" not in g.vs.attributes():
        g.vs["init"] = False
        g.vs[0]["init"] = True
    if "init" not in edit.vs.attributes():
        edit.vs["init"] = False
        edit.vs[0]["init"] = True

    for v1 in g.vs.select(init=True):
        for v2 in edit.vs.select(init=True):
            add_state_pair((v1.index, v2.index))

    # set next_states_to_check returns False when empty
    while next_states_to_check:
        cur_ind = next_states_to_check.pop()
        vert_pair = g_comp_vert[cur_ind]
        # Iterate through all new synchronized states found in last iteration, checking neighbors
        # select edges with source at current vertex
        g_es = g.es(_source=vert_pair[0])
        edit_es = edit.es(_source=vert_pair[1])

        if any([ee.is_inserted(e['label']) for e in edit_es]):
            for e in edit_es:
                new_vert_pair = (vert_pair[0], e.target)
                add_pair_edge(cur_ind, new_vert_pair, e['label'])
        else:
            for e in g_es:
                unedited = [edit_e for edit_e in edit_es
                            if edit_e['label'] == ee.unedited_event(e['label'])]
                deleted = [edit_e for edit_e in edit_es
                           if edit_e['label'] == ee.deleted_event(e['label'])]
                if not unedited and not deleted:
                    new_vert_pair = (e.target, vert_pair[1])
                    add_pair_edge(cur_ind, new_vert_pair, ee.unedited_event(e['label']))
                else:
                    for edit_e in unedited:
                        new_vert_pair = (e.target, edit_e.target)
                        add_pair_edge(cur_ind, new_vert_pair, edit_e['label'])
                    for edit_e in deleted:
                        new_vert_pair = (e.target, edit_e.target)
                        add_pair_edge(cur_ind, new_vert_pair, edit_e['label'])

    g_comp.add_vertices(len(g_comp_vert), g_comp_vert)
    g_comp.vs['marked'] = g_comp_vert_mark
    g_comp.vs['init'] = g_comp_vert_init
    g_comp.vs['secret'] = g_comp_vert_sec
    g_comp.add_edges(g_comp_edges, g_comp_edge_labels)

    # construct the new observation map
    g_comp.generate_out()

    edit_obs_map = StaticMask({e.label if ee.is_inserted(e) or ee.is_unedited(e)
                               else StaticMask.epsilon for e in g_comp.events})

    new_obs_map = edit_obs_map.compose(obs_map)
    return g_comp, new_obs_map


def is_valid_edit_automaton(edit):

    return not any([any([ee.is_deleted(e['label']) or ee.is_unedited(e['label']) for e in edit.es(_source=v)]) and
                    any([ee.is_inserted(e['label']) for e in edit.es(_source=v)]) for v in edit.vs])



def verify_opacity_edit(g, edit, obs_map, public=True,
                        notion='CSO', joint=True,
                        k=1, secret_type=1):

    g_edit, obs_map_edit = construct_edited_system(g, edit, obs_map)
    if public:
        g_edit_so = construct_secret_observer_state_based(g_edit, obs_map_edit, notion, joint, k, secret_type)
        return verify_opacity_secret_observer(g_edit_so)
    else:
        g_so = construct_secret_observer_state_based(g, obs_map, notion, joint, k, secret_type)
        so_init = g_so.vs.select(init=True)
        for e in g_so.es.select(_source=0):
            g_so.vs[e.target]['init'] = True
        g_so.delete_vertices(so_init)
        g_so.vs['marked'] = [not b for b in g_so.vs['marked']]
        g_edit_obs = apply_obs_map(g_edit, obs_map_edit)
        g_edit_obs.vs['marked'] = True
        return language_inclusion(g_edit_obs, g_so, g_edit_obs.events - {''})


'''
