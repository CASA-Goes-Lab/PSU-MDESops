import DESops as d
import DESops.SDA.event_extensions as ee

try:
    from DESops.opacity.edisyn_interface import enforce_state_based_opacity_edisyn
    edisyn_available = True
except ImportError:
    edisyn_available = False

from DESops.opacity.secret_observer import construct_secret_observer_label_transform, tmp_verify_edit_opacity
from DESops.opacity.observation_map import StaticMask, NonDetDynamicMask
from DESops.opacity.language_functions import language_inclusion

import pytest


def test_edit_auto():
    g = d.NFA()
    g.add_vertices(2)
    g.add_edge(0, 1, 'a')
    g.add_edge(1, 0, 'd')
    g.vs['marked'] = True
    g.vs['secret'] = True
    g.vs['init'] = False
    g.vs[0]['init'] = True
    g.generate_out()

    obs_map = StaticMask({'a': 'a', 'd': 'b'})

    edit = d.NFA()
    edit.add_vertices(3)
    edit.vs['marked'] = True
    edit.vs['init'] = False
    edit.vs[0]['init'] = True
    edit.add_edge(0, 1, ('a', 'a'))
    edit.add_edge(1, 1, ('b', 'b'))
    edit.add_edge(1, 2, ('a', 'a'))
    edit.add_edge(2, 2, ('b', ''))
    edit.add_edge(2, 2, ('a', 'a'))
    edit.generate_out()

    edit_map = NonDetDynamicMask(edit)

    edited_obs_map = obs_map.compose(edit_map)

    edited_g = edited_obs_map.apply_obs_map(g)

    target_auto = d.NFA()
    target_auto.add_vertices(6)
    target_auto.vs['init'] = False
    target_auto.vs[0]['init'] = True
    target_auto.vs['marked'] = True
    target_auto.add_edges([(0,1),(1,2),(2,3),(3,4),(4,3)], ['a','b','a','','a'])
    target_auto.Euo = {''}
    target_auto.generate_out()
    assert language_inclusion(target_auto, edited_g, target_auto.events - target_auto.Euo)
    assert language_inclusion(edited_g, target_auto, target_auto.events - target_auto.Euo)


@pytest.mark.skipif(not edisyn_available, reason="EdiSyn not available")
def test_edisyn_edit():
    g = d.NFA()
    g.add_vertices(4)
    g.add_edge(0, 1, 'b')
    g.add_edge(1, 2, 'c')
    g.add_edge(0, 3, 'a')
    g.add_edge(3, 2, 'a')
    g.add_edge(2, 2, 'a')
    g.vs['marked'] = True
    g.vs['secret'] = False
    g.vs[3]['secret'] = True
    g.vs['init'] = False
    g.vs[0]['init'] = True
    g.generate_out()

    obs_map = StaticMask({'a': 'a', 'b': 'b', 'c': 'c'})

    utility = [(0,0),(1,1),(1,2),(2,2),(3,1),(3,2),(3,3)]
    edit = enforce_state_based_opacity_edisyn(g, utility, 'CSO', insertion_bound=2, obs_map=obs_map)

    assert (tmp_verify_edit_opacity(g=g, edit=edit, public=False, notion='CSO', obs_map=obs_map, joint=True))
    assert (tmp_verify_edit_opacity(g=g, edit=edit, public=True, notion='CSO', obs_map=obs_map, joint=True))


def test_edit_auto_pub_priv():
    '''
    Demonstrates that an edit function can enforce private but not public opacity.
    Here we manually define an edit automaton that has an insertion bound of 1 and does not allow deletion
    '''
    g = d.NFA()
    g.add_vertices(15)
    g.vs['marked'] = True
    g.vs['init'] = False
    g.vs[0]['init'] = True
    g.vs['secret'] = False
    g.vs[1]['secret'] = True
    g.vs[4]['secret'] = True
    g.vs[14]['secret'] = True
    g.add_edge(0, 1, 'a')
    g.add_edge(1, 2, 'a')
    g.add_edge(2, 2, 'd')
    g.add_edge(0, 3, 'a')
    g.add_edge(3, 4, 'b')
    g.add_edge(4, 2, 'a')
    g.add_edge(0, 5, 'c')
    g.add_edge(5, 6, 'c')
    g.add_edge(6, 7, 'a')
    g.add_edge(7, 8, 'b')
    g.add_edge(8, 9, 'a')
    g.add_edge(9, 9, 'd')
    g.add_edge(9, 10, 'c')
    g.add_edge(5, 11, 'a')
    g.add_edge(11, 12, 'b')
    g.add_edge(12, 13, 'a')
    g.add_edge(13, 13, 'd')
    g.add_edge(13, 14, 'c')

    obs_map = StaticMask({'a': 'a', 'b': 'b', 'c': 'c', 'd': 'd'})

    edit = d.NFA()
    edit.add_vertices(10)
    edit.vs['marked'] = True
    edit.vs['init'] = False
    edit.vs[0]['init'] = True
    '''
    In this way of representing an edit automaton, an insertion of 'a' after 'b'
    is represented by a deletion of 'b', followed by an insertion of 'a', ending with a reinsertion of 'a'
    '''
    edit.add_edge(0, 1, ('a', 'c'))
    edit.add_edge(1, 2, ('', 'a'))
    edit.add_edge(2, 3, ('a', 'b'))
    edit.add_edge(3, 4, ('', 'a'))
    edit.add_edge(4, 4, ('d', 'd'))
    edit.add_edge(2, 5, ('b', 'b'))
    edit.add_edge(5, 9, ('', 'a'))
    edit.add_edge(9, 4, ('a', ''))
    edit.add_edge(0, 6, ('c', 'c'))
    edit.add_edge(6, 7, ('a', 'c'))
    edit.add_edge(7, 8, ('', 'a'))
    edit.add_edge(6, 8, ('c', 'c'))
    edit.add_edge(8, 8, ('a', 'a'))
    edit.add_edge(8, 8, ('b', 'b'))
    edit.add_edge(8, 8, ('c', 'c'))
    edit.add_edge(8, 8, ('d', 'd'))

    privately_opaque = tmp_verify_edit_opacity(g=g, edit=edit, public=False, notion='KSTEP', k=1, obs_map=obs_map, joint=False)
    #publicly_opaque = tmp_verify_edit_opacity(g=g, edit=edit, public=True, notion='KSTEP', k=1, obs_map=obs_map, joint=False)
    assert privately_opaque
    #assert not publicly_opaque


if __name__ == '__main__':
    test_edit_auto()
    test_edisyn_edit()
    test_edit_auto_pub_priv()

