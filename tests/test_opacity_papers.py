from DESops.automata import NFA
from DESops.opacity import secret_observer as so
from DESops.opacity.secret_specification import OpacityNotion

# TODO - convert to using files instead of building the automata here
# TODO - convert references to doc format

def saboori_07_fig1a():
    """
    Automaton from Figure 1-a in "Notions of security and opacity in discrete event systems"
    This automaton is CSO, (weakly) 1-step opaque, and not (weakly) 2-step opaque
    """
    g = NFA()
    g.add_vertices(4,
                   init=[True, False, False, False],
                   marked=[True]*4,
                   secret=[False, True, False, False])
    g.add_edges([(0,0),(0,2),(1,0),(1,3),(2,1),(3,1)],
                ['a','uo','b','uo','a','b'])
    g.Euo = {'uo'}
    g.generate_out()
    return g


def test_saboori_07_fig1a():
    g = saboori_07_fig1a()
    g_so_1 = so.construct_secret_observer_label_transform(g, notion=OpacityNotion.KSTEP, k=1, joint=False, secret_type=2)
    assert so.verify_opacity_secret_observer(g_so_1)

    g_so_2 = so.construct_secret_observer_label_transform(g, notion=OpacityNotion.KSTEP, k=2, joint=False, secret_type=2)
    assert not so.verify_opacity_secret_observer(g_so_2)


def saboori_09_ex1():
    """
    Example 1 from "Verification of K-step opacity and analysis of its complexity"
    This example is not (weakly) 2-step opaque for these secret states
    """
    g = NFA()
    g.add_vertices(5,
                   init=[True, False, False, False, False],
                   marked=[True]*5,
                   secret=[True, False, False, False, False])
    g.add_edges([(0,1),(0,2),(0,3),(2,2),(1,4),(3,4),(4,4)],
                ['b', 'uo', 'a', 'b', 'b', 'b', 'a'])
    g.Euo = {'uo'}
    g.generate_out()
    return g


def test_saboori_09_ex1():
    g = saboori_09_ex1()

    g_so = so.construct_secret_observer_label_transform(g, notion=OpacityNotion.KSTEP, k=2, joint=False, secret_type=2)
    assert not so.verify_opacity_secret_observer(g_so)


def saboori_09_fig1b():
    """
    Automaton from Figure 1-b in "Verification of K-step opacity and analysis of its complexity"
    This example is (weakly) 2-step opaque
    This example is not (strongly) 2-step opaque
    """
    g = NFA()
    g.add_vertices(7,
                   init=[True]+[False]*6,
                   marked=[True]*7,
                   secret=[False, True, False, False, False, False, True])
    g.add_edges([(0, 1), (0, 2), (1, 3), (2, 4), (3, 5), (4, 6)],
                ['a', 'uo', 'uo', 'a', 'a', 'a'])
    g.Euo = {'uo'}
    g.generate_out()
    return g


def test_saboori_09_fig1b():
    g = saboori_09_fig1b()
    g_so_weak = so.construct_secret_observer_label_transform(g, notion=OpacityNotion.KSTEP, k=2, joint=False, secret_type=2)
    assert so.verify_opacity_secret_observer(g_so_weak)

    g_so_strong = so.construct_secret_observer_label_transform(g, notion=OpacityNotion.KSTEP, k=2, joint=True, secret_type=1)
    assert not so.verify_opacity_secret_observer(g_so_strong)


def saboori_11_fig1a():
    """
    Automaton from Figure 1-a in "Verification of Infinite-Step Opacity and Complexity Considerations"
    This automaton is not (weakly) infinite step opaque
    """
    g = NFA()
    g.add_vertices(5,
                   init=[True, False, False, False, False],
                   marked=[True]*5,
                   secret=[False, False, False, True, False])
    g.add_edges([(0,1),(0,2),(0,3),(2,2),(1,4),(3,4),(4,4)],
                ['b', 'uo', 'a', 'b', 'b', 'b', 'a'])
    g.Euo = {'uo'}
    g.generate_out()
    return g


def test_saboori_11_fig1a():
    g = saboori_11_fig1a()

    g_so_2 = so.construct_secret_observer_label_transform(g, notion=OpacityNotion.KSTEP, k=2, joint=False, secret_type=2)
    assert not so.verify_opacity_secret_observer(g_so_2)


def falcone_13_fig2a():
    """
    Automaton from Figure 2-a in "Runtime Enforcement of K-step Opacity"
    Also from Figure 2-a in "Enforcement and validation (at runtime) of various notions of opacity"
    This automaton is not CSO
    There exist "R-Enforcers" to enforce (weak) 1-step and 2-step opacity using delay
    """
    g = NFA()
    g.add_vertices(8,
                   names=["q0", "q0'", "q1", "q2", "q3", "q4", "q5", "q6"],
                   init=[True] + [False] * 7,
                   marked=[True]*8,
                   secret=[False, False, False, True, False, False, True, False])
    g.add_edges([(0, 0), (0, 1), (1, 2), (2, 3), (3, 4), (4, 4), (4, 4),
                 (0, 5), (5, 6), (6, 5), (6, 7), (7, 7), (7, 7)],
                ['b', 'tau', 'a', 'b', 'a', 'a', 'b',
                 'a', 'b', 'a', 'b', 'a', 'b'])
    g.Euo = {'tau'}
    g.generate_out()
    return g


def falcone_15_fig10a():
    """
    The delay enforcer from Figure 10-a in "Enforcement and validation (at runtime) of various notions of opacity"
    Enforces (weak) 1-step opacity for the automaton from Figure 2-a
    This edit function delays the observation of b^*ab by 2 steps
    """
    edit = NFA()
    edit.add_vertices(6)
    edit.vs['init'] = False
    edit.vs['init'] = True
    edit.vs['marked'] = True
    edit.add_edge(0, 0, ('b', 'b'))
    edit.add_edge(0, 1, ('a', 'a'))
    edit.add_edge(1, 2, ('b', ''))
    edit.add_edge(2, 3, ('a', ''))
    edit.add_edge(2, 4, ('b', ''))
    edit.add_edge(3, 5, ('a', 'b', 'a', 'a'))
    edit.add_edge(3, 5, ('b', 'b', 'a', 'b'))
    edit.add_edge(4, 5, ('a', 'b', 'b', 'a'))
    edit.add_edge(4, 5, ('b', 'b', 'b', 'b'))
    edit.add_edge(5, 5, ('a', 'a'))
    edit.add_edge(5, 5, ('b', 'b'))
    edit.Euo = {''}
    return edit


def test_falcone_13_fig2a():
    g = falcone_13_fig2a()
    g_so = so.construct_secret_observer_label_transform(g, notion=OpacityNotion.CSO)
    assert not so.verify_opacity_secret_observer(g_so)

    edit = falcone_15_fig10a()
    assert so.tmp_verify_edit_opacity(g, edit, public=True, notion=OpacityNotion.KSTEP, k=1, joint=False, secret_type=2)
    assert not so.tmp_verify_edit_opacity(g, edit, public=False, notion=OpacityNotion.KSTEP, k=1, joint=False, secret_type=2)


def falcone_13_fig2b():
    """
    Automaton from Figure 2-b in "Runtime Enforcement of K-step Opacity"
    Also from Figure 2-b in "Enforcement and validation (at runtime) of various notions of opacity"
    This automaton is (weakly) 1-step opaque but not (weakly) 2-step opaque
    There exist "R-Enforcers" to enforce (weak) 1-step and 2-step opacity using delay
    """
    g = NFA()
    g.add_vertices(6,
                   names=["q0", "q1", "q2", "q3", "q4", "q5"],
                   init=[True] + [False] * 5,
                   marked=[True]*6,
                   secret=[False, False, True, False, False, False])
    g.add_edges([(0, 1), (1, 2), (2, 3), (3, 3), (0, 4), (4, 5), (5, 5)],
                ['tau', 'a', 'b', 'a', 'a', 'b', 'b'])
    g.Euo = {'tau'}
    g.generate_out()
    return g


def test_falcone_13_fig2b():
    g = falcone_13_fig2b()
    g_so_1 = so.construct_secret_observer_label_transform(g, notion=OpacityNotion.KSTEP, k=1, joint=False, secret_type=2)
    assert so.verify_opacity_secret_observer(g_so_1)
    g_so_2 = so.construct_secret_observer_label_transform(g, notion=OpacityNotion.KSTEP, k=2, joint=False, secret_type=2)
    assert not so.verify_opacity_secret_observer(g_so_2)


def falcone_15_fig2c():
    """
    From Figure 2-c in "Enforcement and validation (at runtime) of various notions of opacity"
    This automaton is (weakly) K-step opaque for all K, but not (strongly) 1-step opaque
    """
    g = NFA()
    g.add_vertices(8,
                   names=["q0", "q1", "q2", "q3", "q4", "q5", "q6", "q7"],
                   init=[True] + [False] * 7,
                   marked=[True]*8,
                   secret=[False, False, True, False, False, False, True, False])
    g.add_edges([(0, 1), (1, 2), (2, 3), (3, 4), (4, 4),
                 (0, 5), (5, 6), (6, 7), (7, 7)],
                ['tau', 'a', 'b', 'a', 'a', 'a', 'b', 'a', 'a'])
    g.Euo = {'tau'}
    g.generate_out()
    return g


def test_falcone_15_fig2c():
    g = falcone_15_fig2c()
    g_so_weak = so.construct_secret_observer_label_transform(g, notion=OpacityNotion.KSTEP, k=3, joint=False, secret_type=2)
    assert so.verify_opacity_secret_observer(g_so_weak)
    g_so_strong = so.construct_secret_observer_label_transform(g, notion=OpacityNotion.KSTEP, k=1, joint=True, secret_type=1)
    assert not so.verify_opacity_secret_observer(g_so_strong)


def falcone_15_fig2d():
    """
    From Figure 2-d in "Enforcement and validation (at runtime) of various notions of opacity"
    This automaton (weakly) K-step opaque for all K
    The paper claims it is (strongly) 1-step opaque, but it seems the secret is revealed after observing abac
    It instead appears to not be (strongly) 1-step or 2-step opaque
    """
    g = NFA()
    g.add_vertices(8,
                   names=["q0", "q1", "q2", "q3", "q4", "q5", "q6", "q7"],
                   init=[True] + [False] * 7,
                   marked=[True]*8,
                   secret=[False, False, True, False, False, False, False, True])
    g.add_edges([(0, 1), (1, 2), (2, 3), (3, 4), (4, 2),
                 (0, 5), (5, 6), (6, 7), (7, 5)],
                ['tau', 'a', 'b', 'a', 'c', 'a', 'b', 'a', 'c'])
    g.Euo = {'tau'}
    g.generate_out()
    return g


def test_falcone_15_fig2d():
    g = falcone_15_fig2d()
    """
    # Fails
    g_so_1 = so.construct_secret_observer_label_transform(g, notion=OpacityNotion.KSTEP, k=1, joint=True, secret_type=1)
    assert so.verify_opacity_secret_observer(g_so_1)
    """
    g_so_2 = so.construct_secret_observer_label_transform(g, notion=OpacityNotion.KSTEP, k=2, joint=True, secret_type=1)
    assert not so.verify_opacity_secret_observer(g_so_2)


def falcone_15_fig2e():
    """
    From Figure 2-e in "Enforcement and validation (at runtime) of various notions of opacity"
    This automaton is not (strongly) 2-step opaque
    Strong 2-step opacity can be enforced with an "R-enforcer" using delay
    """
    g = NFA()
    g.add_vertices(4,
                   names=["q0", "q1", "q2", "q3"],
                   init=[True] + [False] * 3,
                   marked=[True]*4,
                   secret=[False, False, True, False])
    g.add_edges([(0, 1), (1, 1), (0, 2), (2, 2), (2, 3), (3, 0), (3, 3)],
                ['a', 'b', 'tau', 'a', 'b', 'a', 'b'])
    g.Euo = {'tau'}
    g.generate_out()
    return g


def falcone_15_fig10b():
    """
    The delay enforcer from Figure 10-b in "Enforcement and validation (at runtime) of various notions of opacity"
    Enforces (strong) 2-step opacity for the automaton from Figure 2-e
    """
    edit = NFA()
    edit.add_vertices(21)
    edit.vs['init'] = False
    edit.vs[0]['init'] = True
    edit.vs['marked'] = True
    edit.add_edge(0, 1, ('a', 'a')) # () -> ()
    edit.add_edge(0, 2, ('b', '')) # () -> b2
    edit.add_edge(1, 3, ('b', 'b')) # () -> ()
    edit.add_edge(1, 13, ('a', '')) # () -> a3
    edit.add_edge(2, 4, ('a', '')) # b2 -> a1 b1
    edit.add_edge(2, 5, ('b', '')) # b2 -> b1 b1
    edit.add_edge(3, 6, ('a', '')) # () -> a1)
    edit.add_edge(3, 7, ('b', '')) # () -> ()
    edit.add_edge(4, 8, ('a', 'b', 'a', 'a')) # a1 b1 -> ()
    edit.add_edge(4, 9, ('a', 'b', 'a', 'b')) # a1 b1 -> ()
    edit.add_edge(5, 10, ('a', 'b', 'b')) # b1 b1 -> a1
    edit.add_edge(5, 11, ('b', 'b', 'b', 'b')) # b1 b1 -> ()
    edit.add_edge(6, 8, ('a', 'a', 'a')) # a1 -> ()
    edit.add_edge(6, 9, ('b', 'a', 'b')) # a1 -> ()
    edit.add_edge(7, 10, ('a', '')) # () -> a1
    edit.add_edge(7, 12, ('b', 'b')) # () -> ()
    edit.add_edge(8, 11, ('a', 'a')) # () -> ()
    edit.add_edge(8, 3, ('b', 'b')) # () -> ()
    edit.add_edge(9, 4, ('a', '')) # () -> a1
    edit.add_edge(9, 5, ('b', '')) # () -> b1
    edit.add_edge(10, 8, ('a', 'a', 'a')) # a1 -> ()
    edit.add_edge(10, 9, ('b', 'a', 'b')) # a1 -> ()
    edit.add_edge(11, 10, ('a', '')) # () -> ()
    edit.add_edge(11, 11, ('b', 'b')) # () -> ()
    edit.add_edge(12, 10, ('a', '')) # () -> a1
    edit.add_edge(12, 12, ('b', 'b')) # () -> ()
    edit.add_edge(13, 14, ('a', '')) # a3 -> a3 a2
    edit.add_edge(13, 15, ('b', '')) # a3 -> b2 a2
    edit.add_edge(14, 17, ('a', '')) # a3 a2 -> a3 a2 a1
    edit.add_edge(14, 18, ('b', '')) # a3 a2 -> b2 a2 a1
    edit.add_edge(15, 20, ('a', '')) # b2 a2 -> a1 b1 a1
    edit.add_edge(15, 16, ('b', '')) # b2 a2 -> b1 b1 a1
    edit.add_edge(16, 6, ('a', 'a', 'b', 'b')) # b1 b1 a1 -> a1
    edit.add_edge(16, 19, ('b', 'a', 'b', 'b')) # b1 b1 a1 -> b1
    edit.add_edge(20, 8, ('a', 'a', 'b', 'a', 'a')) # a1 b1 a1 -> ()
    edit.add_edge(20, 9, ('b', 'a', 'b', 'a', 'b')) # aba -> ()
    edit.add_edge(17, 17, ('a', 'a')) # a3 a2 a1 -> a3 a2 a1
    edit.add_edge(17, 18, ('b', 'a')) # a3 a2 a1 -> b2 a2 a1
    edit.add_edge(18, 20, ('a', 'a')) # b2 a2 a1 -> a1 b1 a1
    edit.add_edge(18, 16, ('b', 'a')) # b2 a2 a1 -> b1 b1 a1
    edit.add_edge(19, 19, ('b', 'b')) # b1 -> b1
    edit.add_edge(19, 6, ('a', 'b')) # b1 -> a1
    # x14: 17, x15: 18, x16: 19, x6: 20
    edit.Euo = {''}
    return edit


def test_falcone_15_fig2e():
    g = falcone_15_fig2e()
    g_so = so.construct_secret_observer_label_transform(g, notion=OpacityNotion.KSTEP, k=2, joint=True, secret_type=1)
    assert not so.verify_opacity_secret_observer(g_so)
    edit = falcone_15_fig10b()
    assert so.tmp_verify_edit_opacity(g, edit, public=True, notion=OpacityNotion.KSTEP, k=2, joint=True, secret_type=1)


"""
if __name__ == '__main__':
    test_saboori_07_fig1a()
    test_saboori_09_ex1()
    test_saboori_09_fig1b()
    test_saboori_11_fig1a()
    test_falcone_13_fig2a()
    test_falcone_13_fig2b()
    test_falcone_15_fig2c()
    test_falcone_15_fig2d()
    test_falcone_15_fig2e()
"""
