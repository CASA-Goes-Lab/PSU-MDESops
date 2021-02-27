import DESops as d
from DESops.opacity.edisyn_interface import enforce_state_based_opacity_edisyn


def test_simple_example():
    g = d.automata.DFA()
    g.add_vertices(2)
    g.add_edge(0, 1, 'e')
    g.add_edge(1, 1, 'e')

    g.vs['marked'] = True

    g.vs["init"] = False
    g.vs[0]["init"] = True

    g.vs["secret"] = False
    g.vs[1]["secret"] = True

    g.generate_out()

    utility = [(u.index, v.index) for u in g.vs for v in g.vs]

    obf = enforce_state_based_opacity_edisyn(g, utility, 'CSO', insertion_bound=1)

    assert obf
    assert obf.vcount() == 2
    assert obf.ecount() == 2


def test_k_step_example():
    g = d.automata.NFA()
    g.add_vertices(5)
    g.add_edge(0, 1, 'a')
    g.add_edge(1, 2, 'b')
    g.add_edge(0, 3, 'a')
    g.add_edge(3, 4, 'b')
    g.add_edge(0, 4, 'b')

    g.vs['marked'] = True

    g.vs["init"] = False
    g.vs[0]["init"] = True

    g.vs["secret"] = False
    g.vs[1]["secret"] = True
    g.vs[4]["secret"] = True

    g.generate_out()

    utility = [(0, 0), (1, 1), (2, 2), (3, 3), (4, 4), (4, 0)]

    obf = enforce_state_based_opacity_edisyn(g, utility, 'KSTEP', k=2, insertion_bound=1, joint=False)
    assert obf.vcount() == 4
    assert obf.ecount() == 3

    obf = enforce_state_based_opacity_edisyn(g, utility, 'KSTEP', k=1, insertion_bound=1, joint=True)
    assert not obf


def ind_to_coord(ind, m):
    return ind % m, int(ind / m)


def coord_to_ind(r, c, m):
    return r + c * m


def l1_dist(p1, p2):
    return max(abs(p1[0] - p2[0]), abs(p1[1] - p2[1]))


def test_square_examples():
    g, utility = gen_square_example(3, 3, 2)
    obf = enforce_state_based_opacity_edisyn(g, utility, 'KSTEP', k=2, insertion_bound=1, joint=False)
    assert obf.vcount() == 15
    assert obf.ecount() == 20


def gen_square_example(m, n, l1_dist_bound):
    g = d.automata.DFA()

    g.add_vertices(m * n)
    g.vs['name'] = [ind_to_coord(v.index, m) for v in g.vs]

    g.add_edges([(coord_to_ind(r, c, m), coord_to_ind(r, c + 1, m)) for r in range(m) for c in range(n - 1)],
                ['r'] * (m * (n - 1)))
    g.add_edges([(coord_to_ind(r, c, m), coord_to_ind(r + 1, c, m)) for r in range(m - 1) for c in range(n)],
                ['d'] * (n * (m - 1)))
    g.add_edges([(coord_to_ind(r, c, m), coord_to_ind(r, c, m)) for r in range(m - 1, m) for c in range(n - 1, n)],
                ['s'] * (1))

    g.vs['marked'] = True

    g.vs["init"] = False
    g.vs[coord_to_ind(0, 0, m)]["init"] = True

    g.vs["secret"] = False
    g.vs[coord_to_ind(int(m / 2), int(n / 2), m)]['secret'] = True
    g.vs[coord_to_ind(int(m / 2) - 1, int(n / 2), m)]['secret'] = True

    g.generate_out()

    utility = [(u.index, v.index) for u in g.vs for v in g.vs if l1_dist(u['name'], v['name']) <= l1_dist_bound]

    return g, utility

