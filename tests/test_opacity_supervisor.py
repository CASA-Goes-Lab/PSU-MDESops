import DESops as d
from DESops.opacity.secret_observer import construct_secret_observer_label_transform
from DESops.supervisory_control.supervisor import supremal_sublanguage
from DESops.opacity.secret_specification import OpacityNotion

def compute_opacity_supervisor(g):

    a_so = construct_secret_observer_label_transform(g, notion=OpacityNotion.KSTEP, k=1, secret_type=1, joint=True)

    plant = a_so.copy()
    plant.vs['marked'] = True

    spec = a_so.copy()
    bad_states = [v.index for v in a_so.vs.select(marked=True)]
    spec.delete_vertices(list(bad_states))
    spec.vs['marked'] = True

    sup = supremal_sublanguage(plant, spec)
    return sup

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

    sup = compute_opacity_supervisor(g)

    assert sup.vcount() == 1
    assert sup.ecount() == 0



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

    sup = compute_opacity_supervisor(g)

    assert sup.vcount() == 2
    assert sup.ecount() == 1


def ind_to_coord(ind, m):
    return ind % m, int(ind / m)


def coord_to_ind(r, c, m):
    return r + c * m


def l1_dist(p1, p2):
    return max(abs(p1[0] - p2[0]), abs(p1[1] - p2[1]))


def test_square_example():
    g = gen_square_example(3, 3)

    sup = compute_opacity_supervisor(g)

    assert sup.vcount() == 8
    assert sup.ecount() == 9


def gen_square_example(m, n):
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
    #g.vs[coord_to_ind(int(m / 2) - 1, int(n / 2), m)]['secret'] = True

    g.generate_out()

    return g


if __name__ == '__main__':
    test_simple_example()
    test_square_example()
    test_k_step_example()
