import DESops.automata.NFA
from DESops.visualization.write_tikz import write_tikz

def test_tikz():
    g = DESops.automata.NFA()
    g.add_vertices(3)
    g.vs['init'] = [True, False, False]
    g.vs['marked'] = [False, False, True]
    g.vs['secret'] = [False, True, False]
    g.add_edges([(0,1),(1,1),(1,2)], ['e_1', 'e_2', 'e_3'])

    write_tikz('tex/fig.tex', g)

if __name__ == '__main__':
    test_tikz()
