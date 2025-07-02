import DESops as d
from DESops.file.wmod_to_igraph import read_wmod, write_wmod, read_xml_automaton
from tempfile import TemporaryDirectory
import os


def test_wmod():
    g = d.NFA()
    g.add_vertices(3)
    g.vs["init"] = [True, False, False]
    g.vs["marked"] = [False, False, True]
    g.add_edges([(0, 1), (1, 2), (2, 0)], ["a", "b", "c"])
    g.events = {"a", "b", "c"}
    g.Euc = {"a"}

    with TemporaryDirectory() as tdir:
        wmod_filename = os.pathsep.join([tdir, "tmp.wmod"])
        write_wmod(wmod_filename, g)
        gg = read_wmod(wmod_filename)

    assert str(g) == str(gg)
