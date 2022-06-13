from DESops.tree import ATA, dist_process, graph_algs


def test_graph_algs():
    in_type = dist_process.DataType({'p_out': {1, 2}})
    dir_type = dist_process.DataType({'p_in': {1, 2}})
    ata_inf = ATA.ATA(in_type, dir_type)
    ata_inf.add_states({"q", "p"})
    ata_inf.init_state = "q"
    ata_inf.add_transitions({("q", in_type(p_out=info)):
                                 ata_inf.alg.Symbol(("p", dir_type(p_in=info)))
                             for info in {1, 2}})
    ata_inf.set_weak_buchi(ata_inf.states)
    ata_inf.simplify()

    scc = graph_algs.SCCHelper(ata_inf.construct_transition_NFA()).computeSCC()
    assert len(scc) == 2
    assert {"p"} in scc
    assert {"q"} in scc
