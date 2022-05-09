from DESops.tree import ATA, dist_process


def ata_example1():
    in_type = dist_process.DataType({'p_out': {1, 2}})
    dir_type = dist_process.DataType({'p_in': {1, 2}})
    ata = ATA.ATA(in_type, dir_type)
    ata.add_states({0, 1, 2, 3})
    ata.init_state = 0
    ata.add_simple_transitions({(0, 1): [],
                                (0, 2): [[(1, 1), (2, 1)]],
                                (1, 1): [[(3, 1)]],
                                (2, 1): [[(2, 2)]],
                                (2, 2): [[(3, 1)]],
                                (3, 1): [[(3, 1)]]})
    ata.set_weak_buchi({3})
    ata.simplify()
    return ata

def ata_example2():
    in_type = dist_process.DataType({'p_out': {1, 2}})
    dir_type = dist_process.DataType({'p_in': {1, 2}})
    ata = ATA.ATA(in_type, dir_type)
    ata.add_states({0, 1})
    ata.init_state = 0
    ata.add_simple_transitions({(0, 2): [[(1, 1), (1, 2)]],
                                (1, 1): [[(1, 1), (0, 2)]]})
    ata.set_weak_buchi({0,1})
    ata.simplify()
    return ata


def ata_example3():
    in_type = dist_process.DataType({'p_out': {1, 2}})
    dir_type = dist_process.DataType({'p_in': {1, 2}})
    ata = ATA.ATA(in_type, dir_type)
    ata.add_states({0, 1})
    ata.init_state = 0
    ata.add_simple_transitions({(0, 2): [[(1, 1), (1, 2)]],
                                (1, 2): [[(1, 1), (0, 2)]]})
    ata.set_weak_buchi({0,1})
    ata.simplify()
    return ata


def test_ATA():
    ata = ata_example1()
    assert len(ata.states) == 4


def test_weak_buchi():
    weak_ata = ata_example1()
    assert weak_ata.is_weak_buchi()

    non_weak_ata = ata_example1()
    non_weak_ata.add_simple_transitions({(3, 1): [[(0, 1)]]})
    assert not non_weak_ata.is_weak_buchi()


def test_nondet():
    ata = ata_example1()
    assert not ata.is_nondet()
    assert ata.to_nondet().is_nondet()
    assert ata.complement().is_nondet()


def test_emptiness():
    ata = ata_example1().to_nondet()
    empty, winning = ata.test_emptiness()
    assert not empty
    assert ata.construct_tree_element(winning).is_tree()

    ata.set_weak_buchi({0})
    assert ata.to_nondet().is_empty()


def test_lang_subset():
    ata1 = ata_example1()
    ata2 = ata_example1()
    ata2.add_simple_transitions({(1, 2): [[(3, 1)]]})

    assert ata1.is_language_subset(ata2)
    assert not ata2.is_language_subset(ata1)


def test_tree():
    ata = ata_example1()
    assert not ata.is_tree()

    tree_ata = ata_example2()
    assert tree_ata.is_tree()
    assert ata.accepts_tree(tree_ata)

    tree_ata = ata_example3()
    assert tree_ata.is_tree()
    assert not ata.accepts_tree(tree_ata)


def ata_example4():
    # accepts p0-trees where inputs p1 and p2 match
    in_type = dist_process.DataType({'p1': {1, 2}, 'p2': {1, 2}})
    dir_type = dist_process.DataType({'p0': {1, 2}})
    ata = ATA.ATA(in_type, dir_type)
    ata.add_states({0})
    ata.init_state = 0
    ata.add_simple_transitions({(0, (1, 1)): [[(0, 1), (0, 2)]],
                                (0, (2, 2)): [[(0, 1), (0, 2)]]})
    ata.set_weak_buchi({0})
    ata.simplify()
    return ata


def ata_example5():
    # accepts p0-trees where input p2 matches previous input p1, first p1 must be 1
    in_type = dist_process.DataType({'p1': {1, 2}, 'p2': {1, 2}})
    dir_type = dist_process.DataType({'p0': {1, 2}})
    ata = ATA.ATA(in_type, dir_type)
    ata.add_states({0, 1})
    ata.init_state = 0
    ata.add_simple_transitions({(0, (1, 1)): [[(0, 1), (0, 2)]],
                                (0, (2, 1)): [[(1, 1), (1, 2)]],
                                (1, (1, 2)): [[(0, 1), (0, 2)]],
                                (1, (2, 2)): [[(1, 1), (1, 2)]]})
    ata.set_weak_buchi({0, 1})
    ata.simplify()
    return ata


def ata_example6():
    # accepts words where inputs p1 and p2 match
    in_type = dist_process.DataType({'p0': {1, 2}, 'p1': {1, 2}, 'p2': {1, 2}})
    dir_type = dist_process.empty_type
    ata = ATA.ATA(in_type, dir_type)
    ata.add_states({0})
    ata.init_state = 0
    ata.add_simple_transitions({(0, (1, 1, 1)): [[(0, ())]],
                                (0, (1, 2, 2)): [[(0, ())]],
                                (0, (2, 1, 1)): [[(0, ())]],
                                (0, (2, 2, 2)): [[(0, ())]]})
    ata.set_weak_buchi({0})
    ata.simplify()
    return ata


def test_change_pipeline():

    ata4 = ata_example4()
    ata5 = ata_example5()
    ata6 = ata_example6()
    t0 = ata4.dir_type
    t1 = ata4.in_type.subtype({'p1'})
    t2 = ata4.in_type.subtype({'p2'})

    # in each step, we can choose p1 to match p2
    assert not ata4.change_pipeline(t1).to_nondet().is_empty()
    # in each step, environment can choose p1 to not match p2
    assert ata4.change_pipeline(t1, mode="AND").to_nondet().is_empty()

    # ata5 accepts the trees of ata4 whose first input has p1=1
    #ata4_delay = ata4.delay_in(t2)
    #assert ata5.is_language_subset(ata4_delay)
    #assert not ata4_delay.is_language_subset(ata5)
    # in each step, for any environment choice of p1, we can choose p2 to match in the next step
    assert not ata5.change_pipeline(t1, mode="AND").to_nondet().is_empty()

    # ata4 accepts all trees whose paths are accepted by ata6
    ata6_change = ata6.change_pipeline(t0, mode="AND")
    assert ata6_change.is_language_equivalent(ata4)

