from DESops.tree import ATA, dist_process, dist_synthesis

def test_types():
    pass


def test_pipeline():
    super_type = dist_process.DataType({'p0': {0, 1}, 'p1': {"x", "y"},
                                        'p2': {frozenset({4}), frozenset({5})}, 'p3': {1, "2"}})
    pipe = dist_process.Pipeline(super_type.subtype({"p0"}))
    p1 = dist_process.Process(
        super_type.subtype({"p0"}),
        super_type.subtype({"p1", "p2"})
    )
    pipe.append_process(p1)
    p2 = dist_process.Process(
        super_type.subtype(({"p1"})),
        super_type.subtype(({"p3"}))
    )
    pipe.append_process(p2)

    assert pipe.check_valid()


def match_spec(t1, t2, match_pairs):
    match = lambda v1, v2: all(getattr(v1, s1) == getattr(v2, s2) for s1, s2 in match_pairs)
    super_type = t1.product_type(t2)
    ata = ATA.ATA(super_type, dist_process.empty_type)
    ata.add_states({"q"})
    ata.init_state = "q"
    ata.add_transitions({("q", super_type.from_subvalues(v1, v2)):
                                 ata.alg.Symbol(("q", dist_process.empty_value))
                             for v1 in t1 for v2 in t2 if match(v1, v2)})
    ata.set_weak_buchi(ata.states)
    return ata

def test_match_pipeline():
    super_type = dist_process.DataType({'p0': {0, 1}, 'p1': {0, 1}, 'p2': {0, 1}})
    t0 = super_type.subtype({"p0"})
    t1 = super_type.subtype({"p1"})
    t2 = super_type.subtype({"p2"})

    pipe = dist_process.Pipeline(t0)
    p1 = dist_process.Process(t0, t1)
    pipe.append_process(p1)
    p2 = dist_process.Process(t1, t2)
    pipe.append_process(p2)

    m1_spec = match_spec(t0, t1, [("p0", "p1")])
    m2_spec = match_spec(t1, t2, [("p1", "p2")])
    total_spec = m1_spec.AND(m2_spec, widen=True)

    tree_spec = dist_synthesis.pipeline_linear_to_tree_spec(pipe, total_spec, delay=False)
    realizable, _ = dist_synthesis.pipeline_synthesis(pipe, tree_spec)
    assert realizable

    tree_spec = dist_synthesis.pipeline_linear_to_tree_spec(pipe, total_spec, delay=True)
    realizable, _ = dist_synthesis.pipeline_synthesis(pipe, tree_spec)
    assert not realizable

