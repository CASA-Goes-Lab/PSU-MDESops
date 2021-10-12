import DESops.tree.ATA as ATA
import DESops.tree.ATA as ASA
import DESops.tree.dist_process as dist_process
import DESops.tree.dist_synthesis as dist_synthesis
import DESops
from DESops import NFA

from itertools import chain

empty_type = dist_process.DataType({})
empty_val = empty_type()


def inferability(pipe):
    in_type = pipe.get_type(["infer", "info"])
    info_values = pipe.in_type.var_values("info")
    ata_inf = ATA.AWA(in_type)
    # Label of inference should be the same as the label of the info
    ata_inf.add_states({"q"})
    ata_inf.init_state = "q"
    ata_inf.add_transitions({("q", in_type(info=info, infer=info)):
                                 ata_inf.alg.Symbol(("q", empty_val))
                             for info in info_values})
    ata_inf.set_weak_buchi(ata_inf.states.copy())
    return ata_inf


def secrecy(pipe, g_ns):
    in_type = pipe.get_type(["Eo"])
    ata_sec = ATA.AWA(in_type)
    # event output should be constrained by nonsecret automaton
    ata_sec.add_states(set(g_ns.vs.indices))
    ata_sec.init_state = g_ns.vs.select(init=True)[0].index
    ata_sec.add_transitions({(e.source, in_type(Eo=e["label"])):
                             ata_sec.alg.Symbol((e.target, empty_val))
                             for e in g_ns.es})
    ata_sec.set_weak_buchi(ata_sec.states.copy())
    return ata_sec


def block_assumption(pipe):
    block_type = pipe.get_type(["block"])
    in_type = block_type.product_type(pipe.in_type)
    ata_block = ATA.AWA(in_type)

    # Input must hold its values constant when output is not blocking
    # states represents last input
    ata_block.add_states({d for d in pipe.in_type})
    ata_block.init_state = "block_init"
    ata_block.add_states({ata_block.init_state})

    ata_block.add_transitions({(q, in_type.from_subvalues(q, block_type(block=1))):
                               ata_block.alg.Symbol((q, empty_val))
                               for q in pipe.in_type})
    ata_block.add_transitions({(ata_block.init_state, in_type.from_subvalues(q, block_type(block=0))):
                               ata_block.alg.Symbol((qp, empty_val))
                               for q in pipe.in_type for qp in pipe.in_type})
    ata_block.add_transitions({(ata_block.init_state, in_type.from_subvalues(qp, block_type(block=1))):
                               ata_block.alg.Symbol((qp, empty_val))
                               for qp in pipe.in_type})

    ata_block.set_weak_buchi(ata_block.states.copy())
    return ata_block


def block_guarantee(pipe, k_bound=0):
    in_type = pipe.get_type(["block"])
    ata_block = ATA.AWA(in_type)
    if k_bound is None:
        ata_block.add_states(set(range(2)))
        ata_block.init_state = 0
        both = ata_block.alg.AND(ata_block.alg.Symbol((0, empty_val)),
                                 ata_block.alg.Symbol((0, empty_val)))
        ata_block.add_transitions({(0, in_type(block=0)): both,
                                   (0, in_type(block=1)): both,
                                   (1, in_type(block=0)):
                                       ata_block.alg.TRUE,
                                   (1, in_type(block=1)):
                                       ata_block.alg.Symbol((1, empty_val))})
        ata_block.set_weak_buchi({0})
    else:
        # output must not block more than k times in a row
        ata_block.add_states(set(range(k_bound + 1)))
        ata_block.init_state = 0
        ata_block.add_transitions({(q, in_type(block=0)):
                                   ata_block.alg.Symbol((0, empty_val))
                                   for q in ata_block.states})
        ata_block.add_transitions({(q, in_type(block=1)):
                                   ata_block.alg.Symbol((q+1, empty_val))
                                   for q in range(0, k_bound)})
        ata_block.set_weak_buchi(ata_block.states.copy())
    return ata_block


def plant_dyn(pipe, g_plant):
    """
    Encode plant behavior from NFA into AFA with blocking
    """
    block_type = pipe.get_type(["block"])
    in_type = block_type.product_type(pipe.in_type)
    ata_dyn = ATA.AWA(in_type)
    # input to architecture must agree with the plant, accounting for block
    ata_dyn.add_states({v for v in g_plant.vs.indices})
    ata_dyn.init_state = g_plant.vs.select(init=True)[0].index
    for v in ata_dyn.states:
        for e in g_plant.es.select(_source=v):
            ata_dyn.add_transitions({(v, in_type(block=0, Ei=e["label"], info=g_plant.vs["info"][e.target])):
                                         ata_dyn.alg.Symbol((e.target, empty_val))
                                     })
        ata_dyn.add_transitions({(v, in_type.from_subvalues(block_type(block=1), in_value)):
                                     ata_dyn.alg.Symbol((v, empty_val))
                                 for in_value in pipe.in_type})
    ata_dyn.set_weak_buchi(ata_dyn.states.copy())
    return ata_dyn


def create_dist_problem(g, info_attr="info"):
    master_type = dist_process.DataType({
       "Ei": g.events,
       "Eo": g.events,
       "block": {0, 1},
       "info": set(g.vs[info_attr]),
       "infer": set(g.vs[info_attr])
    })

    pipe = dist_process.Pipeline(master_type.subtype({"info", "Ei"}))
    edit_process = dist_process.Process(
        master_type.subtype({"Ei"}),
        master_type.subtype({"block", "Eo"})
    )
    pipe.append_process(edit_process)
    infer_process = dist_process.Process(
        master_type.subtype({"Eo"}),
        master_type.subtype({"infer"})
    )
    pipe.append_process(infer_process)

    g_ns = g.copy()
    g_ns.delete_vertices(g_ns.vs.select(secret=True))

    # TODO remove simplify if possible?
    A_inf = inferability(pipe).simplify()
    A_sec = secrecy(pipe, g_ns).simplify()
    A_block_assumption = block_assumption(pipe).complement().simplify()
    A_block_guarantee = block_guarantee(pipe, k_bound=0).simplify()
    A_plant_dyn = plant_dyn(pipe, g).complement().simplify()

    A_spec = A_block_guarantee.AND((A_inf.AND(A_sec)).OR(A_block_assumption, A_plant_dyn)).simplify()
    A_spec = A_spec.widen_output(master_type)

    #A_spec = dist_synthesis.linear_to_tree_specification(A_spec, pipe.in_type, mode="mealy")
    A_spec = dist_synthesis.linear_to_tree_specification_pipeline(A_spec, pipe)
    return pipe, A_spec


if __name__ == '__main__':
    g = NFA()
    g.add_vertices(2)
    g.vs['init'] = [True, False]
    g.vs['secret'] = [False, True]
    g.vs['info'] = [False, True]
    g.add_edges([(0, 1), (1, 0), (0, 0), (0, 0)], ['a', 'a', 'b', 'c'])

    print("Constructing problem")
    pipe, spec = create_dist_problem(g)
    #print(spec.transitions)
    #print(spec.init_state)
    print("Synthesizing")
    realizable = not dist_synthesis.pipeline_synthesis(pipe, spec, delay=True)
    print(realizable)
