from DESops.tree import ATA, dist_process, dist_synthesis
from DESops.automata import DFA


empty_type = dist_process.DataType({})
empty_val = empty_type()


def match_spec():
    in_type = dist_process.DataType({'p_out': {1,2}})
    dir_type = dist_process.DataType({'p_in': {1,2}})
    ata_inf = ATA.ATA(in_type, dir_type)
    ata_inf.add_states({"q"})
    ata_inf.init_state = "q"
    ata_inf.add_transitions({("q", in_type(p_out=info)):
                                 ata_inf.alg.Symbol(("q", dir_type(p_in=info)))
                             for info in {1,2}})
    ata_inf.set_weak_buchi(ata_inf.states)
    return ata_inf

def lin_match_spec():
    in_type = dist_process.DataType({'y':{0,1}, 'x':{0,1}, 'p_out': {0,1}, 'p_in': {0,1}})
    ata_inf = ATA.AWA(in_type.subtype(['p_in', 'p_out']))
    ata_inf.add_states({0})
    ata_inf.init_state = 0
    ata_inf.add_transitions({(0, ata_inf.in_type(p_out=info, p_in=info)):
                                 ata_inf.alg.Symbol((0, dist_process.empty_value))
                             for info in {0,1}})
    ata_inf.set_weak_buchi(ata_inf.states)

    ata_o = ATA.AWA(in_type.subtype(['x', 'p_in']))
    ata_o.add_states({0})
    ata_o.init_state = 0
    ata_o.add_transitions({(0, ata_o.in_type(p_in=info, x=1-info)):
                           ata_o.alg.Symbol((0, dist_process.empty_value))
                           for info in {0, 1}})
    ata_o.set_weak_buchi(ata_o.states)
    ata_o.complement()

    ata_inf = ata_inf.OR(ata_o).widen_output(in_type)
    return ata_inf

def lin_match_spec_2():
    in_type = dist_process.DataType({'x':{0,1}, 'p_out': {0,1}, 'p_in': {0,1}})
    ata_inf = ATA.AWA(in_type.subtype(['p_in', 'p_out']))
    ata_inf.add_states({0})
    ata_inf.init_state = 0
    ata_inf.add_transitions({(0, ata_inf.in_type(p_out=info, p_in=info)):
                                 ata_inf.alg.Symbol((0, dist_process.empty_value))
                             for info in {0,1}})
    ata_inf.set_weak_buchi(ata_inf.states)

    return ata_inf.widen_output(in_type)

def lin_spec():
    in_type = dist_process.DataType({'p_out': {0, 1}, 'p_in': {0, 1}})
    ata_inf = ATA.AWA(in_type)
    ata_inf.add_states({0, 1, 2})
    ata_inf.init_state = 0
    ata_inf.add_transitions({(0, ata_inf.in_type(p_out=0, p_in=1)):
                             ata_inf.alg.Symbol((1, dist_process.empty_value))})
    ata_inf.add_transitions({(0, ata_inf.in_type(p_out=0, p_in=0)):
                             ata_inf.alg.Symbol((2, dist_process.empty_value))})
    ata_inf.add_transitions({(1, ata_inf.in_type(p_out=1, p_in=0)):
                             ata_inf.alg.Symbol((1, dist_process.empty_value))})
    ata_inf.add_transitions({(2, ata_inf.in_type(p_out=0, p_in=1)):
                             ata_inf.alg.Symbol((2, dist_process.empty_value))})
    ata_inf.add_transitions({(1, ata_inf.in_type(p_out=1, p_in=1)):
                             ata_inf.alg.Symbol((1, dist_process.empty_value))})
    ata_inf.add_transitions({(2, ata_inf.in_type(p_out=0, p_in=0)):
                             ata_inf.alg.Symbol((2, dist_process.empty_value))})

    ata_inf.set_weak_buchi(ata_inf.states)

    return ata_inf

"""
A = match_spec()
print(A.is_nondet())
#print(A.transitions)
#A = A.to_nondet()
#print(A.transitions)
empty, tree = A.is_empty()
#print(tree.transitions)
"""

A = lin_match_spec_2()
A.simplify()
#A_tree = dist_synthesis.linear_to_tree_specification(A, A.in_type.subtype(['p_in']), mode="mealy")

pipe = dist_process.Pipeline(A.in_type.subtype({"p_in"}))
p1 = dist_process.Process(
    A.in_type.subtype({"p_in"}),
    A.in_type.subtype({"x"})
)
pipe.append_process(p1)
p2 = dist_process.Process(
    A.in_type.subtype({"x"}),
    A.in_type.subtype({"p_out"})
)
pipe.append_process(p2)

A_spec = dist_synthesis.linear_to_tree_specification_pipeline(A, pipe)
res = dist_synthesis.pipeline_synthesis(pipe, A_spec, delay=True)
print(res)


"""
#print(A_tree.transitions)
#print(A_tree.is_empty())
#print(A_tree.is_nondet())
B = A_tree.delay_in(p2.out_type)
#print(B.transitions)
#print(B.is_empty())
C = B.delay_in(A_tree.in_type)
print(C.transitions)
print(C.is_empty())
D = B.change_pipeline(p1.out_type, delay=True)
print(D.transitions)
print(D.to_nondet().is_empty())
#B = A_tree.change_pipeline(p1.out_type, delay=False)
#print(B.transitions)
#print(B.to_nondet().is_empty())
res = dist_synthesis.pipeline_synthesis(pipe, A_tree, delay=False)
print(res)
"""

"""
B=A
#B = A.delay_in(A.in_type.quotient_type(pipe.in_type))
C = B.delay_in(A.in_type.quotient_type(pipe.in_type))
print("HEHHE")
print(A.in_type.quotient_type(pipe.in_type).var_names())
D = C.delay_in(p2.out_type)
print(p2.out_type.var_names())
#E = D.change_pipeline(pipe.in_type, mode='AND', delay=True)
#F = E.to_nondet().change_pipeline(p1.out_type, mode='OR', delay=True).copy_int()
#print(F.init_state)
#print(F.transitions)
#print(F.to_nondet().is_empty())
A_tree = dist_synthesis.linear_to_tree_specification(D, pipe.in_type)
res = dist_synthesis.pipeline_synthesis(pipe, A_tree, delay=True)
print(res)
"""


"""
A = lin_spec()
A = A.to_tree_automaton(A.in_type.subtype(['p_in']))
#A = A.delay_input_mod()
A = A.to_nondet()
#A = A.change_pipeline(A.in_type)
print(A.transitions)
empty, B = A.is_empty()
print(empty)
print(A.accepts_tree(B))
"""
