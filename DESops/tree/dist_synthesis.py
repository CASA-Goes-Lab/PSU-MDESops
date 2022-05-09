from DESops.tree import dist_process

def pipeline_synthesis(pipe, spec_ata):
    """
    Perform synthesis on a pipeline architecture for the given specification automaton
    The automaton should have input type given by the non-environmental (input) variables of the pipeline
    and direction type given by the environmental (input) variables of the pipeline
    """
    A = []
    N = []
    B = [spec_ata]
    """
    Iteratively reduce the specification automaton by "nondeterministically" implementing
    the processes of the pipeline in order.
    """
    for i, p in enumerate(pipe.process_list):
        print(f"Reducing process {i}")
        # Narrow the directions of the specification to the input of the current process
        A.append(B[-1].narrow_direction(p.in_type).copy_int())
        # Make the result nondeterministic for change operation / nonemptiness check
        N.append(A[-1].to_nondet().copy_int())
        # No need to compute change operation for last process
        if len(B) == len(pipe.process_list):
            break
        # Nondeterministically implement the current process
        # Change the direction type of the specification to the output of the current process
        B.append(N[-1].change_pipeline(p.out_type).copy_int())

    # check emptiness for last automaton and find an implementation if one exists
    print("Checking emptiness")
    realizable = not N[-1].is_empty()
    return realizable, N


def construct_pipeline_realization(pipe, N):

    strats = []
    previous = None
    for i, joint_ata in reversed(enumerate(N)):
        if i < len(N):
            joint_ata = joint_ata.AND(previous.inverse_change())
        winning_set = joint_ata.construct_winning_set_emptiness()
        joint_strat = joint_ata.construct_tree_element(winning_set)
        strat = joint_strat.narrow_input(pipe.process_list[i].out_type)
        strats.append(strat)
        previous = joint_strat

    """

    # iterate and find implementation for the previous processes
    ata_list = [member_ata]
    lifted_ata_list = [member_ata]
    for i, p in reversed(list(enumerate(pipe.process_list[:-1]))):
        last_lifted_ata = lifted_ata_list[-1]
        # compose specification for processes with computed implementations of processes
        new_lifted_ata = inverse_change(inverse_narrow(
            last_lifted_ata, p.out_type), p.in_type).AND(N[i])
        # compute a corresponding implementation for the processes
        _, new_lifted_ata = new_lifted_ata.is_empty()
        lifted_ata_list.append(new_lifted_ata)
        # restrict implementation to current process
        new_ata = new_lifted_ata.inverse_widen(p.out_type)
        ata_list.append(new_ata)

    ata_list.reverse()
    if empty:
        return {"realizable": not empty, "solution": ata_list}
    """



def pipeline_linear_to_tree_spec(pipe, awa, delay=False):
    """
    This method takes the word automaton awa and appropriately shifts variables according to the pipeline arch
    so that strategies composed with delay have traces accepted by the shifted version correspond
    to strategies composed without delay have traces accepted by g.
    This method then takes this shifted word automaton and converts it into a tree automaton
    with directions given by the input to the architecture
    """

    # TODO - for efficiency, shifting should be done inbetween each step of synthesis rather than all at the beginning
    ata = awa
    if not delay:
        delay_type = dist_process.empty_type
        # delay the outputs of the nth the last process by n
        for proc in reversed(pipe.process_list):
            delay_type = delay_type.product_type(proc.out_type)
            ata = ata.delay_in(delay_type)

    return ata.change_pipeline(pipe.in_type, mode="AND")

