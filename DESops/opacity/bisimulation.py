"""
Functions related to constructing a secret-preserving bisuimulation
"""
from DESops.automata.NFA import NFA


def construct_bisimulation(g):
    """
    Constructs and returns a minimal-state automaton that is bisimilar to g and that preserves the secret behavior of g
    """
    events = set(g.es["label"])
    partition, table, e_dict = find_coarsest_bisimilar_partition(g, events)

    h = NFA()
    h.add_vertices(len(partition))
    h.vs["init"] = [any([g.vs[i]["init"] for i in block]) for block in partition]
    h.vs["secret"] = [any([g.vs[i]["secret"] for i in block]) for block in partition]
    h.Euo = g.Euo

    for i, block in enumerate(partition):
        # for each block, grab an arbitrary state in the block (since all have the same transitions)
        state = block.pop()
        for e in events:
            # add transitions from the current block to every other block that event e leads to
            next_set = table[state][0][e_dict[e]]
            for j in next_set:
                h.add_edge(i, j, e)

    h.generate_out()
    return h


def find_coarsest_bisimilar_partition(g, events):
    """
    Finds the coarsest partition of states of g that will produce an automaton that
    is bisimilar to g and whose secret behavior is identical to that of g

    Returns:
        the partition as a list of sets of state indices,
        a table whose (i,j) entry is the set of block indices reached by block i via event j,
        a dict mapping events to their column in the table
    """
    e_dict = dict()
    for i, e in enumerate(events):
        e_dict[e] = i

    # initial partition separates secret and nonsecret states
    partition = [
        {v.index for v in g.vs if v["secret"]},
        {v.index for v in g.vs if not v["secret"]},
    ]
    if set() in partition:
        partition.remove(set())

    # loop until we return in the final if statement
    while True:
        # s_dict maps each state index to the block containing it
        s_dict = dict()
        for i, block in enumerate(partition):
            for state in block:
                s_dict[state] = i

        # table tells which blocks each state transitions to with each event
        table = [[set() for _ in events] for _ in g.vs]
        for t in g.es:
            table[t.source][e_dict[t["label"]]].add(s_dict[t.target])

        # convert lists of sets into tuples of frozensets so they are hashable
        for i, row in enumerate(table):
            for j, value in enumerate(row):
                row[j] = frozenset(value)
            # add a secrecy flag to prevent secret and nonsecret states in the same block
            table[i] = (tuple(row), g.vs[i]["secret"])

        # row_dict maps rows of the table to sets of states that produced that row
        row_dict = dict()
        for i, row in enumerate(table):
            if row in row_dict:
                row_dict[row].add(i)
            else:
                row_dict[row] = {i}

        # create new partition where each block consists of states that produced the same row
        new_partition = [block for block in row_dict.values()]

        # if partition size is unchanged, then we have found the coarsest bisimilar partition
        if len(new_partition) == len(partition):
            return partition, table, e_dict
        # otherwise repeat the process using the new partition
        else:
            partition = new_partition
