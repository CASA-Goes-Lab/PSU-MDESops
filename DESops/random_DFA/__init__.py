import os
import random
import subprocess
import sys

from DESops.automata.DFA import DFA
from DESops.automata.event.event import Event

# On import, ensure random_DFA file exists:
this_dir = os.path.dirname(__file__)
rand_DFA_dir = this_dir + "/regal-1.08.0929/random_DFA"

if not os.path.isfile(rand_DFA_dir):
    sys.exit(
        "Could not find random_DFA executable. See instructions to install in DESops/random_DFA/regal_readme.txt"
    )

# output = subprocess.run(["./random_DFA", str(num_vert), str(size_alphabet), str(num_automata)], capture_output=True, text=True)

# print(output.stdout)


def generate(
    num_vert, size_alphabet, num_Euc, num_Euo, g=None, timeout=None, overlap=True, max_parallel_edges=1
):
    """
    Uses regal software to generate random DFA:

    num_vert: |V| of graph
    size_alphabet: |E| of graph


    """
    

    this_dir = os.path.dirname(__file__)
    rand_DFA_dir = this_dir + "/regal-1.08.0929/random_DFA"
    output = subprocess.run(
        [rand_DFA_dir, str(num_vert), str(size_alphabet), "1"],
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    # Convert to DESops DFA:
    if not g:
        g_not_defined = True
        g = DFA()
    else:
        g_not_defined = False
        assert isinstance(g, DFA)

    if size_alphabet <= 0:
        raise ValueError("Requires alphabet size greater than 0, got {0}".format(size_alphabet))
    if num_Euc > size_alphabet:
        raise ValueError("Requires num_Euc no greater than size alphabet, got {0}, max {1}".format(num_Euc, size_alphabet))

    if num_Euo > size_alphabet:
        raise ValueError("Requires num_Euo no greater than size alphabet, got {0}, max {1}".format(num_Euo, size_alphabet))

    if max_parallel_edges < 1:
        raise ValueError("Requires max_parallel_edge to be greater than 0, got {0}".format(max_parallel_edges))
    g.add_vertices(num_vert)

    events = [Event(str(i)) for i in range(size_alphabet)]
    transitions = []
    labels = []
    split_out = output.stdout.split("\n")
    out_attr = []
    for src, row in enumerate(split_out):
        if not row:
            continue

        split_row = row.split("  ")
        out_attr_row = []

        # targets_seen maps: trg -> [events]
        targets_seen = {}

        for event, trg in zip(events, split_row):
            if trg == "?":
                continue

            if trg in targets_seen:
                targets_seen[trg].append(event)

            else:
                targets_seen[trg] = []
                targets_seen[trg].append(event)

        # reduce targets_seen to no more than max_parallel_edge
        for trg, e in targets_seen.items():
            if len(e) >= max_parallel_edges:
                e = random.sample(e, max_parallel_edges)

            # convert info to graph-ready lists:
            labels.extend(e)
            transitions.extend((src, int(trg)) for _ in e)
            out_attr_row.extend((int(trg), event) for event in e)

        out_attr.append(out_attr_row)

    g.Euc = set(random.sample(events, num_Euc))
    g.Euo = set(random.sample(events, num_Euo))

    g.events = set(events)
    g.add_edges(transitions, labels, check_DFA=False)
    g.vs["out"] = out_attr

    if g_not_defined:
        return g
