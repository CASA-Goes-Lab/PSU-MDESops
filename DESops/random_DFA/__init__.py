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
    num_vert, size_alphabet, g=None, timeout=None, Euc_p=0.5, Euo_p=0.5, overlap=True
):
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
        assert isinstance(g, d.DFA)
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

        for event, trg in zip(events, split_row):
            if trg == "?":
                continue
            labels.append(event)
            transitions.append((src, int(trg)))
            out_attr_row.append((trg, event))

        out_attr.append(out_attr_row)

    # TODO: prevent overlap of Euo, Euc ?
    num_Euc = round(size_alphabet * Euc_p)
    num_Euo = round(size_alphabet * Euo_p)

    g.Euc = set(random.sample(events, num_Euc))
    g.Euo = set(random.sample(events, num_Euo))

    g.events = set(events)
    g.add_edges(transitions, labels, check_DFA=False)
    g.vs["out"] = out_attr

    if g_not_defined:
        return g
