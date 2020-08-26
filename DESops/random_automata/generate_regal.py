import os
import random
import subprocess

from DESops import error
from DESops.automata.DFA import DFA
from DESops.automata.event import Event


def generate_regal(
    num_states,
    num_events,
    num_uo=0,
    num_uc=0,
    g=None,
    timeout=None,
    max_out_degree=None,
    max_parallel_edges=None,
    remove_self_loop_prob=0,
):
    """
    Uses regal software to generate random DFA:

    num_vert: |V| of graph
    num_events: |E| of graph

    num_Euc: # of uncontrollable events to randomly select, must be [0, num_events]
    num_Euo: # of unobservable events to randomly select, must be [0, num_events]

    g: optionally pass DFA to build. If none, will return DFA
        Default None

    timeout: time in seconds after start of generation to stop process (taking too long).
        Default None, so won't stop.


    max_out_degree: limit number of transitions defined from a single state.
        Default None is no limit (i.e. num_events)

    max_parallel_edges: optionally limit the number of parallel transitions from any one state to another
        i.e. f(x1, e) = x2 is only defined for (x1, x2) for max_parallel_edges different events e
        Default None, which is set to num_events (no restrictions)

    remove_self_loop_prob: remove generated self loops with probability, [0,1]
        (Experimental) from tests, it seems that on average num_events self_loops generate with large number vertices.
        Default 0

    """

    this_dir = os.path.dirname(__file__)
    rand_DFA_dir = this_dir + "/regal-1.08.0929/random_DFA"

    if not os.path.isfile(rand_DFA_dir):
        raise error.DependencyNotInstalledError(
            "Could not find random_DFA executable. See instructions to install in DESops/random_DFA/regal_readme.txt"
        )

    if not max_parallel_edges:
        max_parallel_edges = num_events

    # can limit completeness by generating with a smaller event set
    # and then randomly replacing events
    if not max_out_degree:
        max_out_degree = num_events

    check_valid_params(num_events, num_uc, num_uo, max_out_degree, max_parallel_edges)

    this_dir = os.path.dirname(__file__)
    rand_DFA_dir = this_dir + "/regal-1.08.0929/random_DFA"
    output = subprocess.run(
        [rand_DFA_dir, str(num_vert), str(max_out_degree), "1"],
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

    g.add_vertices(num_vert)

    events = [Event(str(i)) for i in range(num_events)]
    transitions = []
    labels = []
    split_out = output.stdout.split("\n")
    out_attr = []

    for src, row in enumerate(split_out):
        # each row of output are transitions from a src state (src labeled by line number)
        if not row:
            continue

        split_row = row.split("  ")
        out_attr_row = []

        # targets_seen maps: trg -> [events]
        targets_seen = {}

        rand_events = random.sample(events, max_out_degree)
        for event, trg in zip(rand_events, split_row):
            if trg == "?" or trg == "":
                continue
            trg = int(trg)
            if remove_self_loop_prob > 0 and trg == src:
                if random.uniform(0, 1) > remove_self_loop_prob:
                    # don't add this self loop with p = remove_self_loop_prob
                    continue
                # else add this self loop w p = 1-(remove_self_loop_prob)

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
            transitions.extend((src, trg) for _ in e)
            out_attr_row.extend(g.Out(trg, event) for event in e)

        out_attr.append(out_attr_row)

    g.Euc.update(set(random.sample(events, num_uc)))
    g.Euo.update(set(random.sample(events, num_uo)))

    g.events = set(events)
    g.add_edges(transitions, labels, check_DFA=False, fill_out=False)
    g.vs["out"] = out_attr

    if g_not_defined:
        return g


def check_valid_params(
    num_events, num_Euc, num_Euo, max_out_degree, max_parallel_edges
):

    if num_events <= 0:
        raise ValueError(
            "Requires alphabet size greater than 0, got {0}".format(num_events)
        )
    if num_Euc > num_events:
        raise ValueError(
            "Requires num_Euc no greater than size alphabet, got {0}, max {1}".format(
                num_Euc, num_events
            )
        )

    if num_Euo > num_events:
        raise ValueError(
            "Requires num_Euo no greater than size alphabet, got {0}, max {1}".format(
                num_Euo, num_events
            )
        )

    if max_out_degree < 1:
        raise ValueError(
            "Requires max_out_degree to be greater than 0, got {0}".format(
                max_parallel_edges
            )
        )

    if max_parallel_edges < 1:
        raise ValueError(
            "Requires max_parallel_edge to be greater than 0, got {0}".format(
                max_parallel_edges
            )
        )
