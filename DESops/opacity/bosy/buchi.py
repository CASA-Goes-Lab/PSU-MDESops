"""
Functions for constructing the Buchi automata that are used to enforce CSO with BoSyHyper
"""
import re
from collections import deque

from DESops.automata.DFA import DFA
from DESops.automata.NFA import NFA

# sentinel event for event replacement
e_replace = True


def construct_buchi_cso(
    g,
    event_var_maps,
    inf_fun,
    allow_insert,
    insert_holds_events,
    valid_replaces,
):
    """
    Construct a Buchi automaton that accepts all runs that correspond to a
    valid CSO edit function for a given DFA. An edit function is valid if, for
    as long as the input events remain legal, then the output events remain
    legal and the output state is never a secret state.

    Parameters:
    g: a DfA with secret states
    event_var_maps: see definition in run_bosy() in bosy_interface.py
    inf_fun: see the definition in run_bosy() in bosy_interface.py
    allow_insert: a boolean indicating whether event insertions are allowed
    insert_holds_events: see definition in run_bosy() in bosy_interface.py
    valid_replaces: see definition in run_bosy() in bosy_interface.py

    Returns:
    G_out: the Buchi automaton
    """
    event_map_I = event_var_maps["event_map_I"]

    # "don't care" event for insertion
    e_insert = sorted(list(g.events))[0]

    # prefix allows removing yield variable for non-insertion
    yield_prefix = "yield_out && " if allow_insert else ""

    # add first few vertices
    G_out = DFA()
    G_out.add_vertices(3, ["INIT", "FAIL", (0, 0, e_replace)])
    if allow_insert:
        G_out.add_vertex((0, 0, e_insert))

    # inital transitions
    G_out.add_edge(0, 2, f"{yield_prefix}{event_map_I[e_insert]}")
    if allow_insert:
        G_out.add_edge(0, 3, f"!yield_out && {event_map_I[e_insert]}")

    # fail state self-loop
    G_out.add_edge(1, 1, "true")

    # deque stores indices of unhandled source vertex indices
    states_to_check = deque([2])
    if allow_insert:
        states_to_check.append(3)

    while states_to_check:
        source = states_to_check.pop()
        i_source, o_source, prev_event = G_out.vs[source]["name"]

        # generate list of (target_name, label) pairs for outgoing transitions
        if prev_event is e_replace:
            transitions = generate_replacement_transitions(
                g,
                i_source,
                o_source,
                event_var_maps,
                inf_fun,
                allow_insert,
                insert_holds_events,
                valid_replaces,
            )
        else:
            transitions = generate_insertion_transitions(
                g,
                i_source,
                o_source,
                prev_event,
                event_var_maps,
                inf_fun,
                allow_insert,
                valid_replaces,
            )

        # generate each of the transitions
        for target_name, label in transitions:
            try:
                target = G_out.vs.select(name=target_name)[0].index
            except IndexError:
                # add target if it's a new state
                target = G_out.vcount()
                states_to_check.append(target)
                G_out.add_vertex(target_name)

            G_out.add_edge(source, target, label)

    # only fail state is accepting
    G_out.vs["marked"] = False
    G_out.vs[1]["marked"] = True

    # mark fail state as dead
    G_out.vs["dead"] = G_out.vs["marked"]

    return G_out


def generate_replacement_transitions(
    g,
    i_source,
    o_source,
    event_var_maps,
    inf_fun,
    allow_insert,
    insert_holds_events,
    valid_replaces,
):
    """
    Generate a list of (target_name, label) pairs for the outgoing transitions from
    the given state that represent an event replacement

    Parameters:
    g: the original automaton
    i_source: the input state at the source state
    o_source: the output state at the source state
    event_var_maps: see definition in run_bosy() in bosy_interface.py
    inf_fun: see definition in run_bosy() in bosy_interface.py
    allow_insert: a boolean indicating whether event insertions are allowed
    insert_holds_events: see definition in run_bosy() in bosy_interface.py
    valid_replaces: see definition in run_bosy() in bosy_interface.py

    Returns:
    a list of (target_name, label) pairs
    """
    event_map_I = event_var_maps["event_map_I"]
    event_map_O = event_var_maps["event_map_O"]

    transitions = list()

    # "don't care" event for insertion
    e_insert = sorted(list(g.events))[0]

    # prefix allows removing yield variable for non-insertion
    yield_prefix = "yield_out && " if allow_insert else ""

    # construct transitions to each next state
    for i_target in g.next_states(i_source):
        for o_target in g.next_states(o_source):
            # don't visit secret output states
            if g.vs[o_target]["secret"]:
                continue

            if not valid_replaces:
                # get allowable output formula (doesn't depend on input)
                good_outputs = [
                    event_map_O[o_event]
                    for o_event in g.events_between(o_source, o_target)
                ]
                output_formula = f"({' || '.join(good_outputs)})"

            # get labels of disjunction over inputs
            partial_labels = list()
            for i_event in g.events_between(i_source, i_target):
                if valid_replaces:
                    # get allowable output formula based on current input
                    good_outputs = [
                        event_map_O[o_event]
                        for o_event in g.events_between(o_source, o_target)
                        if o_event in valid_replaces[i_event]
                    ]
                    output_formula = f"({' || '.join(good_outputs)})"
                    if not good_outputs:
                        # skip if output target wasn't reachable for this input
                        continue
                # get label for input event and correct inferences
                inner_label = event_map_I[i_event]
                if inf_fun:
                    correct_infs = [fun(x=i_target, e=i_event) for fun in inf_fun]
                    inf_formula = f"({' && '.join(correct_infs)})"
                    inner_label = f"{inner_label} && {inf_formula}"
                inner_label = f"({inner_label} && {output_formula})"
                partial_labels.append(inner_label)

                if allow_insert and insert_holds_events:
                    # non-yielding transitions
                    target_name = (i_target, o_target, i_event)
                    label = f"!yield_out && {inner_label}"
                    transitions.append((target_name, label))

            if not partial_labels:
                # skip if output target wasn't reachable for any input
                continue

            # yielding transition
            target_name = (i_target, o_target, e_replace)
            label = f"{yield_prefix}({' || '.join(partial_labels)})"
            transitions.append((target_name, label))

            if allow_insert and not insert_holds_events:
                target_name = (i_target, o_target, e_insert)
                label = f"!yield_out && ({' || '.join(partial_labels)})"
                transitions.append((target_name, label))

    # construct failure transition
    # get allowable output formula
    X_NS = [v.index for v in g.vs if not v["secret"]]
    good_outputs = [
        event_map_O[o_event] for o_event in g.events_between(o_source, X_NS)
    ]
    output_formula = f"({' || '.join(good_outputs)})"

    # get labels of disjunction over inputs
    partial_labels = list()
    for i_event in g.active_events(i_source):
        if inf_fun:
            i_target = g.trans(i_source, i_event)
            correct_infs = [fun(x=i_target, e=i_event) for fun in inf_fun]
            inf_formula = f"({' && '.join(correct_infs)})"
            inner_label = f"{inf_formula} && {output_formula}"
        else:
            inner_label = output_formula
        # we fail if we have a good event and bad outputs
        inner_label = f"({event_map_I[i_event]} && !({inner_label}))"
        partial_labels.append(inner_label)

    # failure transition
    target_name = "FAIL"
    label = f"{' || '.join(partial_labels)}" if good_outputs else "true"
    transitions.append((target_name, label))

    return transitions


def generate_insertion_transitions(
    g,
    i_source,
    o_source,
    prev_event,
    event_var_maps,
    inf_fun,
    allow_insert,
    valid_replaces,
):
    """
    Generate a list of (target_name, label) pairs for the outgoing transitions from
    the given state that represent an event replacement

    Parameters:
    g: the original automaton
    i_source: the input state at the source state
    o_source: the output state at the source state
    prev_event: the previous event at the source state
    event_var_maps: see definition in run_bosy() in bosy_interface.py
    inf_fun: see definition in run_bosy() in bosy_interface.py
    allow_insert: a boolean indicating whether event insertions are allowed
    valid_replaces: see definition in run_bosy() in bosy_interface.py

    Returns:
    a list of (target_name, label) pairs
    """
    event_map_I = event_var_maps["event_map_I"]
    event_map_O = event_var_maps["event_map_O"]

    transitions = list()

    # prefix allows removing yield variable for non-insertion
    yield_prefix = "yield_out && " if allow_insert else ""

    # construct transitions to each next state
    for o_target in g.next_states(o_source):
        # don't visit secret output states
        if g.vs[o_target]["secret"]:
            continue

        # get allowable output formula
        good_outputs = [
            event_map_O[o_event]
            for o_event in g.events_between(o_source, o_target)
            if not valid_replaces or o_event in valid_replaces[prev_event]
        ]
        output_formula = f"({' || '.join(good_outputs)})"
        if not good_outputs:
            # skip if that target wasn't reachable by a valid event
            continue

        partial_label = event_map_I[prev_event]
        if inf_fun:
            correct_infs = [fun(x=i_source, e=prev_event) for fun in inf_fun]
            inf_formula = f"({' && '.join(correct_infs)})"
            partial_label = f"{partial_label} && {inf_formula}"
        partial_label = f"{partial_label} && {output_formula}"

        # yielding transition
        target_name = (i_source, o_target, e_replace)
        label = f"{yield_prefix}{partial_label}"
        transitions.append((target_name, label))

        if allow_insert:
            # non-yielding transition
            target_name = (i_source, o_target, prev_event)
            label = f"!yield_out && {partial_label}"
            transitions.append((target_name, label))

    # construct failure transition
    # get allowable output formula
    X_NS = [v.index for v in g.vs if not v["secret"]]
    good_outputs = [
        event_map_O[o_event] for o_event in g.events_between(o_source, X_NS)
    ]
    output_formula = f"({' || '.join(good_outputs)})"

    if inf_fun:
        correct_infs = [fun(x=i_source, e=prev_event) for fun in inf_fun]
        inf_formula = f"({' && '.join(correct_infs)})"
        inner_label = f"{inf_formula} && {output_formula}"
    else:
        inner_label = output_formula

    # we fail if we have a good event and bad outputs
    target_name = "FAIL"
    label = f"{event_map_I[prev_event]} && !({inner_label})" if good_outputs else "true"
    transitions.append((target_name, label))

    return transitions


def add_safe_state(g):
    """
    At every transition in g, add a transition to a "safe" state that is taken if no other transition is satisfied

    Parameters:
    g: an atomaton with transitions labeled as boolean formulae

    Returns:
    G_out: the automaton with the "safe" state added
    """
    G_out = g.copy()

    safe_index = g.vcount()
    G_out.add_vertex("SAFE", False)
    G_out.add_edge(safe_index, safe_index, "(true)")
    G_out.vs[safe_index]["init"] = False

    for v in g.vs:
        labels = {f"({o.label})" for o in v["out"]}
        safe_trans = f"!({' || '.join(labels)})"
        G_out.add_edge(v.index, safe_index, safe_trans)

    G_out.generate_out()
    return G_out


def compose_buchi(g, h, event_var_maps):
    """
    Compose a Buchi automaton that accepts all valid CSO edit functions with
    a Buchi automaton that accepts runs that fail to satisfy an auxiliary LTL
    specification.

    Parameters:
    g: a deterministic Buchi automaton that accepts valid CSO edit functions
    h: a (possibly non-deterministic) Buchi automaton that accepts runs that
        don't satisfy the auxiliary LTL spec
    num_states: the number of states in the original input automaton that the
        Buchi automaton g was produced from

    Returns:
    G_out: the composition automaton
    """
    event_map_I = event_var_maps["event_map_I"]

    G_out = NFA()

    # add first few vertices
    G_out.add_vertex((0, 0))

    # deque stores indices of unhandled source vertex indices
    states_to_check = deque([0])

    while states_to_check:
        source = states_to_check.pop()
        g_source, h_source = G_out.vs[source]["name"]

        # if either vertex is dead, we can just self-loop because we know we will accept
        if g.vs[g_source]["dead"] or h.vs[h_source]["dead"]:
            G_out.add_edge(source, source, "true")
            continue

        # generate a transition for each combination of formulae
        for g_target, g_label in g.vs[g_source]["out"]:
            for h_target, h_label in h.vs[h_source]["out"]:
                # encode events and evaluate states in h label
                x_target = g.vs[g_target]["name"][0]
                # split label between variables names and everything else
                terms = re.split(r"(\w+)", h_label)
                for i, t in enumerate(terms):
                    # encode events
                    if t in event_map_I:
                        terms[i] = event_map_I[t]
                    # check if string is state name, evaluate it if it is
                    elif re.match(r"^x[0-9]+$", t):
                        terms[i] = "true" if int(t[1:]) == x_target else "false"
                h_label = "".join(terms)

                target_name = (g_target, h_target)
                label = f"(({g_label}) && ({h_label}))"

                try:
                    target = G_out.vs.select(name=target_name)[0].index
                except IndexError:
                    # add target if it's a new state
                    target = G_out.vcount()
                    states_to_check.append(target)
                    G_out.add_vertex(target_name)

                G_out.add_edge(source, target, label)

    # indicate initial states
    G_out.vs["init"] = False
    G_out.vs[0]["init"] = True
    # mark states if either component was originally marked
    G_out.vs["marked"] = [False] + [
        g.vs[u]["marked"] or h.vs[v]["marked"] for u, v in G_out.vs[1:]["name"]
    ]

    return G_out
