from collections import deque

from DESops.automata.DFA import DFA
from DESops.automata.NFA import NFA
from DESops.opacity.bisimulation import construct_bisimulation
from DESops.opacity.bosy.edit_to_bosy import list_to_bool_vars


def write_partial_smv(path, g, event_var_maps):
    """
    Write a partial smv file that contains the transition constraints of the inputs

    Parameters:
    path: the path/filename of the _smv file that should be written
    g: the original system automaton
    event_var_maps: see the definition in run_bosy() in bosy_interface.py
    """
    # get input variable maps
    states = range(g.vcount())
    _, state_map_I = list_to_bool_vars(states, "x_I_")
    event_map_I = event_var_maps["event_map_I"]

    # map (state, event) pairs to their target state
    trans = dict()
    for e in g.es:
        trans[(e.source, e["label"])] = e.target

    # map states to an SMV formula that is satisfied by valid events
    valid_formula = list()
    for v in g.vs:
        valid = {e["label"] for e in g.es if e.source == v.index}
        valid_formula.append(f"({' | '.join([event_map_I[e] for e in valid])})")

    # formula for initial state
    init_formula = f"({state_map_I[0]} & {valid_formula[0]})".replace("&&", "&")

    # formulae for transitions
    trans_formulae = list()
    for key, val in trans.items():
        source, event = key
        target = val

        current_formula = f"({state_map_I[source]} & {event_map_I[event]})"
        next_formula = f"next({state_map_I[target]} & {valid_formula[target]})"
        trans_formulae.append(
            f"({current_formula} -> {next_formula})".replace("&&", "&")
        )

    with open(path, "w") as file:
        file.write(f"INIT {init_formula}\n")
        file.write(f"TRANS {' & '.join(trans_formulae)}\n")


def make_human_readable(path, g, event_var_maps):
    """
    Edit an smv file representing the environment and controller to add human readable event and state variables.

    Parameters:
    path: the path/filename of the smv file that should be modified
    g: the original system automaton
    event_var_maps: see the definition in run_bosy() in bosy_interface.py
    """
    states = range(g.vcount())
    events = sorted(list(g.events))

    with open(path, "r") as file:
        contents = file.read().splitlines()

    # Count number of latches
    num_latches = sum(line.startswith("__latch_s") for line in contents)
    controller_states = list(range(2 ** num_latches))

    # Encode automaton states/events and controller states as boolean variables
    event_map_I = event_var_maps["event_map_I"]
    event_map_O = event_var_maps["event_map_O"]
    state_vars_I, _ = list_to_bool_vars(states, "x_I_")
    _, controller_state_map = list_to_bool_vars(controller_states, "__latch_s")

    i = contents.index("VAR")
    contents.insert(
        i + 1,
        "".join([f"{x} : boolean;\n" for x in state_vars_I])
        + f"event_i : {{{', '.join(events)}, undef}};\n"
        + f"event_o : {{{', '.join(events)}, undef}};\n"
        + f"controller_state : {{{', '.join(str(c) for c in controller_states)}, undef}};",
    )

    i = contents.index("ASSIGN")
    contents.insert(
        i + 1,
        "event_i := "
        + "".join(f"{event_map_I[e]} ? {e} : " for e in events)
        + "undef;\n"
        + "event_o := "
        + "".join(f"{event_map_O[e]} ? {e} : " for e in events)
        + "undef;\n"
        + "controller_state := "
        + "".join(f"{controller_state_map[c]} ? {c} : " for c in controller_states)
        + "undef;",
    )
    contents[i + 1] = contents[i + 1].replace("&&", "&")

    with open(path, "w") as file:
        file.write("\n".join(contents))


def read_smv(path, g, event_var_maps, inf_vars, allow_insert, insert_holds_events):
    """
    Read the smv file after having run BoSyHyper, and construct automata representing the obfuscator and inferrers

    Parameters:
    path: the path/filename of the smv file that should be read
    g: the original system automaton
    event_var_maps: see definition in run_bosy() in bosy_interface.py
    inf_vars: a list of the names of the inference variables
    allow_insert: a boolean indicating whether event insertions are allowed
    insert_holds_events: see definition in run_bosy() in bosy_interface.py

    Returns:
    cntl: The controller automaton
    preds: A dict mapping each inference variable to its "predictor" automaton that marks runs in which the inference is made
        (Warning: correctness of predictor automata are unverified; use at your own risk)
    """
    events = sorted(list(g.events))

    with open(path, "r") as file:
        contents = file.read().splitlines()

    # Count number of latches
    num_latches = sum(line.startswith("__latch_s") for line in contents)
    controller_states = list(range(2 ** num_latches))

    # Encode automaton states/events and controller states as boolean variables
    event_vars_I = event_var_maps["event_vars_I"]
    event_map_I = event_var_maps["event_map_I"]
    controller_state_vars, controller_state_map = list_to_bool_vars(
        controller_states, "__latch_s"
    )

    # find and parse the logical expressions
    exprs = [line for line in contents if ":=" in line]
    seq_init = list()
    seq_next = list()
    comb = list()
    for line in exprs:
        # strip semicolons
        line = line[:-1]

        words = line.split()
        terms = list()
        in_parentheses = False
        for word in words:
            # replace symbolic enums with strings
            if word == "undef" or word in events:
                word = f"'{word}'"

            # group expressions in parentheses as single words
            if in_parentheses:
                terms[-1] += f" {word}"
            else:
                terms.append(word)

            if "(" in word:
                in_parentheses = True
            if ")" in word:
                in_parentheses = False

        # reorder ternary operators
        for j, term in enumerate(terms):
            if term == "?":
                terms[j - 1], terms[j + 1] = terms[j + 1], terms[j - 1]

        # rejoin terms, and define variables as globals
        line = f"global {terms[0]}; " + " ".join(terms)

        # convert to Python operators
        line = line.replace(":=", "=")
        line = line.replace("?", "if")
        line = line.replace(":", "else")
        line = line.replace("!", "not ")
        line = line.replace("&", "and")
        line = line.replace("TRUE", "True")
        line = line.replace("FALSE", "False")

        if "init(" in line:
            line = line.replace("init(", "")
            line = line.replace(")", "")
            seq_init.append(line)

        elif "next(" in line:
            line = line.replace("next(", "")
            line = line.replace(")", "")
            seq_next.append(line)

        elif line.startswith("global event_i"):
            # input event doesn't need to be computed
            pass

        elif line.startswith("global event_o"):
            event_o_expr = line

        elif line.startswith("global controller_state"):
            controller_state_expr = line

        elif line.startswith("global yield_out"):
            yield_expr = line

        else:
            comb.append(line)

    # suppress error from undefined variables
    global event_i
    global event_o
    global controller_state
    global yield_out

    # sentinel event for event replacement
    e_replace = True
    # "don't care" event for insertion
    e_insert = sorted(list(g.events))[0]

    # initialize inputs
    compute_boolean_vars(e_insert, event_vars_I, event_map_I)
    for line in seq_init:
        exec(line)
    for line in comb:
        exec(line)

    # determine if the first event is replacement or insertion
    if allow_insert:
        exec(yield_expr)
    else:
        yield_out = True

    # update sequential logic
    for line in seq_next:
        exec(line)
    exec(controller_state_expr)

    # create controller automaton that starts after initial yield signal
    cntl = DFA()
    init_state = (
        (0, 0, controller_state, e_replace)
        if yield_out
        else (0, 0, controller_state, e_insert)
    )
    cntl.add_vertex(init_state)

    # for each inference, map transducer states to correct inference
    inference_results = dict()
    for inf in inf_vars:
        inference_results[inf] = dict()

    # deque stores indices of unhandled source vertex indices
    states_to_check = deque([0])

    # construct controller automaton
    while states_to_check:
        source = states_to_check.pop()
        state_i, state_o, controller_current, prev_event = cntl.vs[source]["name"]

        possible_inputs = (
            g.active_events(state_i) if prev_event is e_replace else [prev_event]
        )
        for event_i in possible_inputs:
            # compute binary variable inputs from event / controller state
            compute_boolean_vars(event_i, event_vars_I, event_map_I)
            compute_boolean_vars(
                controller_current, controller_state_vars, controller_state_map
            )

            # update combinational logic
            for line in comb:
                exec(line)
            exec(event_o_expr)
            if allow_insert:
                exec(yield_expr)
            else:
                yield_out = True
            for inf in inf_vars:
                inference_results[inf][source] = eval(inf)

            # update sequential logic
            for line in seq_next:
                exec(line)
            exec(controller_state_expr)

            # the input transitions only if we're replacing
            target_i = g.trans(state_i, event_i) if prev_event is e_replace else state_i
            target_o = g.trans(state_o, event_o)

            # next prev_event will be:
            #     e_replace if we yield
            #     e_insert if we insert and inferences don't use events
            #     the current event otherwise
            next_prev_event = (
                e_replace
                if yield_out
                else e_insert
                if not insert_holds_events
                else event_i
            )
            target_name = (target_i, target_o, controller_state, next_prev_event)

            # label is replacement if prev_event is e_replace
            label = f"{event_i}/{event_o}" if prev_event is e_replace else f"/{event_o}"

            try:
                target = cntl.vs.select(name=target_name)[0].index
            except IndexError:
                # add target if it's a new state
                target = cntl.vcount()
                cntl.add_vertex(target_name)
                states_to_check.append(target)

            # create outgoing transition
            cntl.add_edge(source, target, label)

    cntl.vs["init"] = False
    cntl.vs[0]["init"] = True

    # create predictor automata for each inference
    preds = dict()
    for inf in inf_vars:
        # may be NFA since different input may produce same output
        pred = NFA(cntl)
        # mark inference assertions as secret
        pred.vs["secret"] = [inference_results[inf][v.index] for v in pred.vs]
        # replace events with their output events
        pred.es["label"] = [e["label"].split("/")[1] for e in pred.es]
        # simplify predictor by constructing a simulation
        pred = construct_bisimulation(pred)
        preds[inf] = pred

    # simplify controller by constructing a bisimulation
    cntl = construct_bisimulation(cntl)

    return cntl, preds


def compute_boolean_vars(var, var_list, var_map):
    """
    Given a variable var, sets its corresponding global boolean variables so that they encode the value of var.

    Parameters:
    var: The variable
    var_list: A list of the boolean variables used to encode the values
    var_map: A map from a value to a formula over the boolean variables representing it
    """
    for x in var_list:
        if var not in var_map or f"!{x}" in var_map[var]:
            exec(f"global {x}; {x} = False")
        else:
            exec(f"global {x}; {x} = True")
