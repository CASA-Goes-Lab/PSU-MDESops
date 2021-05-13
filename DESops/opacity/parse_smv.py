from _collections import deque
from DESops.automata.NFA import NFA
from DESops.opacity.bisimulation import construct_bisimulation, construct_simulation
from DESops.opacity.edit_to_bosy import get_bool_vars


def make_human_readable(smv_path, g):
    """
    Edit an smv file representing the environment and controller to add human readable event and state variables.

    Parameters:
    smv_path: Path to the smv file representing the controller
    g: The automaton that the original bosy file was created from
    """
    states = list(range(g.vcount()))
    events = sorted(list(g.events))

    with open(smv_path, "r") as smv_file:
        contents = smv_file.read().splitlines()

    # Count number of latches
    num_latches = sum(line.startswith("__latch_s") for line in contents)
    controller_states = list(range(2 ** num_latches))

    # Encode automaton states/events and controller states as boolean variables
    bool_vars = get_bool_vars(g, num_latches)
    state_map_I = bool_vars["state_map_I"]
    state_map_O = bool_vars["state_map_O"]
    event_map_I = bool_vars["event_map_I"]
    event_map_O = bool_vars["event_map_O"]
    controller_state_map = bool_vars["controller_state_map"]

    i = contents.index("VAR")
    contents.insert(
        i + 1,
        f"event_i : {{{', '.join(events)}, undef}};\n"
        + f"event_o : {{{', '.join(events)}, undef}};\n"
        + f"state_i : {{{', '.join(str(s) for s in states)}, undef}};\n"
        + f"state_o : {{{', '.join(str(s) for s in states)}, undef}};\n"
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
        + "state_i := "
        + "".join(f"{state_map_I[s]} ? {s} : " for s in states)
        + "undef;\n"
        + "state_o := "
        + "".join(f"{state_map_O[s]} ? {s} : " for s in states)
        + "undef;\n"
        + "controller_state := "
        + "".join(f"{controller_state_map[c]} ? {c} : " for c in controller_states)
        + "undef;",
    )
    contents[i + 1] = contents[i + 1].replace("&&", "&")

    with open(smv_path, "w") as smv_file:
        smv_file.write("\n".join(contents))


def smv_to_automata(smv_path, g, inferences=None, simplify=True):
    """
    Returns an automaton that captures the behavior of the synthesized controller described in the smv file

    Parameters:
    smv_path: Path to the smv file
    g: The automaton that the original bosy file was created from
    """
    if inferences is None:
        inferences = ["s_OO"]

    events = sorted(list(g.events))

    with open(smv_path, "r") as smv_file:
        contents = smv_file.read().splitlines()

    # Count number of latches
    num_latches = sum(line.startswith("__latch_s") for line in contents)

    # Encode automaton states/events and controller states as boolean variables
    bool_vars = get_bool_vars(g, num_latches)
    state_vars_I = bool_vars["state_vars_I"]
    state_map_I = bool_vars["state_map_I"]
    event_vars_I = bool_vars["event_vars_I"]
    event_map_I = bool_vars["event_map_I"]
    controller_state_vars = bool_vars["controller_state_vars"]
    controller_state_map = bool_vars["controller_state_map"]

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

        # rename yield since it is a Python keyword
        line = line.replace("yield", "_yield")

        if "init(" in line:
            line = line.replace("init(", "")
            line = line.replace(")", "")
            seq_init.append(line)

        elif "next(" in line:
            line = line.replace("next(", "")
            line = line.replace(")", "")
            seq_next.append(line)

        elif line.startswith("global event_i"):
            event_i_expr = line

        elif line.startswith("global event_o"):
            event_o_expr = line

        elif line.startswith("global state_i"):
            state_i_expr = line

        elif line.startswith("global state_o"):
            state_o_expr = line

        elif line.startswith("global controller_state"):
            controller_state_expr = line

        elif line.startswith("global _yield"):
            yield_expr = line

        else:
            comb.append(line)

    # suppress error from undefined variables
    global event_i
    global event_o
    global state_i
    global state_o
    global controller_state
    global _yield

    # compute inital controller state
    for line in seq_init:
        exec(line)
    exec(controller_state_expr)

    init_states = [
        (v.index, v.index, "begin", controller_state) for v in g.vs if v["init"]
    ]
    states_to_check = deque(range(len(init_states)))

    # controller automaton
    cntl = NFA()
    cntl.add_vertices(len(init_states), init_states)
    cntl.vs["init"] = True

    inference_results = [dict() for _ in inferences]

    # construct controller automaton
    while states_to_check:
        source_index = states_to_check.pop()
        state_i, state_o, event_i, controller_state = cntl.vs[source_index]["name"]

        # compute binary variable inputs from state / event / controller state
        compute_boolean_vars(state_i, state_vars_I, state_map_I)
        compute_boolean_vars(event_i, event_vars_I, event_map_I)
        compute_boolean_vars(
            controller_state, controller_state_vars, controller_state_map
        )

        # compute internal signals
        for line in comb:
            exec(line)
        exec(yield_expr)

        # compute next controller_states
        for line in seq_next:
            exec(line)
        exec(controller_state_expr)

        # find next label/event pairs
        if _yield:
            outs = g.vs[state_i]["out"]
        else:
            outs = [(state_i, "")]

        source_event = event_i

        # record the value of each inference that is made
        for i, inf in enumerate(inferences):
            inference_results[i][source_index] = eval(inf)

        # find next states
        for out in outs:
            state_i = out[0]
            event_i = out[1] if out[1] else source_event

            # compute binary variable inputs from state / event / controller state
            compute_boolean_vars(state_i, state_vars_I, state_map_I)
            compute_boolean_vars(event_i, event_vars_I, event_map_I)
            compute_boolean_vars(
                controller_state, controller_state_vars, controller_state_map
            )

            # compute intermediate signals
            for line in comb:
                exec(line)

            # compute outputs at target state
            exec(event_o_expr)
            exec(state_o_expr)

            target = (state_i, state_o, event_i, controller_state)
            label = f"{out[1]}/{event_o}"

            # add vertex if it hasn't already been added
            if target not in cntl.vs["name"]:
                target_index = cntl.vcount()
                cntl.add_vertex(target)
                states_to_check.append(target_index)
            else:
                target_index = cntl.vs["name"].index(target)

            # create outgoing transition
            cntl.add_edge(source_index, target_index, label)

    # create predictor automata for each inference
    preds = list()
    for i, inf in enumerate(inferences):
        pred = cntl.copy()
        # mark inference assertions as secret
        pred.vs["secret"] = [inference_results[i][v.index] for v in pred.vs]
        # replace events with their output events
        pred.es["label"] = [e["label"].split("/")[1] for e in pred.es]
        if simplify:
            # simplify by constructing a simulation
            pred = construct_simulation(pred)
        preds.append(pred)

    if simplify:
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
