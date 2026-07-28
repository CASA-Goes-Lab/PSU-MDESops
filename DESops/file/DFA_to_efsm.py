"""
dfa_to_efsm.py

Converts a DESops DFA object into an EFSM description, written as a
.efsm text file (the format defined in efsm_to_DFA_new.py).

Because a DFA has no variable structure of its own, 
the user must supply that structure:
  1. which variables exist and what values they can take
  2. which DFA state corresponds to which variable assignment

The function writes the result to an output .efsm file and returns the
content as a string in the terminal.

Potential errors raised:
    ValueError if:
      - a DFA state name is missing from state_to_assignment
      - a variable in an assignment was not declared in variables
      - an assignment value is not in that variable's declared domain
      - two different DFA states map to the same variable assignment
        (this would produce a nondeterministic EFSM)
      - an assignment does not specify every declared variable
"""

from DESops.automata.DFA import DFA
from DESops.automata.event import Event


# Validation helper functions:
# These check the user-provided inputs for consistency before
# anything is written to the file.

def _validate_inputs(dfa, variables, state_to_assignment):
    """
    PURPOSE:
        Check that the user-provided variables and state_to_assignment
        are internally complete before writing the .efsm file. Raises a
        clear ValueError for any problem found.

    CHECKS:
        1. Every DFA state name has an entry in state_to_assignment.
        2. Every assignment references only declared variables.
        3. Every assignment value is in that variable's declared domain.
        4. Every assignment specifies all declared variables (no partial assignments).
        5. No two DFA states share the same assignment (would be nondeterministic).
    """

    state_names = dfa.vs["name"]    # list of all vertex name strings in the DFA

    # check 1: every DFA state name must appear in the mapping
    for name in state_names:
        if name not in state_to_assignment:
            raise ValueError(
                "DFA state '" + str(name) + "' has no entry in state_to_assignment. "
                "Every DFA state must be mapped to a variable assignment."
            )

    for state_name, assignment in state_to_assignment.items():

        # check 2: every variable in the assignment must be declared
        for var in assignment:
            if var not in variables:
                raise ValueError(
                    "State '" + state_name + "': variable '" + var + "' in its "
                    "assignment was not declared in variables. "
                    "Add it with variables['" + var + "'] = [...]."
                )

        # check 3: every value must be in that variable's domain
        for var, val in assignment.items():
            if val not in variables[var]:
                raise ValueError(
                    "State '" + state_name + "': value '" + str(val) + "' for "
                    "variable '" + var + "' is not in its declared domain "
                    + str(variables[var]) + "."
                )

        # check 4: assignment must cover every declared variable
        missing = set(variables.keys()) - set(assignment.keys())
        if missing:
            raise ValueError(
                "State '" + state_name + "': assignment is missing variable(s) "
                + str(missing) + ". Every declared variable must be assigned a value."
            )

    # check 5: no two states share the same assignment (would be nondeterministic)
    # To check, build a reverse mapping: assignment_string -> list of state names that use it
    seen_assignments = {}
    for state_name, assignment in state_to_assignment.items():
        key = _assignment_to_string(assignment)
        if key not in seen_assignments:
            seen_assignments[key] = []
        seen_assignments[key].append(state_name)

    for key, names in seen_assignments.items():
        if len(names) > 1:
            raise ValueError(
                "Multiple DFA states share the same variable assignment '" + key +
                "': " + str(names) + ". Each state must have a unique assignment. "
                "(Merging states would produce a nondeterministic EFSM)"
            )


def _assignment_to_string(assignment):
    """
    PURPOSE:
        Turn a variable assignment dict into a string so it can
        be used as a dictionary key or compared for equality.
        Identical to the helper in efsm_to_DFA_new.py.

    EXAMPLE:
        {"status": 0, "cond": 0} -> "cond=0,status=0"
    """
    var_names = sorted(assignment.keys())   # sort so order is always consistent
    parts = []
    for var in var_names:
        parts.append(var + "=" + str(assignment[var]))
    return ",".join(parts)


# Building the .efsm file content:

def _build_efsm_content(dfa, variables, state_to_assignment):
    """
    PURPOSE:
        Walk the DFA object and produce the full text content of a .efsm
        file as a single string. The caller writes this to a file.

    METHOD:
        Build the file section by section in the order the .efsm format
        expects: VAR lines, then CTRL/UCTRL lines, then INIT, then MARK,
        then TRANS.

    RETURNS:
        str -> the complete .efsm file content
    """

    lines = []

    # Provide header comment:
    lines.append("# Auto-generated by dfa_to_efsm.py")
    lines.append("")

    # VAR lines:
    # One line per variable, listing its name and all domain values.
    # Sort variable names so the output is consistent across runs.
    lines.append("# State variables")
    for var in sorted(variables.keys()):
        domain_str = " ".join(str(v) for v in variables[var])
        lines.append("VAR " + var + " " + domain_str)                   # add content to str
    lines.append("")

    # CTRL and UCTRL lines:
    # dfa.Euc holds the uncontrollable events. Everything else in dfa.events
    # is controllable. Sort both sets so the output is consistent.
    lines.append("# Events")
    euc_labels = set()
    for e in dfa.Euc:
        # event objects print as their label string (see event.py __repr__)
        euc_labels.add(str(e))

    all_event_labels = set()
    for e in dfa.events:
        all_event_labels.add(str(e))

    ctrl_labels = all_event_labels - euc_labels     # controllable = all events minus uncontrollable

    for label in sorted(ctrl_labels):                                   # add content to str
        lines.append("CTRL " + label)
    for label in sorted(euc_labels):
        lines.append("UCTRL " + label)
    lines.append("")

    # INIT line:
    # The initial state in a DESops DFA is always vertex index 0.
    # Look up its name then its assignment.
    lines.append("# Initial state")
    initial_name = dfa.vs["name"][0]
    initial_assignment = state_to_assignment[initial_name]

    # Write as space-separated var=val pairs -> ex: "INIT status=0 cond=0"
    init_parts = []
    for var in sorted(initial_assignment.keys()):
        init_parts.append(var + "=" + str(initial_assignment[var]))
    lines.append("INIT " + " ".join(init_parts))                        # add content to str
    lines.append("")

    # MARK lines:
    # Walk all vertices and write a MARK line for every one that is marked.
    lines.append("# Marked states")
    any_marked = False
    for vertex in dfa.vs:
        if vertex["marked"]:
            any_marked = True
            assignment = state_to_assignment[vertex["name"]]
            mark_parts = []
            for var in sorted(assignment.keys()):
                mark_parts.append(var + "=" + str(assignment[var]))
            lines.append("MARK " + " ".join(mark_parts))                # add content to str

    if not any_marked:
        lines.append("# (no marked states)")                            # case if zero states are marked
    lines.append("")

    # TRANS lines:
    # Walk all edges. For each edge, look up the source and target vertex
    # names, find their assignments, and write a TRANS line.
    # TRANS uses comma-separated var=val pairs -> ex: "TRANS status=0,cond=0 on status=1,cond=0"
    lines.append("# Transitions")
    for edge in dfa.es:
        src_name = dfa.vs["name"][edge.source]
        tgt_name = dfa.vs["name"][edge.target]
        event_label = str(edge["label"])

        src_assignment = state_to_assignment[src_name]
        tgt_assignment = state_to_assignment[tgt_name]

        # build comma-separated var=val strings for source and target
        src_parts = []
        for var in sorted(src_assignment.keys()):
            src_parts.append(var + "=" + str(src_assignment[var]))
        src_str = ",".join(src_parts)

        tgt_parts = []
        for var in sorted(tgt_assignment.keys()):
            tgt_parts.append(var + "=" + str(tgt_assignment[var]))
        tgt_str = ",".join(tgt_parts)

        lines.append("TRANS " + src_str + " " + event_label + " " + tgt_str)        # add content to str

    lines.append("")
    return "\n".join(lines)


# Main conversion function:

def dfa_to_efsm(dfa, output_filename, variables, state_to_assignment):
    """
    Convert a DESops DFA object into an EFSM, then print it and write it to a .efsm file.

    PARAMETERS:
        dfa                 : DFA
            A DESops DFA object (from DESops.automata.DFA). Initial
            state is assumed to be vertex index 0, which is the DESops
            convention.

        output_filename     : str
            Path to write the .efsm output file to.
            ex: ".\\DESops\\file\\output.efsm"

        variables           : dict[str, list]
            Declares the state variables and their domains.
            ex: {"status": [0, 1], "cond": [0, 1]}
            Same format as the internal representation in efsm_to_DFA_new.py.

        state_to_assignment : dict[str, dict]
            Maps each DFA vertex name string (from dfa.vs["name"]) to a
            variable assignment dict.
            Example:
                {
                    "s0": {"status": 0, "cond": 0},
                    "s1": {"status": 1, "cond": 0},
                    "s2": {"status": 1, "cond": 1},
                }
            Every DFA state must have an entry. No two states may share
            the same assignment (would produce a nondeterministic EFSM).

    RETURNS:
        str -> the full content of the written .efsm file

    RAISES:
        ValueError if any validation check fails (see _validate_inputs).
    """

    # validate all inputs before touching the file system:
    _validate_inputs(dfa, variables, state_to_assignment)

    # build the full file content as a string:
    content = _build_efsm_content(dfa, variables, state_to_assignment)

    # write the file:
    f = open(output_filename, "w")
    f.write(content)
    f.close()

    # return the content string:
    return content


# Interactive command-line entry point:
#
# Run this file directly from the terminal to be guided through
# the conversion step by step via prompts.
#
# Usage:
#   poetry run python .\DESops\file\dfa_to_efsm.py <input.fsm> <output.efsm>
#
# The terminal will then prompt the user to:
#   1. Declare variables and their domains
#   2. Map each DFA state to a variable assignment
# Then it prints the resulting .efsm content and writes it to the ouput .efsm file.

if __name__ == "__main__":
    import sys
    # fsm_to_igraph.py must be in the same folder or on the Python path,
    # since read_fsm() is used to load the DFA from the .fsm file.
    from fsm_to_igraph import read_fsm

    # first, check and store arguments:

    if len(sys.argv) != 3:
        print("Usage: poetry run python DFA_to_efsm.py <input.fsm> <output.efsm>")
        sys.exit(1)

    input_fsm  = sys.argv[1]
    output_efsm = sys.argv[2]

    # load the DFA from the .fsm file:

    print()
    print("Reading DFA from '" + input_fsm + "'...")
    try:
        dfa = read_fsm(input_fsm)
    except Exception as e:
        # print error message if needed
        print("ERROR: could not read '" + input_fsm + "': " + str(e))
        sys.exit(1)

    # show the user what states and events were found, so they know
    # what they need to map when the prompts start
    state_names = dfa.vs["name"]
    all_event_labels = sorted(str(e) for e in dfa.events)
    euc_labels       = sorted(str(e) for e in dfa.Euc)
    ctrl_labels      = sorted(e for e in all_event_labels if e not in euc_labels)

    print("Found " + str(len(state_names)) + " state(s): " + ", ".join(str(n) for n in state_names))
    print("Found event(s): " + ", ".join(all_event_labels))
    if euc_labels:
        print("  Uncontrollable: " + ", ".join(euc_labels))
    if ctrl_labels:
        print("  Controllable:   " + ", ".join(ctrl_labels))

    # prompt the user to declare variables:

    print()
    print("Variable Declaration:")
    print("Declare the state variables and their possible values.")
    print("Type 'done' as the variable name when finished.")
    print()

    variables = {}

    while True:
        # prompt for variable name:
        var_name = input("  Variable name (or 'done'): ").strip()

        if var_name.lower() == "done":
            if len(variables) == 0:                                                                         # check for false done response
                print("  ! You must declare at least one variable before continuing.")
                continue
            break

        if var_name == "":
            print("  ! Variable name cannot be blank. Try again.")                                          # check for empty response
            continue

        # prompt for domain values (retry on same variable until valid):
        while True:
            raw_vals = input("  Values for '" + var_name + "' (space-separated, ex: 0 1): ").strip()

            if raw_vals == "":
                print("  ! You must enter at least one value. Try again.")                                  # check for empty response
                continue

            domain = []
            for w in raw_vals.split():
                try:
                    domain.append(int(w))
                except ValueError:
                    domain.append(w)

            variables[var_name] = domain
            print("  -> '" + var_name + "' registered with domain " + str(domain))
            break

    print()
    print("Variables declared: " + str(variables))

    # prompt the user to map each state to an assignment:

    print()
    print("State Mapping:")
    print("Map each DFA state to a variable assignment.")
    print("Format: var=val var=val  (ex: status=0 cond=1)")
    print("Declared variables: " + ", ".join(
        var + " in " + str(variables[var]) for var in sorted(variables)
    ))
    print()

    # build a domain_lookup so we can convert string values back to real
    # types (same trick as read_efsm in efsm_to_DFA_new.py)
    domain_lookup = {}
    for var in variables:
        domain_lookup[var] = {str(v): v for v in variables[var]}

    state_to_assignment = {}

    for state_name in state_names:
        # keep reprompting this specific state until the assignment is valid
        while True:
            raw = input("  " + str(state_name) + " -> ").strip()

            if raw == "":
                print("  ! Assignment cannot be blank. Try again.")                                         # check for empty response
                continue

            # parse the space-separated "var=val" tokens
            tokens = raw.split()
            error_found = False
            assignment = {}

            for token in tokens:
                if "=" not in token:                                                                        # check format
                    print("  ! '" + token + "' is not in var=val format. Try again.")
                    error_found = True
                    break

                var, val_str = token.split("=", 1)

                # check if the variable was declared
                if var not in variables:
                    print("  ! Variable '" + var + "' was not declared. "
                          "Declared variables are: " + ", ".join(sorted(variables.keys())))
                    error_found = True
                    break

                # check the value is in the domain
                if val_str not in domain_lookup[var]:
                    print("  ! Value '" + val_str + "' is not in the domain of '" + var + "'. "
                          "Valid values are: " + str(variables[var]))
                    error_found = True
                    break

                assignment[var] = domain_lookup[var][val_str]

            if error_found:
                continue

            # check all declared variables are covered
            missing = set(variables.keys()) - set(assignment.keys())
            if missing:
                print("  ! Assignment is missing variable(s): " + str(missing) + ". "
                      "All variables must be assigned. Try again.")
                continue

            # check for duplicate assignments (another state already used this one)
            assignment_str = _assignment_to_string(assignment)
            duplicate = None
            for already_mapped_state, already_mapped_assignment in state_to_assignment.items():
                if _assignment_to_string(already_mapped_assignment) == assignment_str:
                    duplicate = already_mapped_state
                    break

            if duplicate is not None:
                print("  ! This assignment is already used by state '" + str(duplicate) + "'. "
                      "Each state must have a unique assignment. Try again.")
                continue

            # if all checks passed, store and move on to the next state
            state_to_assignment[str(state_name)] = assignment
            break

    # run the conversion and print the result:

    print()
    print("Result:")

    try:
        content = dfa_to_efsm(dfa, output_efsm, variables, state_to_assignment)
        print(content)
        print("Written to '" + output_efsm + "'.")
    except ValueError as e:
        # this shouldn't happen since inputs were validated interactively, but just in case
        print("ERROR during conversion: " + str(e))
        sys.exit(1)
