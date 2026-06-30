"""
efsm_to_DFA.py

Reads an EFSM from a .efsm file and converts it into a
DFA object using subset construction.


.efsm file format:

VAR <name> <val1> <val2> ...      define a variable and its possible values
CTRL <event>                      controllable event
UCTRL <event>                     uncontrollable event
INIT <var>=<val> <var>=<val> ...  starting values
MARK <var>=<val> <var>=<val> ...  a marked state
TRANS <src> <event> <tgt>         a transition. src/tgt look like "status=0,cond=0"

Example:
VAR status 0 1
VAR cond 0 1
CTRL on
CTRL off
UCTRL fail
INIT status=0 cond=0
MARK status=0 cond=0
TRANS status=0,cond=0 on status=1,cond=0
TRANS status=1,cond=0 off status=0,cond=0
TRANS status=1,cond=0 fail status=1,cond=1
"""

from collections import deque
from DESops.automata.DFA import DFA
from DESops.automata.event import Event

# Section 1: small helper functions for converting between variable assignment
# dicts like {"status": 0, "cond": 0} and strings like "cond=0,status=0"

# Conversion is necessary because Python dicts are unhashable (can't be used as 
# dict keys or put into a set). Since strings are hashable, the fix is to convert
# to be able to check if the combinations of varible values already exist.

def assignment_to_string(assignment):
    """Turn {"status": 0, "cond": 0} into a string key like 'cond=0,status=0' so it is hashable.
    
    METHOD:
        1. Sort the variable names alphabetically. This part
           guarantees that the same assignment always produces
           the same string, no matter what order the variables happen to
           be in the dict. Without sorting, {"status":0,"cond":0} and
           {"cond":0,"status":0} (same data, different order) would turn
           into two different strings, which would break all the lookups.
        2. Build "var=val" for each variable.
        3. Join them all together with commas.
 
    EXAMPLE:
        assignment_to_string({"status": 0, "cond": 0})
        -> sorted variable names: ["cond", "status"]
        -> pieces: ["cond=0", "status=0"]
        -> result: "cond=0,status=0"
 
    NOTE:
        This is not the reverse of parse_assignment() below, even though
        they look related. This function's job is to make a hashable version
        of a dict that already has real values.
        parse_assignment()'s job is to read raw text off of a file line.
        They are two separate tools that use a similar "var=val,var=val" text style.
        """
    
    var_names = sorted(assignment.keys())                   # sort step
    parts = []
    for var in var_names:
        parts.append(var + "=" + str(assignment[var]))      # build parts
    return ",".join(parts)                                  # return hashable translation


def parse_assignment(text):
    """Turn "status=0,cond=0" raw text from file into {"status": "0", "cond": "0"} (values still strings).

    METHOD:
        1. Split the text on commas to get each "var=val" piece.
        2. Split each piece on "=" to get the variable name and the value.
        3. Store them in a dict.
 
    EXAMPLE:
        parse_assignment("status=0,cond=0")
        -> {"status": "0", "cond": "0"}
 
    NOTE:
        The values in the returned dict are still strings ("0", not the number 0).
        The code that calls this function (in read_efsm below) is
        responsible for converting "0" into the real value 0 by checking
        it against the variable's declared domain (see the VAR lines in defined .efsm format).
        This function does not know about variable domains, so it can't
        do that conversion itself.
    """
    assignment = {}
    pieces = text.split(",")                                # first split for pieces
    for piece in pieces:
        var, val = piece.split("=")                         # second split for name and value
        assignment[var] = val                               # create dict with stored information
    return assignment


def read_efsm(filename):
    """Read a .efsm file and return all the pieces as a dictionary.
    
    METHOD:
        Read the file one line at a time. Each line starts with a
        "keyword" (VAR, CTRL, UCTRL, INIT, MARK, or TRANS) that tells
        what kind of line it is so we can handle each keyword differently.
        Blank lines and lines starting with "#" (comments) are skipped.
 
    RETURNS:
        A dictionary holding everything parsed, so the caller
        (efsm_to_dfa below) can grab whichever pieces it needs.
    """

    # information that fills as we read the file:
    variables = {}          # var name -> list of possible values, ex: {"status": [0, 1]}
    ctrl_events = set()     # controllable events
    uctrl_events = set()    # uncontrollable events
    initial = {}            # starting variable assignment, ex: {"status": 0, "cond": 0}
    marked_list = []        # list of marked states (variable assignments)
    transitions = []        # list of (source dict, event, target dict) tuples

    # first read whole file into memory as list of lines
    f = open(filename, "r")
    lines = f.readlines()
    f.close()

    for line in lines:
        line = line.strip()                                 # remove uneccessary characters

        if line == "" or line.startswith("#"):              # skip blank and comment lines
            continue

        words = line.split()                                # split line on whitespace
        keyword = words[0]                                  # first word tells what kind of data this line holds

        if keyword == "VAR":                                
            var_name = words[1]
            values = []
            for w in words[2:]:
                try:                                        # try to read value as a number
                    values.append(int(w))
                except ValueError:                          # if that fails, keep as plain text
                    values.append(w)
            variables[var_name] = values                    # populate variables dict

        elif keyword == "CTRL":                             
            ctrl_events.add(words[1])

        elif keyword == "UCTRL":
            uctrl_events.add(words[1])

        elif keyword == "INIT":
            text = ",".join(words[1:])                      # words[1:] looks like ["status = 0", "cond=0"] -> join with commas for parse_assignment()
            raw = parse_assignment(text)                    # make raw dict of real values from text
            for var in raw:                                 # for each variable, look through domain and store matching value
                for v in variables[var]:
                    if str(v) == raw[var]:
                        initial[var] = v

        elif keyword == "MARK":
            text = ",".join(words[1:])                      # same process for marked states
            raw = parse_assignment(text)                   
            mark_dict = {}
            for var in raw:
                for v in variables[var]:
                    if str(v) == raw[var]:
                        mark_dict[var] = v
            marked_list.append(mark_dict)

        elif keyword == "TRANS":
            src_text = words[1]                             # store source text, event, and target text
            event = words[2]
            tgt_text = words[3]

            raw_src = parse_assignment(src_text)            # make raw dicts
            raw_tgt = parse_assignment(tgt_text)

            src_dict = {}
            for var in raw_src:                             # using same method, make string values to real values for source
                for v in variables[var]:
                    if str(v) == raw_src[var]:
                        src_dict[var] = v

            tgt_dict = {}                                   # using same method, make string values to real values for target
            for var in raw_tgt:
                for v in variables[var]:
                    if str(v) == raw_tgt[var]:
                        tgt_dict[var] = v

            transitions.append((src_dict, event, tgt_dict))


    # Put all information into one dictionary so the caller function can reference whatever data pieces it needs by name:
    result = {}
    result["variables"] = variables
    result["ctrl_events"] = ctrl_events
    result["uctrl_events"] = uctrl_events
    result["initial"] = initial
    result["marked_list"] = marked_list
    result["transitions"] = transitions
    return result


def enumerate_all_states(variables):
    """Make a list of every possible combination of variable values with the cartesian product. 
    
    An EFSM describes states using variables, but a DFA needs plain individual states. By making every possible combination
    of variable values, this function outlines all the different states possible in a standard DFA.

    METHOD:
        Start with a list containing just the empty dict {}.
        Then, for each variable one at a time, take every state built so
        far and make one copy of it for every possible value of that variable.
        After processing all variables, every state in the list has a value
        for every variable, and every possible combination has been generated exactly once.
 
    EXAMPLE:
      
        Walkthrough with variables {"status": [0, 1], "cond": [0, 1]}:
 
        Start:
            [{}]
 
        Process "status":
            from {} make {"status":0} and {"status":1}
            
        After "status":
            [{"status":0}, {"status":1}]
 
        Process "cond":
            from {"status":0} make {"status":0,"cond":0} and {"status":0,"cond":1}
            from {"status":1} make {"status":1,"cond":0} and {"status":1,"cond":1}
        
        After "cond":
            [{"status":0,"cond":0}, {"status":0,"cond":1}, {"status":1,"cond":0}, {"status":1,"cond":1}]
 
        This is all 4 combinations (2 values x 2 values).
    
    """
    var_names = list(variables.keys())

    all_states = [{}]                                       # start with one empty state
    for var in var_names:
        new_all_states = []                                 # expanded list of all states
        for state in all_states:
            for value in variables[var]:                    
                new_state = dict(state)                     # copy partial state so as not to accidentally modify a dict
                new_state[var] = value
                new_all_states.append(new_state)
        all_states = new_all_states                         # replace original list with expanded one and move on to next variable

    return all_states


def efsm_to_dfa(filename):
    """Read a .efsm file and convert it to a DFA object.
    
    This is the main function to call from outside of this file. Give a path to a .efsm file, and it gives back a DFA object
    representing the same automaton.
    
    METHOD:
        1. Read and parse the .efsm file (see read_efsm above).
        2. Generate every possible concrete state (see enumerate_all_states above).
        3. Build a simple lookup table that outlines transitions
        4. Run subset construction: starting from the initial state,
           explore outward, where each DFA state is actually a set of
           concrete states (called a "macro state"). See below for further explanation.
        5. Build the DFA object and return it.
    
    """

    # Step 1: parse the file
    data = read_efsm(filename)                              # take the data from the file and store it
    variables = data["variables"]
    ctrl_events = data["ctrl_events"]
    uctrl_events = data["uctrl_events"]
    initial = data["initial"]
    marked_list = data["marked_list"]
    transitions = data["transitions"]
    all_events = ctrl_events | uctrl_events                 # union together controllable and uncontrollable events for all events

    # Step 2: generate every possible concrete state
    all_states = enumerate_all_states(variables)
                                                      
    state_to_number = {}
    for i in range(len(all_states)):                        # give each concrete state a number using its string key to simplify process
        key = assignment_to_string(all_states[i])
        state_to_number[key] = i

    
    marked_keys = set()
    for m in marked_list:                                   # turn marked states into a set of string keys to simplify process
        marked_keys.add(assignment_to_string(m))

    # Step 3: build lookup table
    # Build this once upfront so that later for subset construction the table allows easy trans access.

    step_table = {}                                         # step_table maps (source_key, event) -> list of target dicts
    for src_dict, event, tgt_dict in transitions:
        key = (assignment_to_string(src_dict), event)
        if key not in step_table:
            step_table[key] = []
        step_table[key].append(tgt_dict)

    # Step 4: subset construction:
    # The big idea is that each DFA state can represent a whole set of concrete EFSM states (a "macro state").
    # Start with macro state containing just the initial state, then explore outward.
    # For every macro state and for every event, compute the set of all concrete states reachable via that event from any state in the current macro state.
    # The resulting set becomes a new macro state or reuses one already visited.
    # Continue this process until there are no more new macro states.
    # Each macro state becomes one vertex in the final DFA, and every transition between macro states becomes an edge between their corresponding vertices in the final DFA.

    start_number = state_to_number[assignment_to_string(initial)]                           # starting macro state of just the initial concrete state
    start_macro = frozenset([start_number])                                                 # use frozenset because they are hashable

    macro_to_dfa_index = {start_macro: 0}                                                   # create index to remember which DFA state number assigned to each macro state (start gets 0)
    queue = deque()                                                                         # create double-ended queue of macro states that still need to be processed so popping from front is fast
    queue.append(start_macro)

    dfa_edges = []                                                                          # collect list of edges as tuples like (from_dfa_index, to_dfa_index, event) so we can build DFA object later all at once

    while len(queue) > 0:
        current_macro = queue.popleft()                                                     # take next macro state for processing off front of queue
        current_index = macro_to_dfa_index[current_macro]

        for event in all_events:                                                            # try every possible event and see where it leads
            reachable_numbers = set()                                                       # collect every concrete state reachable via this event from any state inside the current macro state

            for state_number in current_macro:
                state_dict = all_states[state_number]
                key = (assignment_to_string(state_dict), event)
                if key in step_table:                                                       # look up the (state, event) pair in the table -> if it's not there, the event doesn't work from this state so skip it
                    for tgt_dict in step_table[key]:
                        tgt_number = state_to_number[assignment_to_string(tgt_dict)]
                        reachable_numbers.add(tgt_number)

            if len(reachable_numbers) == 0:                                                 # if nothing was reachable from the macro state, no transition to add so move on
                continue

            next_macro = frozenset(reachable_numbers)                                       # everything found becomes the next macro state

            if next_macro not in macro_to_dfa_index:                                        # if this is a new macro state, assign it an index and add it to the queue for processing
                macro_to_dfa_index[next_macro] = len(macro_to_dfa_index)
                queue.append(next_macro)

            next_index = macro_to_dfa_index[next_macro]                                     # either way, record the transition
            dfa_edges.append((current_index, next_index, event))

    # Step 5: build the DFA object

    Euc_events = set()                                                                      # make the set of uncontrollable events for the DFA constructor using the Event class
    for e in uctrl_events:                                                                  
        Euc_events.add(Event(e))

    dfa = DFA(Euc=Euc_events, check_DFA=False)                                              # make the final DFA -> check_DFA=False tells the DFA constructor to not bother verifying determinism since it is guaranteed by subset construction

    index_to_macro = {}                                                                     # flip the index dict around to index -> macro state instead of macro state -> index so that the states can be added in the correct order
    for macro in macro_to_dfa_index:
        index_to_macro[macro_to_dfa_index[macro]] = macro

    for i in range(len(macro_to_dfa_index)):                                                # add one DFA vertex per macro state in index order so that the edges collected earlier correspond to the right indices
        macro = index_to_macro[i]

        is_marked = True                                                                    # a macro state is considered marked only if every concrete state inside is marked, so check for that and if not, check is_marked to False
        for state_number in macro:
            state_dict = all_states[state_number]
            if assignment_to_string(state_dict) not in marked_keys:
                is_marked = False

        name_parts = []                                                                     # build a name for the vertex by listing out the concrete states it represents
        for state_number in sorted(macro):
            name_parts.append(str(all_states[state_number]))
        name = "{" + ", ".join(name_parts) + "}"

        dfa.add_vertex(name=name, marked=is_marked)                                         # add the vertex

    edge_pairs = []                                                                         # generate lists of edges and labels for add_edges() method
    edge_labels = []
    for (src, tgt, event) in dfa_edges:                                                     # split source, target, and event pieces apart for the two lists
        edge_pairs.append((src, tgt))
        edge_labels.append(Event(event))

    if len(edge_pairs) > 0:                                                                 # only add edges if there is at least one edge
        dfa.add_edges(edge_pairs, edge_labels, check_DFA=False, fill_out=True)

    dfa_events = set()                                                                      # record the full set of events on the DFA object
    for e in all_events:
        dfa_events.add(Event(e))
    dfa.events = dfa_events

    return dfa                                                                              # finally, return the DFA



# For evidence of working correctly (copied and changed from internet)
# This prints the representation of the DFA object created when ran in the terminal
if __name__ == "__main__":
    import sys
    if len(sys.argv) != 2:
        print("Usage: poetry run python .\DESops\file\efsm_to_DFA_new.py <file.efsm>")
        sys.exit(1)

    dfa = efsm_to_dfa(sys.argv[1])
    print(dfa.summary(use_state_names=True))