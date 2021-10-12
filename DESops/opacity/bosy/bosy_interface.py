import getopt
import os.path
import sys
from collections.abc import Iterable
from pathlib import Path

from DESops.opacity.bosy.buchi import add_safe_state, compose_buchi, construct_buchi_cso
from DESops.opacity.bosy.edit_to_bosy import get_bool_vars, write_bosy_hyper
from DESops.opacity.bosy.parse_smv import (
    make_human_readable,
    read_smv,
    write_partial_smv,
)
from DESops.opacity.bosy.spin import ltl2spin, read_spin, write_spin

# This program relies on BoSy and Aiger.
# Note BoSy relies on swift. Ensure this is in your path
# Ensure bosy is properly installed and placed in a directory with write/execute permissions
# (I had to move it to my home directory)
# Change the path to Bosy here appropriately
bosy_path = "/".join([str(Path.home()), "libraries/bosy"])
# Also ensure that Aiger is installed at the following path
aiger_path = "/".join([str(Path.home()), "libraries/aiger-1.9.9"])
# Note there are currently some issues with non-absolute paths


def run_bosy(
    base_path,
    g,
    ltl_spec=None,
    event_var_maps=None,
    inf_fun=None,
    inf_vars=None,
    ins_bound=1,
    insert_holds_events=True,
    valid_replaces=None,
):
    """
    Use BoSyHyper to enforce current-state opacity with inferability

    PARAMETERS:
        base_path: the base path/filename where the bosy, aiger, and smv files should be written

        g: a DFA for which opacity should be enforced while preserving inferability
            (for NFAs, first determinize them, and then update the LTL spec and inference
            functions to use the states of the determinization instead of the original states)

        ltl_spec: a string (or list of strings) containing LTL specifications that should be
            enforced in addition to enforcing CSO.
            State variables should as x{i} where i is the state index
            Event variables should just be the event name.
            For example, to specify that the inference variable "z_0" should eventually become true
                iff event "a" occurs at any point or state 2 is visited at any point, let
                ltl_spec = "G ((a || x2) <-> F z_0)"

        event_var_maps: a dict that contains var lists and maps for the input and output events
            May optionally contain "obs" versions, which denote the bits that are observable
            by the obfuscator and inferrer
            May optionally contain "cntr" version, which denote the bits that are editable
            by the obfuscator
            (The contact_event_maps() function in opacity/contact_tracing/generate_contact_model.py
            gives an example of the optional "obs" and "cntr" versions)
            Default: events are encoded using the get_bool_vars() function from edit_to_bosy.py

        inf_fun: a function (or list of functions) that takes two parameters:
                x: the target state
                e: the current event
            and returns the value that some inference variable {var} should have when
            the system transitions from state x1 to x2 via event e, as either the string
            "{var}" or "!{var}"
            If insertion is allowed, then the same functions are used on insertions, except
            that x1 = x2 is the current state, and e is the most recent event

        inf_vars: a list of the names of the inference variables whose behavior is defined by ltl_spec or inf_fun

        ins_bound: the bound on the number of consecutive insertions allowed (None specifies finite insertions)
            Default: 1 (event replacement only)

        insert_holds_events: if True (default), then on input events must remain as the previous event on insertions
            if False, then this requirement is dropped, allowing for a smaller buchi automaton

        valid_replaces: a dict that maps each event to the set of events that they are allowed to be replaced by
            if not specified, then any event can be replaced by any other event


    RETURNS:
        cntl: The controller automaton
        preds: A dict mapping each inference variable to its "predictor" automaton that marks runs in which the inference is made
            (Warning: correctness of predictor automata are unverified; use at your own risk)
    """
    if event_var_maps is None:
        event_var_maps = get_bool_vars(g)
    if inf_fun is None:
        inf_fun = list()
    if inf_vars is None:
        inf_vars = list()

    if ltl_spec:
        # join multiple LTL specs
        if isinstance(ltl_spec, Iterable):
            ltl_spec = [f"({spec})" for spec in ltl_spec]
            ltl_spec = f"{' && '.join(ltl_spec)}"
        # start enforcing LTL spec after initial transition
        ltl_spec = f"X ({ltl_spec})"

    # if inf_fun is a single function, make it a list
    if callable(inf_fun):
        inf_fun = [inf_fun]

    input_bosy_path = f"{base_path}.bosy"
    _smv_path = f"{base_path}._smv"
    smv_path = f"{base_path}.smv"

    allow_insert = False
    if ins_bound != 1:
        allow_insert = True
        if ins_bound is None:
            finite_insertion = "G F yield_out"
        else:
            if ins_bound <= 0:
                raise ValueError("Insertion bound must be at least 1 (no deletions).")
            finite_insertion = (
                "G (" + " || X (".join(["yield_out"] * ins_bound) + ")" * ins_bound
            )
        # if no LTL spec, finite insertion is the only requirement
        if ltl_spec is None:
            ltl_spec = finite_insertion
        # if we also have LTL spec, we conjunct the two
        else:
            ltl_spec = f"({finite_insertion}) && ({ltl_spec})"

    # write HyperLTL in bosy file
    write_bosy_hyper(input_bosy_path, event_var_maps, inf_vars, allow_insert)
    # encode transitions in partial smv file
    write_partial_smv(_smv_path, g, event_var_maps)

    if ltl_spec is not None:
        # convert LTL spec to automaton
        ltl2spin("tmp.spin", ltl_spec)
        g_ltl = read_spin("tmp.spin")
        g_ltl = add_safe_state(g_ltl)

    # construct initial buchi
    h = construct_buchi_cso(
        g,
        event_var_maps,
        inf_fun,
        allow_insert,
        insert_holds_events,
        valid_replaces,
    )
    if ltl_spec is not None:
        # compose CSO buchi with ltl
        h = compose_buchi(h, g_ltl, event_var_maps)

    # write final result to bosy spin file
    write_spin(f"{bosy_path}/in.spin", h)

    # run bosy
    print("calling BoSy")
    bosy_main(input_bosy_path)

    # read resulting smv as automaton
    make_human_readable(smv_path, g, event_var_maps)
    return read_smv(
        smv_path, g, event_var_maps, inf_vars, allow_insert, insert_holds_events
    )


def synthesize_bosy(bosy_path, aag_path):
    """
    Synthesize a controller from hyperLTL specifications using bosy.

    Parameters:
    bosy_path: the path for the input bosy file
    aag_path: the path for the Aiger (.aag) file
    """
    print(os.popen("echo $PATH").read())
    os.system(
        f"swift run -c release BoSyHyper --synthesize {bosy_path} | sed -ne '/^aag.*/,$ p' > {aag_path}"
    )


def check_unrealizable_bosy(bosy_path):
    """
    Check if a hyperLTL specification is unrealizable using bosy.

    Parameters:
    bosy_path: the path for the input bosy file
    """
    print(os.popen(f"swift run -c release BoSyHyper --environment {bosy_path}").read())


def aag_to_smv(aag_path, smv_path):
    """
    Convert a Aiger (.aag) file to an SMV file. Ouput variables are appropriately renamed

    Parameters:
    aag_path: path to the input .aag file
    smv_path: path the the output smv file
    """
    output_map = {}
    with open(aag_path, "r") as aag_file:
        for line in aag_file.readlines():
            if line.startswith("o"):
                lsplit = line.split(" ")
                output_map[lsplit[0]] = lsplit[1].strip()

    smv_stream = os.popen(f"{aiger_path}/aigtosmv {aag_path}").read()
    with open(smv_path, "w") as smv_file:
        for line in smv_stream.splitlines():
            if line.startswith("o"):
                tmp = line.split(" ")
                tmp[0] = output_map[tmp[0]]
                line = " ".join(tmp)
                smv_file.write(line)
            else:
                smv_file.write(line)
            smv_file.write("\n")


def append_env_smv(smv_path, env_smv_path):
    """
    Append a partial smv file representing the environment to the the smv file representing the controller.

    Parameters:
    smv_path: path to the smv file representing the controller
    env_smv_path: path to the partial smv file representing the environment
    """
    with open(smv_path, "a") as smv_file, open(env_smv_path, "r") as env_file:
        smv_file.write(env_file.read())


def synthesize_smv(bosy_path, aag_path, env_smv_path, smv_path):
    """
    Synthesize an smv file representing the environment and controller from a hyperLTL specification using bosy.

    Parameters:
    bosy_path: path to the input bosy file
    aag_path: path to write the intermediate .aag file
    env_smv_path: path to the input partial smv path
    smv_path: path to the output smv file
    """
    synthesize_bosy(bosy_path, aag_path)
    aag_to_smv(aag_path, smv_path)
    append_env_smv(smv_path, env_smv_path)


def bosy_main(
    input_bosy_path,
    output_smv_path=None,
    output_aag_path=None,
    input_smv_path=None,
    check_unrealizable=False,
):
    if output_smv_path is None:
        output_smv_path = os.path.splitext(input_bosy_path)[0] + ".smv"
    if output_aag_path is None:
        output_aag_path = os.path.splitext(input_bosy_path)[0] + ".aag"
    if input_smv_path is None:
        input_smv_path = os.path.splitext(input_bosy_path)[0] + "._smv"

    cwd = os.getcwd()
    abs_input_bosy_path = "/".join([cwd, input_bosy_path])
    abs_output_smv_path = "/".join([cwd, output_smv_path])
    abs_output_aag_path = "/".join([cwd, output_aag_path])
    abs_input_smv_path = "/".join([cwd, input_smv_path])

    os.chdir(bosy_path)

    if check_unrealizable:
        check_unrealizable_bosy(input_bosy_path)
    else:
        synthesize_smv(
            abs_input_bosy_path,
            abs_output_aag_path,
            abs_input_smv_path,
            abs_output_smv_path,
        )

    os.chdir(cwd)


# a command line interface is provided for convenience
if __name__ == "__main__":

    usage = (
        "bosy_interface.py usage:\n"
        + "python3 bosy_interface.py -u -o <output-smv-file> -a <output-aag-file> -s <input-partial-smv-file> [input-bosy-file]\n"
        + "Run bosy for hyperLTL on provided input file to synthesize a controller\n"
        + "If the flag -u is specified then unrealizability is checked instead."
    )
    try:
        opts, args = getopt.getopt(
            sys.argv[1:], "huo:a:s:", ["output_smv=", "output_aag=", "input_smv="]
        )
    except getopt.GetoptError:
        print(usage)
        sys.exit(2)

    if len(args) != 1:
        print(usage)
        sys.exit(2)
    input_bosy_path = args[0]

    output_smv_path = None
    output_aag_path = None
    input_smv_path = None
    check_unrealizable = False
    for opt, arg in opts:
        if opt == "-h":
            print(usage)
            sys.exit()
        elif opt in ("-u"):
            check_unrealizable = True
        elif opt in ("-o", "--output_smv"):
            output_smv_path = arg
        elif opt in ("-a", "--output_aag"):
            output_aag_path = arg
        elif opt in ("-s", "--input_smv"):
            input_smv_path = arg

    bosy_main(
        input_bosy_path,
        output_smv_path,
        output_aag_path,
        input_smv_path,
        check_unrealizable,
    )
