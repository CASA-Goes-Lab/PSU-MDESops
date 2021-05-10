import getopt
import os
import os.path
import sys
from pathlib import Path

from DESops.opacity.edit_to_bosy import write_bosy_insertion_system
from DESops.opacity.parse_smv import make_human_readable, smv_to_automaton

# This program relies on BoSy and Aiger.
# Note BoSy relies on swift. Ensure this is in your path
# Ensure bosy is properly installed and placed in a directory with write/execute permissions
# (I had to move it to my home directory)
# Change the path to Bosy here appropriately
bosy_path = "/".join([str(Path.home()), "libraries/bosy"])
# Also ensure that Aiger is installed at the following path
aiger_path = "/".join([str(Path.home()), "libraries/aiger-1.9.9"])
# Note there are currently some issues with non-absolute paths


def run_bosy(g, base_path, ins_bound=None):
    """
    Use BoSy to synthesize a controller that obfuscates secret behavior while preserving discernability.
    Returns an automaton representation of the controller.

    Parameters:
    g: The automaton
    base_path: The base path/filename where bosy/aag/smv files will be written
    ins_bound: The bound on the number of consecutive insertions allowed (None specifies finite insertions)
    """
    input_bosy_path = base_path + ".bosy"
    smv_in_path = base_path + "._smv"
    smv_out_path = base_path + ".smv"

    write_bosy_insertion_system(input_bosy_path, g, smv_in_path, ins_bound)
    bosy_main(input_bosy_path)

    make_human_readable(smv_out_path, g)
    g_out = smv_to_automaton(smv_out_path, g)

    return g_out


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
