import os

from DESops.automata.NFA import NFA


def read_spin(filename):
    """
    Read a spin file and return it as a marked NFA

    Parameters:
    filename: the path/filename of the spin file that should be read

    Return:
    G_out: the marked NFA
    """
    with open(filename, "r") as f:
        contents = f.read().splitlines()

    # create new automaton from states
    G_out = NFA()
    states = [line[:-1] for line in contents if line.endswith(":")]
    marked = [s.startswith("accept") for s in states]
    G_out.add_vertices(len(states), states, marked)
    G_out.vs["init"] = [s.endswith("init") for s in states]

    for line in contents:
        # skips lines that aren't states or transitions
        skip_prefixes = ["never {", "}", "  if", "  fi"]
        if any(line.startswith(pre) for pre in skip_prefixes):
            continue

        # keep track of which state we're on
        if line.endswith(":"):
            source_name = line[:-1]
            source = states.index(source_name)
            continue

        # skip means unconditional self-loop
        if "skip" in line:
            G_out.add_edge(source, source, "true")
            continue

        # If we've made it to here, the current line must be a transition
        # discard prefix
        line = line.replace("  :: ", "")
        # extract guard condition and target state
        condition, target_name = line.split(" -> goto ")
        target = states.index(target_name)

        G_out.add_edge(source, target, condition)

    # marked self-looping accepting states as dead
    G_out.vs["dead"] = [
        v["marked"]
        and all(target == v.index and label == "true" for target, label in v["out"])
        for v in G_out.vs
    ]

    return G_out


def write_spin(filename, g):
    """
    Write a marked automaton as a spin never claim

    Parameters:
    filename: the path/filename of the spin file to be written
    g: the marked automaton
    """
    contents = list()

    # begin never claim
    contents.append("never {")

    for v in g.vs:
        # write source vertex name
        source = v.index
        contents.append(f"{spin_state_name(g, source)}:")

        # begin if
        contents.append("  if")

        # write transition statements
        for target, label in v["out"]:
            contents.append(f"  :: {label} -> goto {spin_state_name(g, target)}")

        # end if
        contents.append("  fi;")

    # end never claim
    contents.append("}")

    with open(filename, "w") as f:
        f.write("\n".join(contents))


def spin_state_name(g, index):
    """
    Generate the name that a given vertex in an automaton will be given in its spin file representation

    Parameters:
    g: the automaton
    index: the vertex index

    Returns:
    the spin state name
    """
    v = g.vs[index]

    # base name uses the original name, or converts to string if it's a tuple
    base_name = v["name"]
    if isinstance(base_name, tuple):
        base_name = f"{'_'.join(str(x) for x in base_name)}"

    # marked states are accepting
    prefix = "accept_S" if v["marked"] else "S"

    # indicate initial states
    init = v["init"] if isinstance(g, NFA) else (index == 0)
    suffix = "_init" if init else ""

    return f"{prefix}{base_name}{suffix}"


def ltl2spin(filename, ltl_spec, tmp_file="tmp.ltl"):
    """
    Use the external ltl2tgba tool to write a spin never claim representation of a
    Buchi automaton that accepts runs which do not satisfy the given LTL specification

    Parameters:
    filename: the filename of the spin file to be written
    ltl_specs: a string of the LTL specification
    tmp_file: the file to which the negated LTL spec will be written
    """
    # negate the LTL spec
    ltl_spec = f"!({ltl_spec})"

    # write the negated LTL spec to a temp file
    with open(tmp_file, "w") as f:
        f.write(ltl_spec)

    # import here to prevent circular import
    from DESops.opacity.bosy.bosy_interface import bosy_path

    # call to ltl2tgba installation from BoSy
    os.system(f"{bosy_path}/Tools/ltl2tgba --spin -F {tmp_file} > {filename}")
