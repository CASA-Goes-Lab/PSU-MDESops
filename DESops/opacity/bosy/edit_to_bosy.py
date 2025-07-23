import json
import math
import warnings

from DESops.automata import DFA

# https://github.com/reactive-systems/bosy

smv_next = "next"
ltl_next = "X"


def write_bosy_hyper(path, event_var_maps, inf_vars, allow_insert):
    """
    Write a bosy file that defines the inputs, outputs, and a HyperLTL specification that denote
    Assumptions and guarantees are not written, since the linear Buchi automaton is constructed outside of BoSy

    Parameters:
    path: the path/filename of the bosy file that should be written
    event_var_maps: see the definition in run_bosy() in bosy_interface.py
    inf_vars: a list of the names of the inference variables
    allow_insert: a boolean indicating whether event insertions are allowed
    """
    # Encode states and events with boolean variables
    event_vars_I = event_var_maps["event_vars_I"]
    event_vars_O = event_var_maps["event_vars_O"]
    try:
        obs_event_vars_I = event_var_maps["obs_event_vars_I"]
        obs_event_vars_O = event_var_maps["obs_event_vars_O"]
    except KeyError:
        # if observable vars are not defined, we assume full observability
        obs_event_vars_I = None  # output can only depend on inputs regardless
        obs_event_vars_O = event_vars_O
    try:
        cntr_event_vars_O = event_var_maps["cntr_event_vars_O"]
    except KeyError:
        # if controllable vars are not defined, we assume full controllability
        cntr_event_vars_O = event_vars_O

    # Setup bosy object (JSON)
    bosy = {}
    # Mealy means current outputs can depend on current inputs
    bosy["semantics"] = "mealy"

    # Set inputs and outputs for Bosy
    bosy["inputs"] = event_vars_I
    bosy["outputs"] = cntr_event_vars_O + inf_vars
    if allow_insert:
        bosy["outputs"].append("yield_out")

    # Set LTL assumptions and guarantees for Bosy
    bosy["assumptions"] = []
    bosy["guarantees"] = []

    # Setup HyperLTL constraints
    # Formula for different current outputs for two runs
    diff_output = " || ".join([f"!({e}[pi1] <-> {e}[pi2])" for e in obs_event_vars_O])
    # Formula for same current inferences for two runs
    same_inferences = [f"({var}[pi1] <-> {var}[pi2])" for var in inf_vars]
    # HyperLTL formula representing consistency of secret assertion across two runs with the same outputs
    secret_output_consistency = [
        f"forall pi1 pi2. ({s}) W ({diff_output})" for s in same_inferences
    ]

    if obs_event_vars_I is not None:
        # do same for making outputs based on observable input info
        diff_obs = " || ".join([f"!({e}[pi1] <-> {e}[pi2])" for e in obs_event_vars_I])
        same_outputs = [f"({e}[pi1] <-> {e}[pi2])" for e in cntr_event_vars_O]
        based_on_observable = [
            f"forall pi1 pi2. ({s}) W ({diff_obs})" for s in same_outputs
        ]
    else:
        # output is fully observable, so nothing is needed here
        based_on_observable = []

    # Set HyperLTL constraints for Bosy
    bosy["hyper"] = based_on_observable + secret_output_consistency

    # json.dump(bosy, sys.stdout)
    with open(path, "w") as f:
        json.dump(bosy, f, indent=4)


def write_bosy_insertion_system(
    path, g, smv_path=None, ins_bound=None, inferences=None, guarantees=None
):
    """
    Construct a system representing the composition of the underlying system (input/environment) and the
    insertion function (output). Constraints specifying the secrecy of the system and inferability are also
    constructed.  The resulting system and design constraints are represented as a list of
    assumption and guarantee LTL formulas as well as a list of hyperLTL formulas. This information is then
    written to a bosy file (json format). This file can be input to Bosy to synthesize an insertion function
    in the form of a Aiger file (.aag). This file can be converted to an SMV file for analysis.

    Additionally, if a path is provide for an smv file, this function writes the assumptions
    on the underlying system (input) to a partial smv file. This file can be concatenated with the
    smv file from synthesis to simulate the system in NuSMV.

    Parameters:
    path: The path to write the bosy file to
    g: The automaton to construct the insertion system for
    smv_path: The optional path to write the partial smv file to
    ins_bound: The bound on the number of consecutive insertions allowed (None specifies finite insertions)
    inferences: A list of variable names of the inferences that some "intended recipient" should be able to make
                Default is s_OO
    guarantees: A list of LTL specifcations for when inferences should be asserted, and for any additional custom constraints
                Required if inferences is not None
                Default is that the secret behavior of the input automaton should be inferrable
    """
    warnings.warn(
        "The files written by this function are incompatible with the modified BoSy installation that uses a cutom Buchi automaton; Use write_bosy_hyper instead"
    )

    if inferences and not guarantees:
        raise ValueError("Non-default inferences require non-default guarantees")

    states = list(range(g.vcount()))

    # Encode states and events with boolean variables
    bool_vars = get_bool_vars(g)
    state_vars_I = bool_vars["state_vars_I"]
    state_map_I = bool_vars["state_map_I"]
    state_vars_O = bool_vars["state_vars_O"]
    state_map_O = bool_vars["state_map_O"]
    event_vars_I = bool_vars["event_vars_I"]
    event_map_I = bool_vars["event_map_I"]
    event_vars_O = bool_vars["event_vars_O"]
    event_map_O = bool_vars["event_map_O"]

    if guarantees is None:
        guarantees = list()

    # Default inference is to determine whether the input run is secret
    if inferences is None:
        inferences = ["s_OO"]
        secret_I = f"({' || '.join([state_map_I[i] for i, sec in enumerate(g.vs['secret']) if sec])})"
        guarantees.append(f"G ({secret_I} <-> s_OO)")

    # Setup bosy object (JSON)
    bosy = {}
    # Mealy means current outputs can depend on current inputs
    bosy["semantics"] = "mealy"

    # Set inputs and outputs for Bosy
    auxiliary_outputs = ["yield"] + inferences
    bosy["inputs"] = event_vars_I + state_vars_I
    bosy["outputs"] = event_vars_O + state_vars_O + auxiliary_outputs

    # Setup dynamics of the system
    # Init formulas
    init_state = g.vs.select(init=True)[0].index
    init_I = [f"{state_map_I[init_state]}"]
    init_O = [f"{state_map_O[init_state]}"]

    # Transition formulas
    trans_I = [
        f"G (yield -> ({state_transition_formula(g, state, state_map_I, event_map_I)}))"
        for state in states
    ]
    trans_O = [
        f"G ({state_transition_formula(g, state, state_map_O, event_map_O)})"
        for state in states
    ]

    # Yield formulas - input system state cannot evolve until output yields
    yield_I = yield_input_formula(state_vars_I)

    # The input and output dynamics
    dyn_I = init_I + yield_I + trans_I
    dyn_O = init_O + trans_O

    # Secrecy formula - all outputs always correpsond to a nonsecret run
    secret_O = f"({' || '.join([state_map_O[i] for i, sec in enumerate(g.vs['secret']) if sec])})"
    secrecy = f"G !{secret_O}"

    # Insertion bound formula - bounds the number of insertions the edit function can perform
    # "1" corresponds to replacement and "None" corresponds to any finite sequence of insertions
    if ins_bound is None:
        finite_insertion = "G F yield"
    else:
        if ins_bound <= 0:
            raise ValueError("Insertion bound must be at least 1 (no deletions).")
        finite_insertion = (
            "G (" + " || X (".join(["yield"] * ins_bound) + ")" * ins_bound
        )

    # Set LTL assumptions and guarantees for Bosy
    bosy["assumptions"] = dyn_I
    bosy["guarantees"] = [secrecy, finite_insertion] + guarantees + dyn_O

    # Setup HyperLTL constraints
    # Formula for different current outputs for two runs
    diff_output = " || ".join([f"!({e}[pi1] <-> {e}[pi2])" for e in event_vars_O])
    # Formula for same current inferences for two runs
    same_inferences = [f"({inf}[pi1] <-> {inf}[pi2])" for inf in inferences]
    # HyperLTL formula representing consistency of secret assertion across two runs with the same outputs
    secret_output_consistency = [
        f"forall pi1 pi2. ({s}) W ({diff_output})" for s in same_inferences
    ]
    # Set HyperLTL constraints for Bosy
    bosy["hyper"] = secret_output_consistency

    # json.dump(bosy, sys.stdout)
    with open(path, "w") as f:
        json.dump(bosy, f, indent=4)

    # If needed, encode the input dynamics (assumptions) as a partial SMV file for simulation and the
    # LTL constraints for verification (Note we cannot encode the HyperLTL constraints)
    if smv_path is not None:
        # Init formulas
        smv_init = f"{state_map_I[init_state]}"
        # Transition formulas
        smv_trans = [
            f"(yield -> ({state_transition_formula(g, state, state_map_I, event_map_I, smv=True)}))"
            for state in states
        ]
        # Yield formulas - input system state cannot evolve until output yields
        smv_yield = yield_input_formula(state_vars_I, smv=True)
        smv_trans_str = " && ".join(smv_trans + smv_yield)
        # LTL constraints
        smv_LTL_spec = (
            "LTLSPEC "
            + "\nLTLSPEC ".join(bosy["assumptions"] + bosy["guarantees"])
            + "\n"
        )

        smv_block = f"INIT {smv_init} \n" f"TRANS {smv_trans_str} \n" + smv_LTL_spec

        # In SMV, conjunctions are represented by &, disjunctions by |
        smv_block = smv_block.replace("&&", "&")
        smv_block = smv_block.replace("||", "|")

        with open(smv_path, "w") as f:
            f.write(smv_block)


def get_bool_vars(g, num_latches=None):
    ret = dict()

    # Encode automaton states with boolean variables
    states = list(range(g.vcount()))
    ret["state_vars_I"], ret["state_map_I"] = list_to_bool_vars(states, "x_I_")
    ret["state_vars_O"], ret["state_map_O"] = list_to_bool_vars(states, "x_O_")

    # Encode events with boolean variables
    events = sorted(list(g.events))
    ret["event_vars_I"], ret["event_map_I"] = list_to_bool_vars(events, "e_I_")
    ret["event_vars_O"], ret["event_map_O"] = list_to_bool_vars(events, "e_O_")

    if num_latches is not None:
        # Encode controller states with boolean variables
        controller_states = list(range(2 ** num_latches))
        ret["controller_state_vars"], ret["controller_state_map"] = list_to_bool_vars(
            controller_states, "__latch_s"
        )

    return ret


def list_to_bool_vars(values, base_name):
    """
    Encode a list of possible values a variable can take on in terms of boolean variables.

    Parameters:
    values: the list of values to encode
    base_name: the base_name of the boolean variables to use

    Returns:
    b_vars: a list of the boolean variables used to encode the values
    var_map: a map from a value to a formula over the boolean variables representing it
    """
    n_values = len(values)
    n_vars = math.ceil(math.log2(n_values))
    b_vars = [f"{base_name}{i}" for i in range(n_vars)]
    var_map = {values[i]: _index_to_formula(i, b_vars) for i in range(n_values)}
    return b_vars, var_map


def _index_to_formula(i, b_vars):
    """
    Encode an index/number as a formula over provided boolean variables.
    This essentially converts the index to a binary number encoded with a boolean formula.

    Parameters:
    i: the index to encode
    b_vars: the list of boolean variables

    Returns: the formula encoding the index
    """
    partial = [
        f"{'' if x == '1' else '!'}{b_vars[j]}"
        for j, x in enumerate(reversed(bin(i)[2:]))
    ]
    partial += [f"!{b_vars[j]}" for j in range(len(partial), len(b_vars))]
    return "(" + " && ".join(partial) + ")"


def state_transition_formula(g, ind, state_map, event_map, smv=False):
    """
    Encode the outgoing transition of the automaton at the provided state with a formula over the given
    boolean variables for states and events.

    Parameters:
    g: the automaton
    ind: the index of the state/vertex in the automaton
    state_map: the map from states of the automaton to corresponding boolean formulas
    event_map: the map from events of the automaton to corresponding boolean formulas
    smv: whether or not to use the smv format instead of LTL

    Returns: a boolean formula encoding all possible outgoing transitions
    """
    if smv:
        next_token = smv_next
    else:
        next_token = ltl_next
    successors = " || ".join(
        [
            f"({state_map[e.target]} && {event_map[e['label']]})"
            for e in g.es.select(_source=ind)
        ]
    )
    trans_form = f"({state_map[ind]} -> {next_token}({successors}))"
    return trans_form


def yield_input_formula(state_vars, smv=False):
    """
    Encode the specification that the input yields to the output as a list of formulas.

    Parameters:
    state_vars: the list of boolean variables encoding the input system state variables
    smv: whether or not to use the smv format instead of LTL

    Returns: a list of formulas
    """
    if smv:
        prefix = ""
        next_token = smv_next
    else:
        prefix = "G "
        next_token = ltl_next
    return [
        prefix
        + f"(!yield -> ({' && '.join([f'({svar} <-> {next_token}({svar}))' for svar in state_vars])}))"
    ]


def tree_example():
    g = DFA()
    g.add_vertices(6)
    g.vs["init"] = False
    g.vs[0]["init"] = True
    g.vs["secret"] = False
    g.vs[2]["secret"] = True
    g.add_edges(
        [(0, 1), (1, 2), (2, 2), (0, 3), (3, 4), (4, 4), (3, 5), (5, 5)],
        ["a", "a", "a", "b", "a", "a", "b", "a"],
    )
    g.generate_out()

    base_path = "tests/bosy/tree"
    write_bosy_insertion_system(
        base_path + ".bosy", g, base_path + "._smv", ins_bound=1
    )


def insert_example():
    g = DFA()
    g.add_vertices(3)
    g.vs["init"] = False
    g.vs[0]["init"] = True
    g.vs["secret"] = False
    g.vs[1]["secret"] = True
    g.add_edges([(0, 1), (1, 0), (0, 2), (2, 0), (2, 2)], ["a", "a", "b", "b", "a"])
    g.generate_out()

    base_path = "tests/bosy/three_rep"
    write_bosy_insertion_system(
        base_path + ".bosy", g, base_path + "._smv", ins_bound=1
    )

    base_path = "tests/bosy/three_ins"
    write_bosy_insertion_system(base_path + ".bosy", g, base_path + "._smv")

    base_path = "tests/bosy/three_ins_2"
    write_bosy_insertion_system(
        base_path + ".bosy", g, base_path + "._smv", ins_bound=2
    )


if __name__ == "__main__":
    tree_example()
    insert_example()
