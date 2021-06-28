"""
Functions for generating example contact tracing models that can be used with opacity verifcation and enforcement functions
"""
import itertools
from math import ceil, log2
from pathlib import Path

from pydash.arrays import flatten_deep

import DESops as d
from DESops.basic_operations.composition import observer, product_linear
from DESops.opacity.bisimulation import construct_bisimulation
from DESops.opacity.bosy.edit_to_bosy import list_to_bool_vars


def contact_example(map_file="map1.fsm", num_agents=2, debug=True):
    """
    Construct and return an automaton representing a contact tracing example.
    The model is determinized, and then reduced in size by constructing a bisimulation.
    The events of the system include the malicious observer's location, the other
    individual's regions, and the contact pairs. The event "_2RS_02", for example,
    would mean that user 0 (the observer) is in location 2, user 1 is in region R,
    user 2 is in region S, and users 0 and 2 are in the same location.

    The first two sections of code should be easily editable to implement additional maps

    Parameters:
    map_file: the path to an fsm file that defines the map
              physical paths between locations should be defined in both directions as a transition labeled "t"
              self-loops are implicitly assumed, and should not be present in the fsm file
    num_agents: the number of users that will be modeled in the system
    debug: if True, print information about the size of the system and whether CSO is already satisfied

    Returns:
    b: the automaton of the model, after it has been determinzed and reduced to a bisimilar partition
    event_var_maps: a dict containing the the var lists and maps for the event encodings
                    (see "contact_event_maps" function in this file for details)
    """

    # Regions and secret locations of additional maps can be defined in this section
    # Recommended to test map1 with num_agents = 2, and to test the other maps with num_agents = 3
    # Maps are listed in order of increasing complexity
    if map_file == "map1.fsm":
        R = ["1"]
        S = ["2", "3", "4"]
        secret_locs = ["2"]

    elif map_file == "map2.fsm":
        R = ["1", "2"]
        S = ["3", "4"]
        secret_locs = ["3"]

    elif map_file == "map3.fsm":
        map_file = "map1.fsm"  # same map as map1, but with different secret location
        R = ["1"]
        S = ["2", "3", "4"]
        secret_locs = ["3"]

    elif map_file == "map4.fsm":
        R = ["1"]
        S = ["2", "3", "4", "5"]
        secret_locs = ["5"]

    else:
        raise ValueError("Unknown map")

    # Additional regions can be defined by adding to this part
    # Note, however, that the contact_event_maps function is hardcoded to expect the two regions R and S
    regions = dict()
    for loc in R:
        regions[loc] = "R"
    for loc in S:
        regions[loc] = "S"

    #######################################
    ### NO NEED TO EDIT BELOW THIS LINE ###
    #######################################

    # get path to this file
    parent_path = Path(__file__).parent.absolute()
    map_automaton = d.read_fsm(f"{parent_path}/{map_file}")
    g = generate_model(map_automaton, regions, secret_locs, num_agents)

    # determinize the system
    o = observer(g)
    # observer state is secret if a specific agent is known to be in the secret state
    o.vs["secret"] = False
    for i in range(1, num_agents):
        o.vs["secret"] = [
            all(v["secret"] or state[i] in secret_locs for state in v["name"])
            for v in o.vs
        ]

    # reduce model size by constructing an equivalent bisimulation
    b = construct_bisimulation(o)

    # generate var lists and maps for event encodings
    event_var_maps = contact_event_maps(g, regions, secret_locs)

    if not debug:
        # we can return now if not printing debug information
        return b, event_var_maps

    # check opacity on the bisimulation
    opaque, path = d.opacity.verify_current_state_opacity(b, return_violating_path=True)
    # print debug information
    print(f"System has {g.vcount()} states and {g.ecount()} transitions")
    print(f"Observer has {o.vcount()} states and {o.ecount()} transitions")
    print(f"Bisimulation has {b.vcount()} states and {b.ecount()} transitions")
    print()
    print(f"System is {'' if opaque else 'not '}opaque; Violating path is {path}")
    print()

    return b, event_var_maps


def generate_model(map_automaton, regions, secret_locs, num_agents, ids=None):
    """
    Generate the nondeterminisitc system representing the contact tracing model
    """
    if ids is None:
        ids = list(range(num_agents))

    gs = list()
    for i in range(num_agents):
        g = map_automaton.copy()
        g.vs["init"] = True

        # observer can't visit secret states
        if i == 0:
            secret_ids = [v.index for v in g.vs if v["name"] in secret_locs]
            g.delete_vertices(secret_ids)

        # add self-loops
        for j in g.vs.indices:
            g.add_edge(j, j, d.Event("t"))

        g.events = set(g.es["label"])
        g.generate_out()
        gs.append(g)

    # product generates full system model
    g = d.NFA(product_linear(*gs))
    # fix state names
    g.vs["name"] = [flatten_deep(v["name"]) for v in g.vs]
    # state is secret if second individual is in secret state
    g.vs["secret"] = [(v["name"][1] in secret_locs) for v in g.vs]

    # add state observations
    for t in g.es:
        dest = t.target_vertex["name"]

        # observer location + other users' regions
        loc_info = "".join(
            [(str(dest[i]) if i == 0 else regions[dest[i]]) for i in range(num_agents)]
        )

        # pairs of contact between users
        contact_info = [
            "".join(sorted((str(ids[i]), str(ids[j]))))
            for i in range(num_agents)
            for j in range(num_agents)
            if i < j and dest[i] == dest[j]
        ]

        t["label"] = "_" + "_".join([loc_info] + sorted(contact_info))

    # simplify state names
    g.vs["name"] = ["".join(v["name"]) for v in g.vs]

    g.events = set(g.es["label"])
    g.generate_out()

    return g


def contact_event_maps(g, regions, secret_locs):
    """
    Returns:
    a dict object containing the following:
        event_vars_I: a list of boolean input event variables
        event_vars_O: a list of boolean output event variables that includes input terms that are carried through to the output
        obs_event_vars_I: a list of of boolean input event variables that only contains the bits that can be observed by the obfuscator
                          (the malicious observer's region is included, but their precise location is not)
        obs_event_vars_O: a list of of boolean output event variables that only contains the bits that can be observed by the inferrer
                          (the malicious observer's region is included, but their precise location is not)
        cntr_event_vars_O: a list of of boolean output event variables that only contains those bits that can be modified by the inferrer
                           (neither the maicious observer's region nor precise location is included)
    each entry also has a corresponding map (e.g. event_map_I) that is a dict mapping events to the corresponding boolean formula over the boolean variables
    """
    ret = dict()

    # Event info is decomposed into its components
    # compute possible values of observer location in each region
    obs_locs = dict()
    for loc, reg in regions.items():
        if loc in secret_locs:
            continue
        if reg not in obs_locs:
            obs_locs[reg] = list()
        obs_locs[reg].append(loc)
    # sort obs_locs lists to maintain consistency
    for reg in obs_locs:
        obs_locs[reg] = sorted(obs_locs[reg])
    # bits needed for observer location is based on max number of locations in any individual region
    loc_set_sizes = [len(locs) for reg, locs in obs_locs.items()]
    num_loc_bits = ceil(log2(max(loc_set_sizes)))

    # split events according to the observer's location
    events = sorted(list(g.events))
    split_events = [list(v) for _, v in itertools.groupby(events, key=lambda x: x[:2])]
    # the number of elements needed in each group is the first power of 2 >= the largest group
    max_elts = max([len(l) for l in split_events])
    target_length = 1
    while target_length < max_elts:
        target_length *= 2
    for l in split_events:
        while len(l) < target_length:
            l.append("")

    # non controllable events
    obs_region = [f"e_I_r0"]
    loc_vars = [f"e_I_l{i}" for i in range(num_loc_bits)]

    event_map_I = dict()
    event_map_O = dict()
    obs_event_map_I = dict()
    obs_event_map_O = dict()
    cntr_event_map_O = dict()
    for lst in split_events:
        tmp_vars_I, tmp_map_I = list_to_bool_vars(lst, "e_I_")
        tmp_vars_O, tmp_map_O = list_to_bool_vars(lst, "e_O_")

        # remove empty string event padding from dicts
        del tmp_map_I[""]
        del tmp_map_O[""]

        # get observer's location for this sublist
        obs_loc = list(tmp_map_I.keys())[0][1]
        # compute region / location of observer
        reg = f"e_I_r0" if regions[obs_loc] == "R" else f"!e_I_r0"
        # compute observer's location within their region
        loc_id = obs_locs[regions[obs_loc]].index(obs_loc)
        terms = [
            f"{'' if x == '1' else '!'}{loc_vars[i]}"
            for i, x in enumerate(reversed(bin(loc_id)[2:]))
        ]
        terms += [f"!{loc_vars[i]}" for i in range(len(terms), len(loc_vars))]

        for e, expr in tmp_map_I.items():
            event_map_I[e] = f"({reg} && {' && '.join(terms)} && {expr})"
            obs_event_map_I[e] = f"({reg} && {expr})"

        for e, expr in tmp_map_O.items():
            cntr_event_map_O[e] = f"({expr})"
            obs_event_map_O[e] = f"({reg} && {expr})"
            event_map_O[e] = f"({reg} && {' && '.join(terms)} && {expr})"

    # generate event
    event_vars_I = tmp_vars_I + obs_region + loc_vars
    event_vars_O = tmp_vars_O + obs_region + loc_vars
    obs_event_vars_I = tmp_vars_I + obs_region
    obs_event_vars_O = tmp_vars_O + obs_region
    cntr_event_vars_O = tmp_vars_O

    # put modified event vars and maps into return dict
    ret["event_vars_I"] = event_vars_I
    ret["event_map_I"] = event_map_I
    ret["event_vars_O"] = event_vars_O
    ret["event_map_O"] = event_map_O
    # observable components
    ret["obs_event_vars_I"] = obs_event_vars_I
    ret["obs_event_map_I"] = obs_event_map_I
    ret["obs_event_vars_O"] = obs_event_vars_O
    ret["obs_event_map_O"] = obs_event_map_O
    # controllable components
    ret["cntr_event_vars_O"] = cntr_event_vars_O
    ret["cntr_event_map_O"] = cntr_event_map_O

    return ret
