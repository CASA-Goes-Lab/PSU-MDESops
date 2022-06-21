"""
Interface to the Edisyn library for synthesis of obfuscation for opacity enforcement
"""
from DESops.automata.NFA import NFA
from DESops.opacity.secret_observer import construct_secret_observer_label_transform
from DESops.opacity.secret_specification import OpacityNotion
from os import makedirs

try:
    import edisyn.edisyn_main as ed
except ImportError:
    ed = None


def check_edisyn():
    """
    Check if the EdiSyn library is accessible.

    Returns
    -------
    bool
        True if EdiSyn is available, False otherwise
    """
    return ed is not None


def apply_edisyn(path, plant, utility, insertion_bound=1, allow_deletions=True):
    """Synthesizes an obfuscation automaton to enforce current-state opacity.
    The marked states of the plant are interpreted to be secret.
    If possible, the obfuscator satisfies the utility constraints on the states of the plant.
    This ensures for every secret state S in the current state estimate, there is another
    nonsecret state NS in the estimate so that (S, NS) is in the utility constraints.
    Furthermore, the obfuscator will not insert more events than the given bound.

    Parameters
    ----------
    path : str
        A directory where intermediate Edisyn files can be stored
    plant : DFA
        An automaton reperesenting the system with secret states marked
    utility : list
        A list of admissible pairs of states estimations of the plant
    insertion_bound : int
        The bound on the number of events the obfuscator can insert (Default value = 1)
    allow_deletions : bool
        Whether or not to allow deletions (Default value = True)

    Returns
    -------
    Automaton
        A obfuscator automaton. An event 'a/b/c' denotes that 'a' should be replaced by 'bc'

    """
    if ed is None:
        raise ImportError
    # Create working directory for Edisyn if it does not already exist
    makedirs(path, exist_ok=True)

    # Write the plant to an fsm file used by Edisyn
    plant_path = path + '/plant.fsm'
    # The map from plant events to the fsm events is returned
    event_map = _automata_to_edisyn_fsm(plant, plant_path)

    # Write the utility specification to a spc file used by Edisyn
    utility_path = path + '/utility.spc'
    _utility_to_spc(utility, utility_path)

    # Apply Edisyn to the created files
    obf_path = path + '/obf.fsm'
    success = ed.main(plant_path, utility_path, obf_path, insertion_bound, False, allow_deletions)

    # Old interface
    # subprocess.run('python ' + edisyn_path + ' -b ' + str(insertion_bound) + ' ' + plant_path + ' ' + utility_path + ' ' + obf_path)
    # out = sh.python(edisyn_path, '-b', insertion_bound, plant_path, utility_path, obf_path)

    # Convert the result from Edisyn to an edit automaton
    edit = None
    if success:
        edit = _edisyn_fsm_to_automata(obf_path, event_map)

    return edit


def trivial_utility(g):
    """Construct trivial utility constraints over the states of g

    Parameters
    ----------
    g : Automaton
        An automaton

    Returns
    -------
    list[tuple]
        A list of all pairs of states of g

    """
    utility = [(v.index, u.index) for v in g.vs for u in g.vs]
    return utility


def _automata_to_edisyn_fsm(g, out_fsm_path):
    """Convert an automaton to an fsm file expected by Edisyn

    Parameters
    ----------
    g : DFA
        A DFA representing the system with marked states representing secrets
    out_fsm_path : str
        A path to write the converted fsm to

    Returns
    -------
    dict
        A map from the events of g to the events of the fsm

    """
    fout = open(out_fsm_path, 'w')

    event_map = {x: i for i, x in enumerate(g.events)}

    # An artificial initial state and event is added for Edisyn
    # Entries are tab delimited

    # Write the number of vertices and events
    fout.write(str(g.vcount() + 1) + '\t' + str(g.ecount() + 1) + '\n')

    # The artificial initial state transitions to all original initial events
    init_states = g.vs.select(init=True)
    fout.write('\ninit\t1\t' + str(len(init_states)) + '\n')
    for v in init_states:
        fout.write('init\t{i}'.format(i=v.index) + '\n')

    # Write the rest of the automaton
    for v in g.vs:
        out_edges = g.es.select(_source=v)
        # Marked states are secret
        if v['marked']:
            fout.write('\n{i}'.format(i=v.index) + '\t0\t' + str(len(out_edges)) + '\n')
        else:
            fout.write('\n{i}'.format(i=v.index) + '\t1\t' + str(len(out_edges)) + '\n')
        for e in out_edges:
            fout.write(str(event_map[e['label']]) + '\t{i}'.format(i=e.target) + '\n')
    fout.close()
    return event_map


def _edisyn_fsm_to_automata(in_path, event_map):
    """Convert the edit function from the fsm file from Edisyn to an automaton encoding it
        The events of the converted automaton are tuples (e1, e2, ..., en) representing
        the event e1 getting replaced by the string e2...en

    Parameters
    ----------
    in_path : str
        A path to read the fsm from
    event_map : dict
        A dictionary mapping events of the input automaton for Edisyn to the events of the fsm output

    Returns
    -------
    NFA
        An automaton converted from the fsm file

    """
    obf = None

    with open(in_path, 'r') as fin:

        # Construct the inverse map from fsm events to original events
        inv_event_map = {str(i): e for i, e in enumerate(event_map)}
        inv_event_map[''] = ''
        inv_event_map['init'] = ''

        num_states, num_events = [int(x) for x in fin.readline().strip().split()]
        state_map = {}
        pair_list = []
        label_list = []

        # Function to get index from state and add the state to state_map if necessary
        def get_state_ind(_state):
            """

            Parameters
            ----------
            _state :


            Returns
            -------

            """
            if _state in state_map:
                return state_map[_state]
            else:
                new_ind = len(state_map)
                state_map[_state] = new_ind
                return new_ind

        for s in range(num_states):
            fin.readline()
            # Read a state and outgoing transitions from the file
            state, public, num_trans = [x for x in fin.readline().strip().split()]
            state_ind = get_state_ind(state)
            for t in range(int(num_trans)):
                # Read a transition from the file
                edit_string, next_state = [x for x in fin.readline().strip().split()]
                # Convert the edit string to a tuple of events
                edit_tup = tuple(inv_event_map[i] for i in edit_string.split('/'))
                next_state_ind = get_state_ind(next_state)
                pair_list.append((state_ind, next_state_ind))
                label_list.append(edit_tup)

        # Build the obfuscation automaton
        obf = NFA()
        obf.add_vertices(len(state_map))
        obf.add_edges(pair_list, label_list)

        obf.Euo = {''}

        # Delete artificial initial state introduced for edisyn
        init_state = obf.vs.select(0)
        for e in obf.es.select(_source_in=init_state.indices):
            obf.vs[e.target]['init'] = True
        obf.delete_vertices(init_state)

        obf.generate_out()

    return obf


def _utility_to_spc(utility, out_utility_path):
    """Convert a utility constraint list to a spc file expected by Edisyn

    Parameters
    ----------
    utility : list[tuple]
        A list of pairs of admissible states
    out_utility_path : str
        The path to write the spc file to

    Returns
    -------

    """
    fout = open(out_utility_path, 'w')

    fout.write('init\tinit\n')
    for pair in utility:
        fout.write(str(pair[0]) + '\t' + str(pair[1]) + '\n')

    fout.close()


def enforce_state_based_opacity_edisyn(g, utility, notion=OpacityNotion.CSO, joint=False,
                                       working_dir='./edisyn',
                                       obs_map=None, insertion_bound=1, allow_deletions=True,
                                       **spec_kwargs):
    """Synthesize an obfuscator enforcing the desired notion of opacity using Edisyn.
    This is done by applying Edisyn to the secret observer of the system.
    The provided utility constraints over the states of g are mapped into
    utility constraints over the states of the secret observer.

    Parameters
    ----------
    g : NFA
        An NFA representing the plant
    utility : list[tuple]
        A list of admissible pairs of states of g
    notion : OpacityNotion
        The notion of opacity to use,  (Default value = CSO)
    joint : bool
        If true, then interpret opacity jointly. If false, then interpret opacity separately (Default value = False)
    working_dir : str
        Where to put intermediate Edisyn files (Default value = './edisyn')
    obs_map : ObservationMap
        The observation map for g (Default value = None)
    insertion_bound : int
        The bound on the number of insertions for the obfuscator (Default value = 1)
    allow_deletions : bool
        Whether or not to allow deletions (Default value = True)
    spec_kwargs :
        Additional keyword arguments for specifying the kind of secret behavior
    **spec_kwargs :


    Returns
    -------
    Automaton
        The obfuscator as an automaton

    """
    # Construct the secret observer of the label transform of the provided system g
    a_so = construct_secret_observer_label_transform(g, obs_map, notion, joint=joint, **spec_kwargs)

    a_utility = utility
    # Map the utility for a to the a utility for the secret observer a_so
    so_utility = _state_based_utility(a_so, a_utility)

    # Apply Edisyn to construct an automaton encoding the edit function / obfuscator
    obfuscator = apply_edisyn(working_dir, a_so, so_utility, insertion_bound, allow_deletions=allow_deletions)
    # Convert the obfuscator to an edit automaton
    edit = _edisyn_obf_to_edit(obfuscator)

    return edit


def _state_based_utility(a_so, utility):
    """Construct utility constraints for the secret observer from utility constraints over the original automaton
    A secret observer state v can be explained by u if for every state of the original system qv from v
    there is a state qu from u so that (qv,qu) is admissible in the provided utility constraints for the
    original system.

    Parameters
    ----------
    a_so : Automaton
        The secret observer for the original system
    utility : list[tuple]
        The utility constraints for the original system

    Returns
    -------
    list[tuple]
        utility constraints over the secret observer

    """

    # The artificial initial state added to the secret observer can only be explained by iteself.
    so_utility = [(v.index, u.index) for v in a_so.vs for u in a_so.vs if
                  (all([any([(sv[0], su[0]) in utility for su in u['name']]) for sv in v['name']])# and
                   #all([any([(sv[0], su[0]) in utility for sv in v['name']]) for su in u['name']]) and
                   #v.index > 0 and u.index > 0) or (v.index == 0 and u.index == 0)
                   )]
    return so_utility


'''
# Edit automaton using insertion, deletion, unedited events
def edisyn_obf_to_edit_auto(obf, obs_map):
    """

    Parameters
    ----------
    obf :

    obs_map :


    Returns
    -------

    """

    inv_obs_map = {v: [] for v in obs_map.values()}
    for k, v in obs_map.items():
        inv_obs_map[v].append(k)

    edit = NFA()
    edit.add_vertices(obf.vcount(), obf.vs['name'])
    edit.vs['init'] = obf.vs['init']
    edit.vs['marked'] = obf.vs['marked']

    for e in obf.es:
        e_split = e['label'].split('/')
        if e_split[1] == '':
            del_e = [ee.deleted_event(orig_e) for orig_e in inv_obs_map[e_split[0]]]
            edit.add_edges([(e.source, e.target)]*len(del_e), del_e)
        elif e_split[0] == e_split[1]:
            unedited_e = [ee.unedited_event(orig_e) for orig_e in inv_obs_map[e_split[0]]]
            edit.add_edges([(e.source, e.target)] * len(unedited_e), unedited_e)
        else:
            num_inter = len(e_split) - 1
            edit.add_vertices(num_inter, marked=[obf.vs[e.source]['marked']]*num_inter)

            del_e = [ee.deleted_event(orig_e) for orig_e in inv_obs_map[e_split[0]]]
            edit.add_edges([(e.source, edit.vcount() - num_inter)]*len(del_e), del_e)

            for i in range(num_inter-1):
                edit.add_edge(edit.vcount() - num_inter + i,
                              edit.vcount() - num_inter + i + 1,
                              ee.inserted_event(e_split[i+1]))
            edit.add_edge(edit.vcount()-1, e.target, ee.inserted_event(e_split[num_inter]))
    return edit
'''


def _edisyn_obf_to_edit(obf):
    """Convert an automaton with edit tuple events to a transducer with edit pair events
    For example the event (a, b, c, d) gets mapped to the string of events (a, b)('',c)('',d)

    Parameters
    ----------
    obf : Automaton
        The automaton with edit tuple events

    Returns
    -------
    Automaton
        A transducer style edit automaton

    """

    if not obf:
        return None
    edit = NFA()

    vert_marked = obf.vs['marked']
    pair_list = []
    label_list = []

    for e in obf.es:
        # the tuple of events
        elab = e['label']
        if elab[1] == '':
            pair_list.append((e.source, e.target))
            label_list.append((elab[0], elab[1]))
        elif len(elab) == 2:
            pair_list.append((e.source, e.target))
            label_list.append((elab[0], elab[1]))
        else:
            # For edits inserting more than one event, we add intermediate states
            num_inter = len(elab) - 2
            vert_marked += [obf.vs[e.source]['marked']] * num_inter
            pair_list.append((e.source, len(vert_marked) - num_inter))
            label_list.append((elab[0], elab[1]))

            pair_list += [(len(vert_marked) - num_inter + i, len(vert_marked) - num_inter + i + 1)
                          for i in range(num_inter-1)]
            pair_list.append((len(vert_marked) - 1, e.target))
            label_list += [('', elab[i]) for i in range(num_inter)]

    edit.add_vertices(len(vert_marked),
                      init=obf.vs['init'] + [False]*(len(vert_marked) - obf.vcount()),
                      marked=vert_marked)

    edit.add_edges(pair_list, label_list)
    edit.generate_out()

    return edit
