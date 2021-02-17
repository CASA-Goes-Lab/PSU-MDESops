"""
Interface to the Edisyn library for synthesis of obfuscation for opacity enforcement
"""
from DESops.automata.NFA import NFA
from DESops.opacity.secret_specification import transform_secret_state_based, current_state_spec, initial_state_spec, k_step_spec, joint_infinite_step_spec
from DESops.opacity.secret_observer import construct_secret_observer
from DESops.basic_operations.unary import find_inacc

import edisyn.edisyn_main as ed

from os import makedirs


def apply_edisyn(path, plant, utility, insertion_bound=1):
    """
    Synthesizes an obfuscation automaton to enforce current-state opacity.
    The marked states of the plant are interpreted to be secret.
    If possible, the obfuscator satisfies the utility constraints on the states of the plant.
    This ensures for every secret state S in the current state estimate, there is another
    nonsecret state NS in the estimate so that (S, NS) is in the utility constraints.
    Furthermore, the obfuscator will not insert more events than the given bound.

    Parameters:
    path: A directory where intermediate Edisyn files can be stored
    plant: A DFA reperesenting the system with secret states marked
    utility: A list of admissible pairs of states estimations of the plant
    insertion_bound: The bound on the number of events the obfuscator can insert

    Returns: A obfuscator automaton. An event 'a/b/c' denotes that 'a' should be replaced by 'bc'
    """
    makedirs(path, exist_ok=True)
    plant_path = path + '/plant.fsm'
    _automata_to_edisyn_fsm(plant, plant_path)
    utility_path = path + '/utility.spc'
    _utility_to_spc(utility, utility_path)

    obf_path = path + '/obf.fsm'

    success = ed.main(plant_path, utility_path, obf_path, insertion_bound, False)
    # subprocess.run('python ' + edisyn_path + ' -b ' + str(insertion_bound) + ' ' + plant_path + ' ' + utility_path + ' ' + obf_path)
    # out = sh.python(edisyn_path, '-b', insertion_bound, plant_path, utility_path, obf_path)

    obfuscator = None
    if success:
        obfuscator = _edisyn_fsm_to_automata(obf_path)

    return obfuscator


def trivial_utility(g):
    '''
    Construct trivial utility constraints over the states of g allowing all pairs of states excluding the first.

    Parameters:
    g: A DFA

    Returns: A list of pairs of states of g
    '''
    # The first state is excluded for the secret observer
    utility = [(v.index, u.index) for v in g.vs for u in g.vs if
               (v.index != 0 and u.index != 0) or (v.index == 0 and u.index == 0)]
    return utility


def _automata_to_edisyn_fsm(g, out_fsm_path):
    '''
    Convert an automaton to an fsm file expected by Edisyn

    Parameters:
    g: A DFA representing the system with marked states representing secrets
    out_fsm_path: A path to write the converted fsm to
    '''
    fout = open(out_fsm_path, 'w')

    event_map = {x: i for i, x in enumerate(g.events)}

    # An artificial initial state and event is added for Edisyn
    fout.write(str(g.vcount() + 1) + '\t' + str(g.ecount() + 1) + '\n')

    init_states = g.vs.select(init=True)
    fout.write('\ninit\t1\t' + str(len(init_states)) + '\n')
    for v in init_states:
        fout.write('init\t{i}'.format(i=v.index) + '\n')

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

def _edisyn_fsm_to_automata(in_path):
    '''
        Convert an fsm file from Edisyn to an automaton

        Parameters:
        in_path: A path to read the fsm from

        Returns: An automaton converted from the fms file
    '''
    g = NFA()

    with open(in_path, 'r') as fin:
        num_states, num_events = [int(x) for x in fin.readline().strip().split()]

        for s in range(num_states):
            fin.readline()
            state, public, num_trans = [x for x in fin.readline().strip().split()]
            state_ind = g.vs.select(name=state)
            v = None
            if state_ind:
                v = state_ind[0]
            else:
                v = g.add_vertex(state)
            for t in range(int(num_trans)):
                ev, nstate = [x for x in fin.readline().strip().split()]

                u = None
                state_ind = g.vs.select(name=nstate)
                if state_ind:
                    u = state_ind[0]
                else:
                    u = g.add_vertex(nstate)

                g.add_edge(v.index, u.index, ev)
    g.Euo = {''}
    g.vs[0]['init'] = True
    g.generate_out()
    return g


def _utility_to_spc(utility, out_utility_path):
    '''
    Convert a utility constraint list to a spc file expected by Edisyn

    Parameters:
    utility: A list of pairs of admissible states
    out_utility_path: The path to write the spc file to
    '''
    fout = open(out_utility_path, 'w')

    fout.write('init\tinit\n')
    for pair in utility:
        fout.write(str(pair[0]) + '\t' + str(pair[1]) + '\n')

    fout.close()


def enforce_state_based_opacity_edisyn(g, utility, notion, joint=False,
                                       secret_type=1, k=0, working_dir='./edisyn',
                                       obs_map=None, insertion_bound=1):
    '''
    Synthesize an obfuscator enforcing the desired notion of opacity using Edisyn.
    This is done by applying Edisyn to the secret observer of the system.
    The provided utility constraints over the states of g are mapped into
    utility constraints over the states of the secret observer.

    Parameters:
    g: An NFA representing the plant
    utility: A list of admissible pairs of states of g
    notion: The notion of opacity to use, i.e., 'CSO','ISO','KSTEP','INFSTEP'
    joint: If true, then interpret opacity jointly. If false, then interpret opacity separately
    secret_type: The type of secrets for K-step and infinite step opacity
    k: The value of K for K-step opacity
    working_dir: Where to put intermediate Edisyn files
    obs_map: The observation map for g
    insertion_bound: The bound on the number of insertions for the obfuscator
    '''
    a, Ens, Eo, obs_map_a = transform_secret_state_based(g, obs_map)
    a_utility = [(v+1, u+1) for (v, u) in utility]
    a_utility.append((0, 0))
    E = a.events

    h_ns = None
    ns_state_sets = None
    if notion == 'CSO':
        h_ns, ns_state_sets = current_state_spec(Ens, E)
    elif notion == 'ISO':
        h_ns, ns_state_sets = initial_state_spec(Ens, E)
    elif notion == 'KSTEP':
        h_ns, ns_state_sets = k_step_spec(secret_type, k, Ens, Eo, E)
        if not joint:
            print('Using Edisyn to enforce separate k-step opacity is conservative.')
    elif notion == 'INFSTEP':
        if not joint:
            raise ValueError("Separate infinite-step opacity is not implemented")
        h_ns, ns_state_sets = joint_infinite_step_spec(secret_type, Ens, Eo, E)
    else:
        raise ValueError("Unrecognized notion of opacity")

    a_so = construct_secret_observer(a, h_ns, ns_state_sets, joint, obs_map_a)

    so_utility = _state_based_utility(a_so, a_utility)

    obfuscator = apply_edisyn(working_dir, a_so, so_utility, insertion_bound)

    orig_obf = None
    if obfuscator:
        orig_obf = _map_state_based_obf(obfuscator, a_so)

    return orig_obf


def _state_based_utility(a_so, utility):
    '''
    Construct utility constraints for the secret observer from utility constraints over the original automaton
    A secret observer state v can be explained by u if for every state of the original system qv from v
    there is a state qu from u so that (qv,qu) is admissible in the provided utility constraints for the
    original system.

    Parameters:
    a_so: The secret observer for the original system
    utility: The utility constraints for the original system

    Returns: utility constraints over the secret observer
    '''
    # The artificial initial state added to the secret observer can only be explained by iteself.
    so_utility = [(v.index, u.index) for v in a_so.vs for u in a_so.vs if
                  (all([any([(sv[0], su[0]) in utility for su in u['name']]) for sv in v['name']]) and
                   #all([any([(sv[0], su[0]) in utility for sv in v['name']]) for su in u['name']]) and
                   v.index > 0 and u.index > 0) or (v.index == 0 and u.index == 0)]
    return so_utility


def _map_state_based_obf(obf, a_so):
    '''
    Map the obfuscator over the secret observer into one over the original system

    Parameters:
    obf: The obfsucator automaton over the secret observer
    a_so: The secret observer of the original system

    Returns: An obfuscator automaton over the original system
    '''

    orig_obf = obf.copy()

    ed_init_state = [v.index for v in orig_obf.vs.select(init=True)]
    so_init_state = [e.target for e in orig_obf.es.select(_source_in=ed_init_state)]
    orig_init = [e.target for e in orig_obf.es.select(_source_in=so_init_state)]

    orig_obf.vs['init'] = False
    orig_obf.vs[orig_init]['init'] = True
    orig_obf.vs['marked'] = True
    orig_obf.generate_out()

    bad_states = find_inacc(orig_obf)
    orig_obf.delete_vertices(list(bad_states))

    orig_obf.events = set(orig_obf.es['label'])#set(a_so.events) - {'e_init'}
    orig_obf.generate_out()

    so_events = list(a_so.events)
    event_map = {}
    for e in orig_obf.events:
        event_map[e] = '/'.join([so_events[int(ee)] if ee != '' else '' for ee in e.split('/')])

    orig_obf.es['label'] = [event_map[e['label']] for e in orig_obf.es]
    orig_obf.events = event_map.values()

    orig_obf.generate_out()
    return orig_obf
