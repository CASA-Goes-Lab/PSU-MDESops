import ast

import igraph as ig

from DESops import error
from DESops.core.dfa import DFA
from DESops.core.event import Event
from DESops.core.nfa import NFA
from DESops.core.pfa import PFA


# pylint: disable=C0103
"""
Convert an 'fsm' filetype, which is used/defined by the DESUMA software,
into an igraph Graph object.
"""


# TODO - fix docstring format
# TODO - change `type_aut` to be a class instead of string
def read_fsm(fsm_filename, g=None, type_aut="", backend="igraph"):
    """
    fsm_filename: filename to read from, e.g. "name_text.fsm"
    g: an already-constructed, empty Automata instance to read into (e.g.
        `d.DFA()`), or an igraph Graph object -- or None to construct a
        fresh Automata of whatever type the file content indicates (or
        `type_aut` forces).
    backend : str
        Which implementation to use: "igraph" (default) parses the file
        directly into an igraph.Graph, then wraps that as the resulting
        Automata's initial state. "native" (pure Python, no igraph
        dependency) parses straight into the resulting Automata via its
        own add_vertices()/add_edges(), so a freshly-read automaton never
        forces an igraph build unless something later reads its .vs/.es --
        see DESops.core.automata and doc/logs/v2-igraph-decoupling.md.
        Both produce equivalent results.
    """
    if backend == "igraph":
        return _read_fsm_igraph(fsm_filename, g, type_aut)
    elif backend == "native":
        return _read_fsm_native(fsm_filename, g, type_aut)
    else:
        raise ValueError(f"Unknown backend: {backend!r}")


def _read_fsm_igraph(fsm_filename, g=None, type_aut=""):
    """
    fsm_filename: filename to write output to, e.g. "name_text.fsm"
    g: igraph Graph object to read from (an Automata instance would work as well).

    Keyword attributes used in this package (for igraph Graph edge/vert sequences):
    "name": vertexseq label to refer to state names
    "marked": vertexseq label to refer to marked attr
    "label": edgeseq label to refer to label of transition
    "obs": edgeseq label to refer to transition observability attr
    "contr": edgeseq label to refer to transition controllability attr

    "prob": for PFA, this additional attribute describes the probability of a transition
        occuring for a given state pair & event label. This is NOT included in the 'fsm'
        file format from DESUMA, but if the probability is included as a tab-separated
        value at the end of the line for a transition, it will be read as the probability
        for that transition.

        For example: in state 1, there is a controllable-unobservable transition
        to state 2 with label 'a' and probability p=0.5
        > <'fsm_file.fsm'>
        > 1   0   1
        > 0   2   c   uo   0.5
        > ...
    """
    g_defined = True
    if not g:
        g = ig.Graph(directed=True)
        g_defined = False

    state_markings = list()
    state_names = list()
    state_crit = list()
    events = set()
    events_unobs = set()
    events_unctr = set()
    trans_list = list()
    trans_labels = list()
    trans_observable = list()
    trans_controllable = list()
    trans_prob = list()
    neighbors_list = list()

    is_NFA = False

    with open(fsm_filename, "r") as f:
        # First line in fsm is # of states
        g.add_vertices(int(f.readline()))
        # next(f)
        i = 2
        for line in f:
            if not line or line == "\n":
                i += 1
                continue
            # Should be delimited in the line by tabs
            states_tuple = line.split("\t")
            if len(states_tuple) < 3:
                raise error.FileFormatError(
                    "ERROR %s:\nMissing argument in line %d\nStates are in the format:\nSOURCE_STATE\tMARKED\t#TRANSITIONS"
                    % (fsm_filename, i)
                )
            last_el = states_tuple.pop()
            states_tuple.append(last_el[0:-1])  # REMOVING \n
            # print(states_tuple)
            name = states_tuple[0]
            states_tuple[0] = ast.literal_eval(name) if name[0] == "(" else name
            state_names.append(states_tuple[0])
            # states.append(State(states_tuple[0]))
            state_markings.append(states_tuple[1] == "1")
            if len(states_tuple) > 3:
                state_crit.append(states_tuple[2])
            i += 1
            total = 0
            neigh = list()

            # set for each vertex to see if any nondeterminism, i.e. repeated labels
            # if any found, set type to NFA, and future vertices won't do this check
            unique_labels = set()
            try:
                x = int(states_tuple[2])
            except ValueError:
                raise error.FileFormatError(
                    "ERROR {0}:\nExpected integer number of neighbors on line {1}.\nDid previous state have more transitions than noted?".format(
                        fsm_filename, i
                    )
                )

            for _ in range(0, int(states_tuple[2])):
                trans_tuple = f.readline().split("\t")
                if trans_tuple == ["\n"]:
                    raise error.FileFormatError(
                        "ERROR %s:\nToo many transitions at state %s"
                        % (fsm_filename, states_tuple[0])
                    )
                if len(trans_tuple) > 5:
                    raise error.FileFormatError(
                        "ERROR %s in line %d:\nToo many argument\nTransitions are in the format:\nEVENT\tTARGET_STATE\tc/uc\to/uo\tprob(optional)"
                        % (fsm_filename, i)
                    )
                elif len(trans_tuple) < 4:
                    raise error.FileFormatError(
                        "ERROR %s in line %d:\nMissing arguments\nTransitions are in the format:\nEVENT\tTARGET_STATE\tc/uc\to/uo\tprob(optional)"
                        % (fsm_filename, i)
                    )

                if not g_defined and not type_aut:
                    if len(trans_tuple) == 5:
                        type_aut = "PFA"
                    elif len(trans_tuple) == 4:
                        # TODO WHEN NFA IS DEFINED THEN SET AS DFA UNTIL A NONDETERMINISTIC TRANS IS FOUND
                        type_aut = "DFA"
                if type_aut == "PFA" and len(trans_tuple) != 5:
                    raise error.FileFormatError(
                        "ERROR %s in line %d:\nPFA transitions are in the format:\nEVENT\tTARGET_STATE\tc/uc\to/uo\tprob "
                        % (fsm_filename, i)
                    )
                elif (type_aut == "DFA" or type_aut == "NFA") and len(trans_tuple) != 4:
                    raise error.FileFormatError(
                        "ERROR %s in line %d:\nDFA transitions are in the format:\nEVENT\tTARGET_STATE\tc/uc\to/uo"
                        % (fsm_filename, i)
                    )

                last_el = trans_tuple.pop()
                trans_tuple.append(last_el[0:-1])
                trans_labels.append(Event(trans_tuple[0]))
                events.add(Event(trans_tuple[0]))
                t_name = trans_tuple[1]
                trans_tuple[1] = (
                    ast.literal_eval(t_name) if t_name[0] == "(" else t_name
                )
                trans_list.append((states_tuple[0], trans_tuple[1]))
                if trans_tuple[2] == "uc":
                    events_unctr.add(Event(trans_tuple[0]))
                trans_controllable.append(trans_tuple[2])
                if trans_tuple[3] == "uo":
                    events_unobs.add(Event(trans_tuple[0]))
                trans_observable.append(trans_tuple[3])

                if type_aut == "PFA":
                    # probabilistic info encoded
                    # must be a PFA
                    type_aut = "PFA"
                    try:
                        # float(trans_tuple[4])
                        if float(trans_tuple[4]) > 1 or float(trans_tuple[4]) < 0:
                            raise ValueError
                    except ValueError:
                        raise error.FileFormatError(
                            "ERROR %s in line %d:\nProbability value must be a number smaller than or equal to 1"
                            % (fsm_filename, i)
                        )
                    trans_prob.append(trans_tuple[4])
                    total = total + float(trans_tuple[4])

                    # PFA out attr is of form (target, event, prob)
                    neigh.append(
                        (trans_tuple[1], Event(trans_tuple[0]), float(trans_tuple[4]))
                    )
                else:
                    neigh.append((trans_tuple[1], Event(trans_tuple[0])))
                    if type_aut == "DFA" and trans_tuple[0] in unique_labels:
                        type_aut = "NFA"
                    elif type_aut != "NFA":
                        unique_labels.add(trans_tuple[0])
                i += 1
            neighbors_list.append(neigh)
            if total > 0 and total != 1:
                raise error.FileFormatError(
                    "ERROR %s:\nTransitions in state %s do not sum up to 1"
                    % (fsm_filename, states_tuple[0])
                )

    # Construct graph

    # alternative to: [bool(x) for x in state_markings]
    g.vs["marked"] = state_markings
    if state_crit:
        g.vs["crit"] = state_crit
    g.vs["name"] = state_names
    trans_list_int_names = list()
    for pair in trans_list:
        source = state_names.index(pair[0])
        target = state_names.index(pair[1])
        trans_list_int_names.append((source, target))

    if g_defined:
        g.Euc.update(events_unctr)
        g.Euo.update(events_unobs)
        g.events = events.copy()

    if type_aut == "DFA" or isinstance(g, DFA):
        if not g_defined:
            g = DFA(g, events_unctr, events_unobs, events, False)
        g.add_edges(trans_list_int_names, trans_labels, fill_out=False)

    elif type_aut == "PFA" or isinstance(g, PFA):
        if not g_defined:
            g = PFA(g, events_unctr, events_unobs, events)
        g.add_edges(trans_list_int_names, trans_labels, trans_prob, fill_out=False)

    elif type_aut == "NFA" or isinstance(g, NFA):
        if not g_defined:
            g = NFA(g, events_unctr, events_unobs, events)
        g.add_edges(trans_list_int_names, trans_labels, fill_out=False)

    # print(events)
    trans_observable_bool = [x == "o" for x in trans_observable]
    g.es["obs"] = trans_observable_bool
    trans_controllable_bool = [x == "c" for x in trans_controllable]
    g.es["contr"] = trans_controllable_bool

    if type_aut == "PFA":
        neighbors_list = [
            [g.Out(state_names.index(adj[0]), adj[1], adj[2]) for adj in l]
            for l in neighbors_list
        ]
    else:
        neighbors_list = [
            [g.Out(state_names.index(adj[0]), adj[1]) for adj in l]
            for l in neighbors_list
        ]

    g.vs["out"] = neighbors_list

    return g


def _read_fsm_native(fsm_filename, g=None, type_aut=""):
    """
    Pure-Python (no igraph) equivalent of _read_fsm_igraph. Same parsing
    logic and file-format validation, kept as an independent copy rather
    than factored out to share code with the igraph version -- see
    doc/logs/v2-igraph-decoupling.md and the "backend-suffixed functions"
    convention it documents.

    Builds the resulting Automata via its own add_vertices()/add_edges()
    (names/marked/crit and obs/contr passed as attribute kwargs, not set
    via direct .vs[...]/.es[...] assignment the way _read_fsm_igraph does),
    so a freshly-read automaton never forces an igraph build -- unlike
    _read_fsm_igraph, which always builds one (it parses into a scratch
    ig.Graph() first, then sets several attributes directly via .vs/.es).
    No manual "out" adjacency construction either: that's derived on
    demand from AutomatonData by Automata._out_view, not maintained here.
    """
    g_defined = g is not None

    state_markings = list()
    state_names = list()
    state_crit = list()
    events = set()
    events_unobs = set()
    events_unctr = set()
    trans_list = list()
    trans_labels = list()
    trans_observable = list()
    trans_controllable = list()
    trans_prob = list()

    with open(fsm_filename, "r") as f:
        num_states = int(f.readline())
        i = 2
        for line in f:
            if not line or line == "\n":
                i += 1
                continue
            states_tuple = line.split("\t")
            if len(states_tuple) < 3:
                raise error.FileFormatError(
                    "ERROR %s:\nMissing argument in line %d\nStates are in the format:\nSOURCE_STATE\tMARKED\t#TRANSITIONS"
                    % (fsm_filename, i)
                )
            last_el = states_tuple.pop()
            states_tuple.append(last_el[0:-1])  # REMOVING \n
            name = states_tuple[0]
            states_tuple[0] = ast.literal_eval(name) if name[0] == "(" else name
            state_names.append(states_tuple[0])
            state_markings.append(states_tuple[1] == "1")
            if len(states_tuple) > 3:
                state_crit.append(states_tuple[2])
            i += 1

            unique_labels = set()
            try:
                int(states_tuple[2])
            except ValueError:
                raise error.FileFormatError(
                    "ERROR {0}:\nExpected integer number of neighbors on line {1}.\nDid previous state have more transitions than noted?".format(
                        fsm_filename, i
                    )
                )

            for _ in range(0, int(states_tuple[2])):
                trans_tuple = f.readline().split("\t")
                if trans_tuple == ["\n"]:
                    raise error.FileFormatError(
                        "ERROR %s:\nToo many transitions at state %s"
                        % (fsm_filename, states_tuple[0])
                    )
                if len(trans_tuple) > 5:
                    raise error.FileFormatError(
                        "ERROR %s in line %d:\nToo many argument\nTransitions are in the format:\nEVENT\tTARGET_STATE\tc/uc\to/uo\tprob(optional)"
                        % (fsm_filename, i)
                    )
                elif len(trans_tuple) < 4:
                    raise error.FileFormatError(
                        "ERROR %s in line %d:\nMissing arguments\nTransitions are in the format:\nEVENT\tTARGET_STATE\tc/uc\to/uo\tprob(optional)"
                        % (fsm_filename, i)
                    )

                if not g_defined and not type_aut:
                    if len(trans_tuple) == 5:
                        type_aut = "PFA"
                    elif len(trans_tuple) == 4:
                        type_aut = "DFA"
                if type_aut == "PFA" and len(trans_tuple) != 5:
                    raise error.FileFormatError(
                        "ERROR %s in line %d:\nPFA transitions are in the format:\nEVENT\tTARGET_STATE\tc/uc\to/uo\tprob "
                        % (fsm_filename, i)
                    )
                elif (type_aut == "DFA" or type_aut == "NFA") and len(trans_tuple) != 4:
                    raise error.FileFormatError(
                        "ERROR %s in line %d:\nDFA transitions are in the format:\nEVENT\tTARGET_STATE\tc/uc\to/uo"
                        % (fsm_filename, i)
                    )

                last_el = trans_tuple.pop()
                trans_tuple.append(last_el[0:-1])
                trans_labels.append(Event(trans_tuple[0]))
                events.add(Event(trans_tuple[0]))
                t_name = trans_tuple[1]
                trans_tuple[1] = (
                    ast.literal_eval(t_name) if t_name[0] == "(" else t_name
                )
                trans_list.append((states_tuple[0], trans_tuple[1]))
                if trans_tuple[2] == "uc":
                    events_unctr.add(Event(trans_tuple[0]))
                trans_controllable.append(trans_tuple[2])
                if trans_tuple[3] == "uo":
                    events_unobs.add(Event(trans_tuple[0]))
                trans_observable.append(trans_tuple[3])

                if type_aut == "PFA":
                    try:
                        if float(trans_tuple[4]) > 1 or float(trans_tuple[4]) < 0:
                            raise ValueError
                    except ValueError:
                        raise error.FileFormatError(
                            "ERROR %s in line %d:\nProbability value must be a number smaller than or equal to 1"
                            % (fsm_filename, i)
                        )
                    trans_prob.append(trans_tuple[4])
                else:
                    if type_aut == "DFA" and trans_tuple[0] in unique_labels:
                        type_aut = "NFA"
                    elif type_aut != "NFA":
                        unique_labels.add(trans_tuple[0])
                i += 1

    # Construct the Automata: resolve state name -> index, then build via
    # add_vertices()/add_edges() only -- no direct .vs[...]/.es[...] access,
    # so this never forces an igraph build.
    #
    # Uses state_names.index(...) (matching _read_fsm_igraph's own
    # `state_names.index(pair[0])`) rather than a {name: index} dict: a
    # parsed state name can be an unhashable literal (e.g. a list, via
    # ast.literal_eval on a "(...)"-formatted name), which .index()
    # tolerates the same way _read_fsm_igraph already does.
    trans_list_int = [
        (state_names.index(source), state_names.index(target))
        for source, target in trans_list
    ]

    if g_defined:
        g.Euc.update(events_unctr)
        g.Euo.update(events_unobs)
        g.events = events.copy()

    vertex_kwargs = {}
    if state_crit and len(state_crit) == num_states:
        vertex_kwargs["crit"] = state_crit

    trans_observable_bool = [x == "o" for x in trans_observable]
    trans_controllable_bool = [x == "c" for x in trans_controllable]
    edge_kwargs = {"obs": trans_observable_bool, "contr": trans_controllable_bool}

    if type_aut == "PFA" or isinstance(g, PFA):
        if not g_defined:
            g = PFA(Euc=events_unctr, Euo=events_unobs, E=events)
        g.add_vertices(num_states, names=state_names, marked=state_markings, **vertex_kwargs)
        trans_prob_float = [float(p) for p in trans_prob]
        g.add_edges(
            trans_list_int, trans_labels, trans_prob_float, fill_out=False, **edge_kwargs
        )

    elif type_aut == "NFA" or isinstance(g, NFA):
        if not g_defined:
            g = NFA(Euc=events_unctr, Euo=events_unobs, E=events)
            # A freshly-constructed empty NFA (init=None) starts with
            # vertex_attrs["init"] = [] -- _read_fsm_igraph instead
            # constructs from a scratch ig.Graph already holding
            # num_states vertices, which takes NFA.__init__'s other
            # branch and marks state 0 initial. Match that explicitly
            # here (only for the fresh-construction case -- an existing
            # caller-provided `g` keeps whatever it already had, exactly
            # as _read_fsm_igraph does for that case too).
            vertex_kwargs["init"] = [i == 0 for i in range(num_states)]
        g.add_vertices(num_states, names=state_names, marked=state_markings, **vertex_kwargs)
        g.add_edges(trans_list_int, trans_labels, fill_out=False, **edge_kwargs)

    else:
        # type_aut == "DFA" (explicit, inferred, or the default when
        # neither the file content nor an isinstance check said otherwise
        # -- matches _read_fsm_igraph's final `elif` falling through to
        # its own DFA branch first, so DFA is effectively the default).
        if not g_defined:
            g = DFA(None, events_unctr, events_unobs, events, False)
        g.add_vertices(num_states, names=state_names, marked=state_markings, **vertex_kwargs)
        g.add_edges(
            trans_list_int, trans_labels, check_DFA=False, fill_out=False, **edge_kwargs
        )

    return g
