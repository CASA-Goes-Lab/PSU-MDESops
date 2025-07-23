"""
Functions used for randomly generating automata
The implementation is modified from the FsmGenerator in the VEiP GitLab repository
"""

from random import choice, randint, randrange, sample, shuffle

from DESops.automata.DFA import DFA
from DESops.automata.event import Event
from DESops.automata.NFA import NFA
from DESops.file.igraph_pickle import write_pickle


def generate(
    num_states,
    num_events,
    min_trans_per_state=0,
    max_trans_per_state=None,  # if None, is set to num_events
    det=True,
    num_init=1,
    num_marked=0,
    num_secret=0,
    num_uo=0,
    num_uc=0,
    filename=None,
    enforce_accesibility=True,
    enforce_max_trans_per_state=True,
    prob_self_loop = 1
):
    """
    Returns a randomly generated automaton

    Events are named as: a b ... z aa ab ... az ba bb ...

    Usage:
    >>> G = generate_automaton()

    Note: the currently implemented method for generating automata can
        potentially reach a point where it is impossible to continue without
        violating the max_trans_per_state specification or rendering parts of
        the the graph inaccesible. This is particularly common for small
        numbers of events or transitions. By default, the generator will
        restart and try again when this problem occurs. This can
        significantly reduce performance. This feature can be disabled
        (allowing the automaton to contain inaccesible portions or violations
        of the max_trans_per_state specification, but potentially improving
        performance) via the enforce_accesibility and
        enforce_max_trans_per_state parameters.


    REQUIRED PARAMETERS:
    num_states: the number of states in the automaton

    num_events: the number of events in the automaton


    OPTIONAL PARAMETERS:
    min_trans_per_state:
        The minimum number of transitions out of each state
        By default this will be 0

    max_trans_per_state:
        The maximum number of transitions out of each state
        This is not guaranteed to be satisfied, especially when
            the value is small and close to min_trans_per_state
        By default this will be num_events

    det:
        Whether the automaton is deterministic
        By default it will be deterministic

    num_init:
        The number of initial states
        Requires det = False
        Requires 1 <= num_init <= num_states
        By default there will be one initial state (vertex 0)

    num_marked:
        The number of marked states
        Requires 0 <= num_marked <= num_states
        By default no states are marked

    num_secret:
        The number of secret states
        Requires 0 <= num_secret <= num_states
        By default no states are secret

    num_uo:
        The number of events that are unobservable
        Requires 0 <= num_uo <= num_events
        By default no events are unobservable

    num_uc:
        The number of events that are uncontrollable
        Requires 0 <= num_uc <= num_events
        By default no events are uncontrollable

    filename:
        If specified, the generated automaton will be saved as a pickle file to this location

    enforce_accesibility:
        Ensures that every vertex is accesible
        True by default

    enforce_max_trans_per_state:
        Ensures that the max_trans_per_state specification is satisfied at all vertices
        True by default

    prob_self_loop:
        The probability a self loop is present from 0 to 1. Default value is 1. 
    """
    generator = randomAutomata(
        num_states,
        num_events,
        min_trans_per_state,
        max_trans_per_state,
        det,
        num_init,
        num_marked,
        num_secret,
        num_uo,
        num_uc,
        enforce_accesibility,
        enforce_max_trans_per_state,
    )

    success = False
    while not success:
        success = generator.generate_automaton()
    generator.g.generate_out()
    self_loop_modifier(generator.g,prob_self_loop)

    if filename:
        write_pickle(filename, generator.g)

    return generator.g
    
def self_loop_modifier(G,prob_self_loop):
    delete = []
    for v in G.vs:
        if is_self_loop(v) == True:
            num = randint(1,10)
            if num > 10 * prob_self_loop:
                start = G.es.select(_from = v.index)
                end = start.select(_to = v.index)
                for e in end:
                    delete.append(e)
    G.delete_edges(delete)


def is_self_loop(vertex) -> bool:
    """
    Given an automata and vertex, returns True if the vertex contains
    a self loop, and false if it does not
    """
    try:
        vertex["out"][0][0]
    except IndexError:
        return False
    else:
        for out in vertex["out"]:
            if vertex.index == out[0]:
                return True
    return False
class randomAutomata:
    def __init__(
        self,
        num_states,
        num_events,
        min_trans_per_state,
        max_trans_per_state,
        det,
        num_init,
        num_marked,
        num_secret,
        num_uo,
        num_uc,
        enforce_accesibility,
        enforce_max_trans_per_state,
    ):
        # required parameters
        self.num_states = num_states
        self.num_events = num_events

        # optional parameters
        self.min_trans_per_state = min_trans_per_state

        if max_trans_per_state:
            self.max_trans_per_state = max_trans_per_state
        else:
            self.max_trans_per_state = num_events

        self.det = det
        self.num_init = num_init
        self.num_secret = num_secret
        self.num_marked = num_marked
        self.num_uo = num_uo
        self.num_uc = num_uc
        self.enforce_accesibility = enforce_accesibility
        self.enforce_max_trans_per_state = enforce_max_trans_per_state

        # initialization
        self.validate_parameters()

        if self.det:
            self.g = DFA()
        else:
            self.g = NFA()

        # names are str changing for that
        self.g.add_vertices(self.num_states, [str(i) for i in range(self.num_states)])

        self.event_names = list()
        self.generate_event_names()

    def validate_parameters(self):
        """
        Raises an exception if the input parameters were invalid
        """
        if self.num_states <= 0:
            raise ValueError("num_states must be greater than 0")
        if self.num_events <= 0:
            raise ValueError("num_events must be greater than 0")

        if self.min_trans_per_state < 0:
            raise ValueError("min_trans_per_state can't be negative")
        if self.max_trans_per_state < self.min_trans_per_state:
            raise ValueError(
                "max_trans_per_state can't be less than min_trans_per_state"
            )

        if self.det and self.max_trans_per_state > self.num_events:
            raise ValueError(
                "max_trans_per_state can't be greater than num_events for a deterministic automaton"
            )
        if self.max_trans_per_state > self.num_events * self.num_states:
            raise ValueError(
                "max_trans_per_state can't be greater than num_events * num_states"
            )

        if self.det and self.num_init != 1:
            raise ValueError("num_init must be 1 for a deterministic atuomaton")

        if self.num_init < 1 or self.num_init > self.num_states:
            raise ValueError("num_init must be between 1 and num_states")
        if self.num_marked < 0 or self.num_marked > self.num_states:
            raise ValueError("num_marked must be between 0 and num_states")
        if self.num_secret < 0 or self.num_secret > self.num_states:
            raise ValueError("num_secret must be between 0 and num_states")

        if self.num_uo < 0 or self.num_uo > self.num_events:
            raise ValueError("num_uo must be between 0 and num_events")
        if self.num_uc < 0 or self.num_uc > self.num_events:
            raise ValueError("num_uc must be between 0 and num_events")

    def generate_event_names(self):
        """
        Generates the names for the events and stores them in the list self.event_names
        """
        for i in range(self.num_events):
            name = ""
            while True:
                name = chr(ord("a") + (i % 26)) + name
                overflow = int(i / 26)
                if overflow:
                    i = overflow - 1
                else:
                    break
            self.event_names.append(Event(name))

    def initialize_automaton(self):
        """
        Resets the automaton to be ready for generation
        """
        # delete any existing edges
        self.g._graph.delete_edges(None)

        # initialize state storage to be used when generating the automata
        self.unprocessed_children = set()
        self.processed_children = set()
        self.unprocessed_states = set(range(self.num_states))
        self.processed_states = set()

        # randomize the attributes
        if self.num_init == 1:
            self.g.vs["init"] = False
            self.g.vs[0]["init"] = True
        else:
            ids = sample(range(self.num_states), self.num_init)
            self.g.vs["init"] = [(i in ids) for i in range(self.num_states)]

        ids = sample(range(self.num_states), self.num_marked)
        self.g.vs["marked"] = [(i in ids) for i in range(self.num_states)]

        ids = sample(range(self.num_states), self.num_secret)
        self.g.vs["secret"] = [(i in ids) for i in range(self.num_states)]

        # Events are of type Event and are stored as sets
        ids = sample(range(self.num_events), self.num_uo)
        self.g.Euo.update(self.event_names[i] for i in ids)

        # Events are of type Event and are stored as sets
        ids = sample(range(self.num_events), self.num_uc)
        self.g.Euc.update(self.event_names[i] for i in ids)

        # Events are of type Event and are stored as sets
        self.g.events = set(self.event_names)

    def generate_automaton(self):
        """
        The main function that generates the automaton
        """
        self.initialize_automaton()

        # Start by creating the children of the initial states
        initial_states = [v.index for v in self.g.vs if v["init"]]
        for state in initial_states:
            self.make_children(state, True)

            # Put all children of the initial states into the unprocessed_hildren stack:
            self.save_unprocessed_children(state)

        while True:
            while self.unprocessed_children:
                state = self.unprocessed_children.pop()
                self.make_children(state, False)
                self.processed_children.add(state)

            # If all the states have been assigned children (min to max - possibly 0),
            #  no need to find any more children states:
            if not self.unprocessed_states:
                break

            # Now, all child states have been processed (new children created for each of the previous
            #  child states).  For each processed child state, find all of their child states and add
            #  to the unprocessed_children stack.
            while self.processed_children:
                state = self.processed_children.pop()
                self.save_unprocessed_children(state)

            if (
                not self.unprocessed_children
                or len(self.processed_states) == self.num_states
            ):
                break

        #
        # ************  Do some final processing   ************
        #   this is generally needed with the minimum # of events per state is 0
        #
        # if unprocessed_states is NOT empty we need to tie these into the fsm:
        while self.unprocessed_states:
            state = self.unprocessed_states.pop()

            # If this unprocessed state is NOT a child of some other state, it needs to be added into
            #  the FSM as a child of some state already in the FSM:
            if not self.g.vs[state].indegree():
                potential_parents = list(self.processed_states)

                okay_parent = None
                good_parent = None
                event = None

                # Find a potential parent state which doesn't already a number of transitions
                #  equal to the max_trans_per_state:
                while True:
                    okay_parent = choice(potential_parents)
                    potential_parents.remove(okay_parent)

                    if self.g.vs[okay_parent].outdegree() < self.max_trans_per_state:
                        good_parent = okay_parent
                        if self.det:
                            event = choice(self.find_unused_events(good_parent))
                        else:
                            event = choice(self.event_names)

                        self.g.add_edge(good_parent, state, event, fill_out=True)
                        break

                    if not potential_parents:
                        break

                if good_parent is None:
                    if self.det:
                        unused_events = self.find_unused_events(okay_parent)
                        if unused_events:
                            event = choice(unused_events)
                        else:
                            # find a different okay parent that has unused events
                            potential_parents = list(self.processed_states)
                            shuffle(potential_parents)
                            for okay_parent in potential_parents:
                                unused_events = self.find_unused_events(okay_parent)
                                if unused_events:
                                    event = choice(unused_events)
                                    break
                    else:
                        event = self.event_names[randrange(self.num_events)]

                    if event is not None:
                        # unable to make accesible without too many transitions
                        if self.enforce_max_trans_per_state:
                            return False
                        self.g.add_edge(okay_parent, state, event, fill_out=True)
                    # unable to make this accesible without violating determinism
                    elif self.enforce_accesibility:
                        return False

            # Add transitions from this state:
            self.make_children(state, False)

        return True

    def find_unused_events(self, state):
        """
        Returns a list of all events that are not used by any outgoing transition from the given state
        """
        events = self.event_names.copy()
        for e in self.g.vs[state].out_edges():
            if e["label"] in events:
                events.remove(e["label"])
        return events

    def save_unprocessed_children(self, state):
        """
        Puts all unprocessed children of the given state into self.unprocessed_children
        """
        for e in self.g.vs[state].out_edges():
            # Important: if state s has a transition to itself, don't add it to the unprocessed
            #  children stack; also don't add the transition state, if it has already been processed
            if e.target != state and e.target not in self.processed_states:
                self.unprocessed_children.add(e.target)

    def make_children(self, state, is_init):
        """
        Creates children states from the given parent state and moves the
        parent state from self.unprocessed_states to self.processed_states
        """
        # ONLY create children for this state, if there isn't any already:
        if self.g.vs[state].outdegree():
            return
        # ONLY create children for this state, it not already done:
        if state in self.processed_states:
            if state in self.unprocessed_states:
                self.unprocessed_states.remove(state)
            return

        # Get a random number of transitions from this state:
        num_transitions = randint(self.min_trans_per_state, self.max_trans_per_state)

        if is_init and num_transitions == 0:
            num_transitions = 1

        # Initialize local lists
        avail_states = list(range(self.num_states))
        avail_events = list(range(self.num_events))

        for _ in range(num_transitions):
            event = None
            next_state = None

            while next_state is None:
                if avail_events:
                    event = choice(avail_events)
                    # For deterministic fsm's, don't allow the same event to be used more than once,
                    #  for a given state's transitions.
                    if self.det:
                        avail_events.remove(event)
                if event is None:
                    continue

                # calculate avail_states to be the states
                avail_states = list(range(self.num_states))
                for t in self.g.vs[state].out_edges():
                    if (
                        t["label"] == self.event_names[event]
                        and t.target in avail_states
                    ):
                        avail_states.remove(t.target)
                # Now get a random next state that this event will lead to
                if avail_states:
                    next_state = choice(avail_states)
                    # avail_states.remove(next_state)
                else:
                    avail_events.remove(event)

            self.g.add_edge(state, next_state, self.event_names[event], fill_out=True)

        # Now, add the (parent) state to the list of processed states
        self.processed_states.add(state)
        #  and remove this (parent) state from the list of unprocessed states:
        if state in self.unprocessed_states:
            self.unprocessed_states.remove(state)
