# pylint: disable=C0103
"""
Classes and methods related to state estimation for automata.

Motivated by Estimation and Inference in Discrete Event Systems by Christoforos N. Hadjicostis
"""
import igraph as ig


"""
The StateMapping class represents possible state transitions for finite systems.

The state transition information is represented in the state mapping as a directed bipartite graph with parts named
source and target. Both source and target consist of one node for each state of the original system. Possible
transitions from a state s to a state t is encoded in the graph by an edge from the node representing s in source to the
node representing t in target.
"""


class StateMapping:
    def __init__(self, num_states):
        """
        Create a state mapping with the given number of states with no transitions

        Parameters:
        num_states: the number of states in the original system
        """
        self.num_states = num_states

        # The bipartite graph
        self.g = ig.Graph(directed=True)
        self.g.add_vertices(2 * num_states)

    def add_transitions(self, transitions):
        """
        Add a state transition to the mapping as an edge in the graph.

        Parameters:
        transitions: transitions to add to the state mapping represented as a collection of tuples (source, target)
        """
        self.g.add_edges([(s, self.num_states + t) for (s, t) in transitions])

    def targets_from_source(self, state):
        """
        Returns the targets of a given source state in the mapping.

        Parameters:
        state: the source state of the original system
        """
        return {
            target - self.num_states for target in self.g.neighbors(state, mode="OUT")
        }

    def sources_from_target(self, state):
        """
        Returns the sources of a given target state in the mapping.

        Parameters:
        state: the target state of the original system
        """
        return set(self.g.neighbors(state + self.num_states, mode="IN"))

    def active_sources(self):
        """
        Returns the sources of the mapping with outgoing transitions.
        """
        return {s for s in range(self.num_states) if self.targets_from_source(s)}

    def active_targets(self):
        """
        Returns the targets of the mapping with incoming transitions.
        """
        return {s for s in range(self.num_states) if self.targets_from_source(s)}


def compose_state_mapping(sm_dest, sm1, sm2):
    """
    Construct a state mapping by composing two other state mappings on the same system. The resulting state mapping
    consists of transitions from a source to a target if and only if there exists a transition from source to a node
    intermediate in the first state mapping and a transition from intermediate to target in the second mapping.

    Parameters:
    sm_dest: the result of the composition is stored here
    sm1: the first state mapping
    sm2: the second state mapping
    """
    if not sm_dest.num_states == sm1.num_states or not sm1.num_states == sm2.num_states:
        raise ValueError("Number of states in mappings does not match.")
    n = sm_dest.num_states
    for source in range(n):
        target_set = set()
        intermediate = sm1.targets_from_source(source)
        for inter in intermediate:
            target_set.update(sm2.targets_from_source(inter))
        sm_dest.add_transitions([(source, target) for target in target_set])


"""
The StateTrajectory class represents possible state trajectories of fixed length for a finite system.

The state trajectory information is represented as a directed (T+1)-partite graph, where T is the trajectory length,
with parts corresponding to the step in the trajectory. Each part consists of one node for each state of the original
system. Possible transitions from a state s to a state t at a given step k is encoded in the graph by an edge from the
node representing s in the k^th part to the node representing t in the (k+1)^th part.

This structure is also known as a trellis diagram.
"""


class StateTrajectory:
    def __init__(self, num_states, num_steps):
        """
        Construct a state trajectory with the given number of states and number of steps.

        Parameters:
        num_states: the number of states of the original system
        num_steps: the number of steps in the trajectories considered
        """
        self.num_states = num_states
        self.num_steps = num_steps

        # the partite graph
        self.g = ig.Graph(directed=True)
        self.g.add_vertices(num_states * (num_steps + 1))

        # the terminal states with incoming transitions
        self.active_terminal = set()

    def add_transitions(self, transitions):
        """
        Add a state transition to the trajectory as an edge in the graph.

        Parameters:
        transitions: transitions to add to the trajectories as a collection of tuples (source, target, step)
        """
        self.g.add_edges(
            [
                (source + self.num_states * step, target + self.num_states * (step + 1))
                for (source, target, step) in transitions
            ]
        )
        self.active_terminal.update(
            [
                target
                for (source, target, step) in transitions
                if step == self.num_steps - 1
            ]
        )

    def successors(self, state, step):
        """
        Returns the successors of a state after a given step

        Parameters:
        state: the state of the original system to compute successors for
        step: the step number
        """
        if step == self.num_steps:
            return {}
        return {
            target - (step + 1) * self.num_states
            for target in self.g.neighbors(state + step * self.num_states, mode="OUT")
        }

    def predecessors(self, state, step):
        """
        Returns the predecessors of a state before a given step

        Parameters:
        state: the state of the original system to compute predecessors for
        step: the step number
        """
        if step == -1:
            return {}
        return {
            source - step * self.num_states
            for source in self.g.neighbors(
                state + (step + 1) * self.num_states, mode="IN"
            )
        }

    def active_states(self, step):
        """
        Return the active states in a given step.
        If the number of steps in the trajectory is more than 0, then this returns states with incoming transitions in
        step (step-1) or outgoing transitions in step (step).
        If the number of states in the trajectory is 0, then this returns the terminal states marked as active.

        Parameters:
        num_states: the number of states of the original system
        num_steps: the number of steps in the trajectories considered
        """
        if step < self.num_steps:
            return {s for s in range(self.num_states) if self.successors(s, step)}
        else:
            return {s for s in self.active_terminal}

    def __eq__(self, other):
        """
        Determine if this state trajectory is equal to another. This is done by comparing the successors of each state
        in each step and the active terminal states of both systems.

        Parameters:
        other: the other state trajectory to compute equality to
        """
        if (
            not self.num_states == other.num_states
            or not self.num_steps == other.num_steps
        ):
            return False
        for s in range(self.num_states):
            for step in range(self.num_steps):
                if not self.successors(s, step) == other.successors(s, step):
                    return False
        if self.num_steps == 0:
            if not self.active_terminal == other.active_terminal:
                return False
        return True

    def exists_avoiding_trajectory(self, avoid_states):
        """
        Returns whether there exists a single trajectory that avoids the given states in this structure or not.

        Parameters:
        avoid_states: the states of the original system to be avoided
        """
        not_avoid_states = set(range(self.num_states)).difference(avoid_states)
        backwards_reachable = not_avoid_states.intersection(self.active_terminal)
        for step in range(self.num_steps - 1, -1, -1):
            if not backwards_reachable:
                return False
            new_reachable = set()
            for s in backwards_reachable:
                new_reachable.update(self.predecessors(s, step))
            backwards_reachable = new_reachable.intersection(not_avoid_states)
        return bool(backwards_reachable)

    def is_empty(self):
        """
        Returns whether this state trajectory has any transitions
        """
        return self.g.ecount() == 0

    def can_visit(self, visit_states, step):
        """
        Returns whether or not there is a trajectory that can visit the given states in the given step

        Parameters:
        visit_states: the states to be visited
        step: the step to visit the states in
        """
        return bool(self.active_states(step).intersection(visit_states))


def construct_initial_state_trajectory(initial_states, num_states, num_steps):
    """
    Construct a state trajectory structure consisting of constant trajectories for each initial state.
    In the induced state trajectory automata, this is the initial state.

    Parameters:
    initial_state: the initial states of the original system
    num_states: the number of states in the original system
    num_steps: the length of trajectories considered
    """
    st = StateTrajectory(num_states, num_steps)
    st.add_transitions(
        [(s, s, step) for s in initial_states for step in range(num_steps)]
    )
    st.active_terminal.update(initial_states)
    return st


def construct_state_trajectory_from_mapping(sm):
    """
    Construct a state trajectory structure with 1 step induced by the given state mapping

    Parameters:
    sm: the state mapping
    """
    st = StateTrajectory(sm.num_states, 1)
    for s in range(sm.num_states):
        st.add_transitions([(s, t, 0) for t in sm.targets_from_source(s)])


def compose_state_trajectory_and_mapping(st_dest, st, sm):
    """
    Compose a state trajectory and a state mapping. The resulting state trajectory structure consists of trajectories of
    the original state trajectory structure followed by a transition from the state mapping, with the original step
    pruned to preserve the number of steps.

    Parameters:
    st_dest: the state trajectory to store the result in
    st: the state trajectory to compose
    sm: the state mapping to compose
    """
    if not st_dest.num_states == st.num_states or not st.num_states == sm.num_states:
        raise ValueError(
            "Number of states in trajectories and mappings does not match."
        )
    if not st_dest.num_steps == st.num_steps:
        raise ValueError("Number of steps in trajectories does not match.")
    n = st_dest.num_states

    # state trajectories have no transitions when k = 0, so this case is handled separately
    if st.num_steps == 0:
        for s in st.active_terminal:
            st_dest.active_terminal.update(sm.targets_from_source(s))
        return

    active = set()
    transitions = []
    for inter in range(n):
        targets = sm.targets_from_source(inter)
        sources = st.predecessors(inter, st_dest.num_steps - 1)
        if targets and sources:
            active.add(inter)
            transitions.extend([(inter, t, st_dest.num_steps - 1) for t in targets])
            # transitions.extend([(s, inter, st_dest.num_steps-2) for s in sources])

    for step in range(st_dest.num_steps - 2, -1, -1):
        new_active = set()
        for t in active:
            sources = st.predecessors(t, step + 1)
            if sources:
                new_active.update(sources)
                transitions.extend([(s, t, step) for s in sources])
        active = new_active
    st_dest.add_transitions(transitions)


def construct_induced_state_mappings(g, events):
    """
    Construct a the state mappings induced by the given automata for each of the given events.
    Returns a dictionary of state mappings indexed by events.

    Parameters:
    g: the original automata to compute the induced state mappings for
    events: the events of the automata to compute induced state mappings for
    """
    num_states = g.vcount()
    # events = set(g.es['label'])

    state_mappings = {}
    for event in events:
        sm = StateMapping(num_states)
        sm.add_transitions(
            [(trans.source, trans.target) for trans in g.es.select(label=event)]
        )
        state_mappings[event] = sm

    return state_mappings


def construct_induced_state_trajectory_automata(
    traj_auto,
    induced_trajectories,
    num_states,
    num_steps,
    state_mappings,
    initial_states,
):
    """
    Construct the induced state trajectory automataon from the provided state mappings dictionary.

    Parameters:
    traj_auto: the automaton to store the resulting automaton in
    induced_trajectories: a list of induced trajectories indexed by the states of traj_auto
    num_states: the number of states of the original system
    num_steps: the number of steps in the trajectories considered
    state_mappings: a dictionary of state_mappings of the original system indexed by events
    initial_states: a collection of initial states of the original system
    """
    initial_trajectory = construct_initial_state_trajectory(
        initial_states, num_states, num_steps
    )
    induced_trajectories.append(initial_trajectory)
    traj_auto.add_vertices(1)
    events = state_mappings
    if not events:
        return

    unexplored = {0}
    while unexplored:
        current_index = unexplored.pop()
        for event in events:
            new_traj = StateTrajectory(num_states, num_steps)
            compose_state_trajectory_and_mapping(
                new_traj, induced_trajectories[current_index], state_mappings[event]
            )
            if not new_traj.active_terminal:
                continue
            # print([(edge.source, edge.target - num_states * num_steps) for edge in new_traj.g.es])
            try:
                new_index = induced_trajectories.index(new_traj)
            except ValueError:
                new_index = len(induced_trajectories)
                traj_auto.add_vertex()
                induced_trajectories.append(new_traj)
                unexplored.add(new_index)
            traj_auto.add_edge(current_index, new_index, label=event)
