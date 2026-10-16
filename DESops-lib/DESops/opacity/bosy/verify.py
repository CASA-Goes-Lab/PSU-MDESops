"""
Functions for verifying that the output of BoSy synthesis has correct behavior
"""

from collections import deque


def verify_edit_function(g, cntl):
    """
    Check whether the given automaton is current-state opaque under the given edit function

    Parameters:
    g: the automaton
    cntl: the edit function given as a transducer automaton with events labeled in the form "{input_event}/{output_event}"

    Returns:
    True if CSO is enforced, False if it is not
    """
    # if any initial state is secret, enforcement is impossible
    if any(v["secret"] for v in g.vs.select(init=True)):
        return False

    # add initial states in form (real state, observed state, controller state)
    init_states = [
        (u.index, u.index, v.index)
        for u in g.vs.select(init=True)
        for v in cntl.vs.select(init=True)
    ]
    states_to_check = deque(init_states)
    states_checked = set()

    # iterate through states until we've checked all reachable states
    while states_to_check:
        state = states_to_check.pop()
        states_checked.add(state)
        real_source, obs_source, cntl_source = state

        # map input event to output event
        edit_events = dict()
        # map input event to next state in controller
        cntl_targets = dict()
        for cntl_target, cntl_event in cntl.vs[cntl_source]["out"]:
            event_i, event_o = cntl_event.split("/")
            edit_events[event_i] = event_o
            cntl_targets[event_i] = cntl_target

        # if we had empty input, then this is an insertion
        insertion = "" in edit_events

        # map events to next state in real automaton
        real_targets = dict()
        for real_target, real_event in g.vs[real_source]["out"]:
            real_targets[real_event] = real_target
        # event insertion doesn't change real state
        real_targets[""] = real_source

        # map events to next state in observed automaton
        obs_targets = dict()
        for obs_target, obs_event in g.vs[obs_source]["out"]:
            obs_targets[obs_event] = obs_target

        # determine next state after each possible input event
        for real_target, real_event in g.vs[real_source]["out"]:
            if insertion:
                # event insertion: input event is empty string
                real_event = ""

            out_event = edit_events[real_event]
            next_real = real_targets[real_event]
            next_obs = obs_targets[out_event]
            next_cntl = cntl_targets[real_event]
            next_state = (next_real, next_obs, next_cntl)

            # enforcement failed if we observe a secret state
            if g.vs[next_obs]["secret"]:
                return False

            # if state is new, add it to the queue
            if next_state not in states_checked:
                states_to_check.append(next_state)

            # event insertion: we only have one input (the empty string)
            if insertion:
                break

    # if we checked all possible states without finding a secret one, enforcement was successful
    return True


# TODO - it would be nice to have a function for checking the behavior of the inferrer as well
