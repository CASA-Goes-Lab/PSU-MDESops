# pylint: disable=C0103
"""
Function to transform an fsm with secret states and unobservable events into a nondeterminstic fsm without
 unobservable events while preserving the secrecy of trajectories
"""
from DESops.automata.NFA import NFA
from DESops.basic_operations.ureach import (
    unobservable_reach,
    ureach_from_set,
    ureach_ignore_states,
)


def contract_secret_traces(g, secret_type=1, h=None, Euo=None):
    """
    Function contracting unobservable events while preserving secrecy properties.

    Given the automaton 'g' with secret states and unobservable events, this function constructs a nondeterministic
    finite automaton (NFA) called 'h' without unobservable events that preserves the secrecy or opacity properties of
    'g' in a suitable sense. Depending on the value of anyNonsecIsNonsec, a sequence of unobservable transitions is
    called secret if it passes through a secret state or if it does not visit any nonsecret states. The NFA 'h' has the
    following properties:
    1) For every trajectory 'q' in 'g', there is a trajectory 'r' in 'h' so that
        i) the observable projection of 'q' is 'r'
        ii) the i^th sequence of unobservable transitions (separated by observable transitions) in 'q'  is secret if and
            only if the the i^th state visited in 'h' is secret.
    1) For every trajectory 'r' in 'h', there is a trajectory 'q' in 'g' so that
        i) the observable projection of 'q' is 'r'
        ii) the i^th sequence of unobservable transitions (separated by observable transitions) in 'q'  is secret if and
            only if the the i^th state visited in 'h' is secret.

    Parameters:
    g: given automaton with secret states

    secret_type: what behavior marks an observation period as secret
        1: an observation period is secret if it contains ANY secret state
        2: an observation period is secret if it contains ONLY secret states
    default is 1

    h: where to put the result of the construction
        if not specified, a new automaton will be constructed and returned

    Euo: set of unobservable events
        if not specified, Euo will be determined from g.Euo
    """
    h_defined = True
    if h is None:
        h = NFA()
        h_defined = False

    if Euo is None:
        Euo = g.Euo
    Q0 = g.vs.select(init=True).indices

    R = set()
    R.update(g.vs.select(init=True).indices)
    R.update([e.target for e in g.es.select(label_notin=Euo)])
    Rlist = list(R)

    # names must be in this form for language-based k-step opacity methods
    h.add_vertices(len(R), [(ind, 1) for ind in R])
    h.add_vertices(len(R), [(ind, 0) for ind in R])

    h.vs["marked"] = True

    h.vs.select(range(len(R)))["orig_vert"] = Rlist
    h.vs.select(range(len(R)))["secret"] = True
    h.vs.select(range(len(R), 2 * len(R)))["orig_vert"] = Rlist
    h.vs.select(range(len(R), 2 * len(R)))["secret"] = False

    secret_dict = {r: x for (x, r) in enumerate(Rlist)}
    nonsecret_dict = {r: (x + len(R)) for (x, r) in enumerate(Rlist)}

    Rs = set()
    Rns = set()
    for r in R:
        x_ureach = set()
        unobservable_reach(x_ureach, r, g._graph, Euo)
        if secret_type == 2:
            if not all(g.vs.select(x_ureach)["secret"]):
                Rns.add(r)
            if g.vs["secret"][r]:
                Rs.add(r)
        else:
            if any(g.vs.select(x_ureach)["secret"]):
                Rs.add(r)
            if not g.vs["secret"][r]:
                Rns.add(r)

    h.vs["init"] = False
    h.vs.select([secret_dict[r] for r in Rs if r in Q0])["init"] = True
    h.vs.select([nonsecret_dict[r] for r in Rns if r in Q0])["init"] = True

    orig_secret_set = set(g.vs.select(secret=True).indices)
    orig_nonsecret_set = set(g.vs.select(secret=False).indices)
    for r in R:
        ureach = set()
        unobservable_reach(ureach, r, g._graph, Euo)

        secret_succ = set()
        nonsecret_succ = set()
        if secret_type == 2:
            ureach_ignore_states(secret_succ, r, g, Euo, orig_nonsecret_set)
            nonsecret_ureach = set(g.vs.select(ureach, secret=False).indices)
            ureach_from_set(nonsecret_succ, nonsecret_ureach, g._graph, Euo)
        else:
            ureach_ignore_states(nonsecret_succ, r, g, Euo, orig_secret_set)
            secret_ureach = set(g.vs.select(ureach, secret=True).indices)
            ureach_from_set(secret_succ, secret_ureach, g._graph, Euo)

        obs_sec_succ_events = g.es.select(_source_in=secret_succ, label_notin=Euo)
        obs_nonsec_succ_events = g.es.select(_source_in=nonsecret_succ, label_notin=Euo)

        h.add_edges(
            [
                (secret_dict[r], secret_dict[e.target])
                for e in obs_sec_succ_events
                if e.target in Rs
            ],
            labels=[e["label"] for e in obs_sec_succ_events if e.target in Rs],
        )
        h.add_edges(
            [
                (secret_dict[r], nonsecret_dict[e.target])
                for e in obs_sec_succ_events
                if e.target in Rns
            ],
            labels=[e["label"] for e in obs_sec_succ_events if e.target in Rns],
        )
        h.add_edges(
            [
                (nonsecret_dict[r], secret_dict[e.target])
                for e in obs_nonsec_succ_events
                if e.target in Rs
            ],
            labels=[e["label"] for e in obs_nonsec_succ_events if e.target in Rs],
        )
        h.add_edges(
            [
                (nonsecret_dict[r], nonsecret_dict[e.target])
                for e in obs_nonsec_succ_events
                if e.target in Rns
            ],
            labels=[e["label"] for e in obs_nonsec_succ_events if e.target in Rns],
        )

    h.generate_out()

    if not h_defined:
        return h
