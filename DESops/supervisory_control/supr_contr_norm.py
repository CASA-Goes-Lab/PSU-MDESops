"""
Functions relevant to computing the supremal controllable and normal supervisor
of given system and specifcation automata.

supremal_cn_supervisor() computes and returns the SCNS as an igraph Graph.

The cn_preprocessing module (cn_pp.py) handles necessary preprocessing,
and returns modified system/specifiation automata that meet the necessary
assumptions in the SCNS algorithm.

The required assumptions are:

1. H (the specification) is a strict subautomata of G
2. G is an SPA (state partitioned automaton)

TODO: implement a supremal_cn_supervisor_pp() function that performs
preprocessing and calls supremal_cn_supervisor(), which performs
no preprocessing (similar to how the SCS is handled).
"""


from DESops.automata.DFA import DFA
from DESops.basic_operations import composition

from ..basic_operations.construct_subautomata import strict_subautomata
from ..basic_operations.observer_comp import observer_comp
from ..basic_operations.parallel_comp import parallel_comp
from ..basic_operations.product_comp import product_comp
from ..basic_operations.refine_product import refine_product_SCS
from ..basic_operations.unary import find_inacc
from ..visualization.plot import plot


def supr_contr_norm(G, H=None, preprocess=True, X_crit=None):
    """
    Computes the supremal controllable-normal supervisor for the given
    plant and specification Automata. An iterative process is used, where the
    specification is modified to meet the controllability condition, then the
    normality condition, ..., until convergance when the most recent controllable
    specification matches the most recent normal specification. Convergence is
    checked by verifying no states were removed in the last controllable/normal
    evaluation step.

    Returns: an igraph Graph as the automata realization of the supremal
    controllable-normal supervisor.

    Parameters:
    G: plant/system as an automaton.
    H: specification as an automaton.

    If preprocess=False: will extract critical states from G, either by states named "dead" or by specified X_crit vertice names

    Valid inputs:
        (H, preprocess)
        (H, not prep)
        (not prep, X_crit)
    """

    Euo = G.Euo
    Euc = G.Euc
    # Process H, G to ensure conditions for ^CN computation
    #   1. H is a strict subautomat of G
    #   2. G is an SPA
    # NOTE: The states in H are not yet deleted and must be deleted in SCS
    if preprocess:
        (preH, preG) = strict_subautomata(H, G)
        obsG = observer_comp(preG)
        preG = parallel_comp([preG, obsG])
        preH = find_H(preG)
    else:
        import warnings

        warnings.warn(
            "\nComputing the supremal controllable and normal sublanguage without strict subautomaton preprocessing\nAssuming that given H is a strict subautomaton of G\nStill preprocessing G,H to be Strict Partition Automata"
        )
        t = G.vs["name"]
        if X_crit:
            G.vs["name"] = ["dead" if v in X_crit else v for v in G.vs["name"]]
        tt = G.vs["name"]
        obsG = observer_comp(G)
        preG = parallel_comp([G, obsG])
        ttt = preG.vs["name"]
        preH = find_H(preG)

    teeeeee = preG.vs["out"]
    if preH is None:
        # no solution
        # todo warn here
        return DFA()

    # For each state:
    # 2.1: Compute normality condition
    # 2.2: Compute controllability condition
    # 2.3: find_inacc (ensure we are only checking accessible states in the first place)
    # Collect set of good states, find set diff total_states - good_states = bad_states
    # delete all bad states, resulting in K^CN
    # states_removed = set()

    G_names = {i: v["name"] for i, v in enumerate(preG.vs)}
    preG.vs["name"] = [str(i) for i in range(preG.vcount())]
    preH.vs["name"] = [
        str(i) for i, v in enumerate(preG.vs) if preH.vs.select(name_eq=G_names[i])
    ]
    # # G_obs names are sets of states as strings. int(s) are indices in G, where s are those strings
    obsG = observer_comp(preG)
    obsG_names = obsG.vs["name"]
    dict_Gstate_obsGstate = {st: n for n in obsG_names for st in n}
    if "in" not in preG.vs.attributes():
        incoming_adj = [[] for _ in range(preG.vcount())]
        for e in preG.es():
            incoming_adj[e.target].append((e.source, e["label"]))
        preG.vs["in"] = incoming_adj
    preG_name_dict = {v["name"]: v for v in preG.vs()}
    # Finding which states were already delete from G to compute H
    all_del_states = set(preG.vs["name"]) - set(preH.vs["name"])
    new_del_states = set(preG.vs["name"]) - set(preH.vs["name"])

    # at the beggining new_del_states always have states that we must check controllability
    while new_del_states:
        preH_name_dict = {v["name"]: v.index for v in preH.vs()}
        # controllability check
        states_to_check_ctr = set(new_del_states)
        ctr_next_it = set()
        for x in states_to_check_ctr:
            for prev_state in preG.vs["in"][int(x)]:
                if (
                    preG.vs["name"][prev_state[0]] in preH.vs["name"]
                    and prev_state[1] in Euc
                ):
                    ctr_next_it.add(preG.vs["name"][prev_state[0]])
                    new_del_states.add(preG.vs["name"][prev_state[0]])
                    all_del_states.add(preG.vs["name"][prev_state[0]])

        # normality
        # saving which states were added in new_del_states that we haven't check ctr
        # this will be used to not check twice ctr in each state
        # states_add_ctr = new_del_states - old_del_states

        #
        old_del_states = set(new_del_states)

        # this will hold which new states must be deleted due to violation of normality
        new_del_states = set()

        for x in old_del_states:
            # normality check since G is SPA
            #    - check the if all states in the partition of a new to be deleted state is
            #    - were already deleted;
            #    - if this test fails then all states in this partition must be deleted
            if not dict_Gstate_obsGstate[x].issubset(all_del_states):
                new_del_states = new_del_states.union(
                    dict_Gstate_obsGstate[x].difference(all_del_states)
                )
                all_del_states = all_del_states.union(new_del_states)

        # computing deleted states that we must check controllability in the next iteration
        new_del_states = ctr_next_it | new_del_states

        # finding the indices of these state in preH
        # states_to_remove = [v.index for v in preH.vs.select(name_in=new_del_states)]
        states_to_remove = [
            preH_name_dict[v] for v in new_del_states if v in preH_name_dict
        ]
        preH.delete_vertices(states_to_remove)
        # computing accessible part
        inacc_states = find_inacc(preH)
        inacc_states_names = {preH.vs["name"][v] for v in inacc_states}
        preH.delete_vertices(inacc_states)

        # augmenting new_del_states with states deleted due inaccessibility
        new_del_states = new_del_states | inacc_states_names
    if preH.vcount() == 0:
        import warnings

        warnings.warn(
            "\nPrefix closed Sup CN has no solution for given G,H\n Returning an empty automaton"
        )
        return DFA()
    else:
        return preH


def find_H(Gspa):
    states_del = {v.index for v in Gspa.vs if v["name"][0][0] == "dead"}
    # print(states_del)
    if 0 in states_del:
        return None
    H = DFA(Gspa)
    H.delete_vertices(states_del)
    inacc_states = find_inacc(H)
    H.delete_vertices(inacc_states)
    H.generate_out()
    return H


def scs(G, S, Euc, states_to_remove, first_iter):
    """
    Computes the supremal controllable supervisor.
    Used here to take advantage of the intermediate structure
    in the iterative process of computing the SCNS (as opposed to
    using the supremal_controllable_supervisor module). As such,
    an actual supervisor is not computed; rather, the states violating
    the controllability condition are removed from S.

    When this function is called, the only states violating the controllability
    condition should be those with uncontrollable transitions targetting a recently
    removed state. That is, only successors to states_to_remove must be checked
    for the controllability condition. Using the supremal_controllable_supervisor
    module would mean every state gets checked (same worst case computation time,
    but in general this should be significantly faster).

    Returns list of names of vertices of G that were removed (in
    this particular iteration).

    Parameters:
    G: system automaton as an igraph Graph
    S: specification/controller automaton as an igraph Graph
    Euc: set of uncontrollable events
    states_to_remove: the states most recently identified as needing
        to be deleted. Those states will be removed, along with inaccessible
        states at the end of the function.
    first_iter: bool, True if first iteration of SCS. If it's not the first
        iteration, the trim will be computed.
    """

    inacc_states = set()
    if not first_iter:
        inacc_states = find_inacc(S)

    # only need to check the predecessors of states marked for removal which are still reachable
    states_removed = set(states_to_remove).difference(inacc_states)

    states_to_check = set()
    for v in states_to_remove:
        for e_i in S._graph.incident(v, mode="IN"):
            e = S.es[e_i]
            if (
                e["label"] in Euc
                and e.source not in states_removed
                and e.source not in inacc_states
            ):
                states_to_check.add(e.source)

    while states_to_check:
        states_removed.update(states_to_check)

        states_to_check_new = set()
        for v in states_to_check:
            for e_i in S._graph.incident(v, mode="IN"):
                e = S.es[e_i]
                if (
                    e["label"] in Euc
                    and e.source not in states_removed
                    and e.source not in inacc_states
                ):
                    states_to_check_new.add(e.source)

        states_to_check = states_to_check_new
    G_removed_vs_names = {S.vs[v]["name"][1] for v in states_removed}
    S.delete_vertices(states_removed | inacc_states)
    return G_removed_vs_names


def sns(G, G_obs, S, Euc, Euo, states_removed):
    """
    Computes the supremal normal supervisor (really just returns
    a set of states that violate the normality condition and need to
    be deleted).

    Returns bad_states, a set of states violating the normality condition.

    Parameters:
    G: system automaton as an igraph Graph
    G_obs: observer automaton of G, as an igraph graph
    S: spec/controller automaton as an igraph Graph
    Euc: set of uncontrollable events
    Euo: set of unobservable events
    states_removed: set of states removed from S in the last iteration.
    """
    q_dict = dict()
    bad_states = set()
    states_yi = {v["name"][1] for v in S.vs}
    # Q = list()
    for yi in S.vs:
        for q in G_obs.vs["name"]:
            if yi["name"][1] in q:
                # Make sure q is in Yi
                if q in q_dict:
                    if not q_dict[q]:
                        bad_states.add(yi.index)
                else:
                    good_state = q.issubset(states_yi)
                    q_dict[q] = good_state
                    if not good_state:
                        bad_states.add(yi.index)

    return bad_states
