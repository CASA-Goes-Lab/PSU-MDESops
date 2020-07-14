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


def supr_contr_norm(G, H, preprocess=True):
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
    """

    Euo = G.Euo
    Euc = G.Euc
    # Process H, G to ensure conditions for ^CN computation
    #   1. H is a strict subautomat of G
    #   2. G is an SPA
    # NOTE: The states in H are not yet deleted and must be deleted in SCS
    if preprocess:
        # preH,preG = DFA(),DFA()
        (preH, preG) = strict_subautomata(H, G)
        # print(preG.vs["name"])
        obsG = observer_comp(preG)
        preG = parallel_comp([preG, obsG])
        preH = find_H(preG)
        print(preH.vs["name"])
        print(preG.vs["name"])
        # print(len(preH.vs))
        # print(preG.vs["out"])
    else:
        import warnings

        warnings.warn(
            "\nComputing the supremal controllable and normal sublanguage without strict subautomaton preprocessing\nAssuming that given H is a strict subautomaton of G\nStill preprocessing G,H to be Strict Partition Automata"
        )

        obsG = observer_comp(G)
        preG = parallel_comp([G, obsG])
        preH = find_H(preG)

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

    # obsG.vs["name"] = [frozenset(int(s) for s in name) for name in G_obs.vs["name"]]
    # G.vs["name"] = G_names
    # first_iter = True
    # while True:
    #     if not first_iter and not states_to_remove:
    #         break
    #     else:
    #         states_just_removed = scs(G, H, Euc, states_to_remove, first_iter)
    #     if not first_iter and not states_just_removed:
    #         break

    #     else:
    #         states_removed.update(states_just_removed)
    #         states_to_remove = sns(G, G_obs, H, Euc, Euo, states_removed)

    #     if first_iter:
    #         first_iter = False

    # return H


def find_inacc(G):
    """
    Returns a list of vertex indices of G that are inaccessible
    and should be removed.

    """
    Q = list()
    Q.append(0)
    good_states = set()
    good_states.add(0)
    while Q:
        v = Q.pop(0)

        neighbors = set()
        for t in G._graph.neighbors(v, mode="OUT"):
            if t in good_states:
                continue
            good_states.add(t)
            Q.append(t)

    bad_states = {v.index for v in G.vs if v.index not in good_states}
    return bad_states


def find_H(Gspa):
    states_del = set()
    for v in Gspa.vs:
        # print(v['name'][0][0])
        if v["name"][0][0] == "dead":
            states_del.add(v.index)
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
