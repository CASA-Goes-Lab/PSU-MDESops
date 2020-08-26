import itertools
import os
import subprocess
import time
from collections import deque

import igraph as ig
import pydash

from DESops.automata.DFA import DFA
from DESops.automata.event import Event
from DESops.basic_operations import composition
from DESops.supervisory_control import supervisor


def construct_AES(G, spec, compact=True, preprocess=True):
    # arena: igraph graph object where resulting arena will be stored, assumed to be empty
    # G: input system automata
    # spec: Either an automata representing the specification or a set of critical states
    #   (names of states in G)

    if not isinstance(spec, DFA) and not isinstance(spec, set):
        raise TypeError(
            "Expected spec to be type DFA or set (of names of critical states). Got {}".format(
                type(spec)
            )
        )
    if isinstance(spec, DFA):
        # TODO: test this, I think most of the time X_crit is specified so this hasn't been used a lot
        # Need to construct H_o as refined product of GxH to determine infinite-cost states

        _, G = composition.strict_subautomata(spec, G, skip_H_tilde=True)
        X_crit_vs = set(i.index for i in G.vs if i["name"][0] == "dead")
        G.vs["name"] = [str(i) for i in range(G.vcount())]

    else:
        # X_crit provided; specification is plant w/o X_crit states
        X_crit_vs = set(i.index for i in G.vs if i["name"] in spec)

    # Computing the control decision set
    process_G(G)
    Eo = G.events - G.Euo
    if compact:
        # Finding the compact control decision set
        Gamma = find_compact_control_decisions_sets(G.events, G.Euc, G.Euo)
    else:
        Gamma = find_control_decisions_sets(G.events, G.Euc)

    # get infinite cost states:
    X_crit_vs = G.compute_state_costs(starting_states=X_crit_vs)

    # Q1 and Q2 states map name to vertex index for BTS and set of vertex indices of G; init state is 0
    Q1, Q2 = dict(), dict()
    Qname, Qcrit = list(), list()
    # holds the names of each state in order of their vertex index
    # transitions for igraph constructed using vertex index
    h1, h2 = list(), list()

    # transitions labels map labels to transitions h1, h2
    labelh1, labelh2 = list(), list()
    Q1[frozenset({0})] = 0
    queue = deque()
    Qname.append(setvs2statename(G, {0}))
    Qcrit.append(0)
    queue.append({0})

    # constructs the BTS in a BFS manner based on Gamma
    A = construct_T(
        G, Qname, Qcrit, Q1, Q2, h1, h2, labelh1, labelh2, queue, X_crit_vs, Gamma
    )
    # Pruning the BTS: (1) find states that violate X_crit (2) supremal controllable
    Aout = A.vs["out"]
    # Find states that violate X_crit
    M = find_violation(A)

    # Construct specification. This spec is already a strict subautomaton of A
    Atrim = DFA(A)
    Atrim.delete_vertices(M)

    # Finding supcon based on A and Atrim
    # AES = supr_contr.supr_contr(A, Atrim, mark_states=False, preprocess=False)
    AES = supervisor.supremal_sublanguage(
        A,
        Atrim,
        mode=supervisor.Mode.CONTROLLABLE,
        preprocess=False,
        prefix_closed=True,
    )
    AES.events = G.events.copy()

    # clear "out_dict" attr
    del G.vs["out_dict"]

    return AES, A


def construct_T(
    G, Qname, Qcrit, Q1, Q2, h1, h2, labelh1, labelh2, queue, X_crit, Gamma
):
    # G: the plant automaton
    # Qnames: list of names of each state in order of their vertex index
    # Q1,Q2: dictionary state_names: index (position in Qnames)
    # h1,h2: transition function based on Qnames index
    # labelh1,labelh2: transition event label in order with h1,h2
    # queue: list of states to visit in the arena
    # X_crit: safety specification. It is used as a stop condition for the construction of T_comp
    # Gamma: set of control decisions

    A = DFA()

    # index counter saves the current vertex index
    vertex_counter = 1

    Eo = G.events - G.Euo
    Euo = frozenset(G.Euo)
    # used to not recompute UR
    UR_state_classes = dict()
    n = 0
    # queue holds states that must be visited
    sumq1, sumq2 = 0, 0
    while queue:

        q = queue.popleft()

        if Q1_state(q):

            qvs = frozenset(q)
            start_time = time.process_time()
            # Finding the feasible control decision (SLOWER THAN WITHOUT IT)
            # if (qvs, Euo) in UR_state_classes:
            #     qureach = UR_state_classes[qvs, Euo]
            #     ctr = feasible_control_decisions(qureach, Gamma, G)
            # else:
            #     qureach = ureach_from_set_adj(qvs, G._graph, G.Euo)
            #     ctr = feasible_control_decisions(qureach, Gamma, G)
            #     UR_state_classes[(qvs, Euo)] = qureach

            # print(len(ctr))

            for gamma in Gamma:
                q2_state = G.UR.from_set(qvs, frozenset(G.Euo.intersection(gamma)))
                """
                if (qvs, frozenset(G.Euo.intersection(gamma))) in UR_state_classes:

                    q2_state = UR_state_classes[
                        (qvs, frozenset(G.Euo.intersection(gamma)))
                    ]
                else:
                    q2_state = ureach_from_set_adj(
                        qvs, G._graph, G.Euo.intersection(gamma)
                    )

                    UR_state_classes[
                        (qvs, frozenset(G.Euo.intersection(gamma)))
                    ] = q2_state
                    """
                q2 = (q2_state, gamma)
                vertex_counter = Q2_add_state(
                    Q1[qvs],
                    q2,
                    G,
                    Qname,
                    Qcrit,
                    Q2,
                    h1,
                    labelh1,
                    queue,
                    vertex_counter,
                    X_crit,
                    n,
                )
            sumq1 = sumq1 + time.process_time() - start_time

        if Q2_state(q):
            start_time = time.process_time()
            gamma = q[1]
            states = q[0]
            # print(gamma,Eo.intersection(gamma))
            inter = Eo.intersection(gamma)
            for e in inter:

                # nxstates = {v[0] for i in states for v in G.vs["out"][i] if v[1] == e}
                nxstates = {
                    G.vs["out_dict"][i][e] for i in states if e in G.vs["out_dict"][i]
                }
                # print(nxstates)
                if nxstates:
                    vertex_counter = Q1_add_state(
                        nxstates,
                        Q2[(frozenset(q[0]), frozenset(q[1]))],
                        e,
                        G,
                        Qname,
                        Qcrit,
                        Q1,
                        h2,
                        labelh2,
                        queue,
                        vertex_counter,
                        X_crit,
                        n,
                    )
            sumq2 = sumq2 + time.process_time() - start_time
    # print(sumq1 / len(Q1), sumq2 / len(Q2))

    # Creating BTS as DFA
    if Qname:
        args = {"crit": Qcrit}
        A.add_vertices(len(Qname), Qname, **args)
        # h1.extend(h2)
        # labelh1.extend(labelh2)
        # print(len(h1),len(labelh1))
        A.add_edges(h1, labelh1)
        A.add_edges(h2, labelh2)

    Ev = generate_ev_uc(Gamma, G.Euc)
    # print(Ev[0], Ev[1])

    A.events = G.events.copy()
    A.events = A.events.union(Ev[0])
    A.Euc.update(G.events)
    A.Euc.add(Ev[1])
    A.generate_out()

    return A


def feasible_control_decisions(q, Gamma, G):
    # possible_events = set(G.es(_source_in=q)["label"])
    possible_events = {e for s in q for t, e in G.vs["out"][s]}
    all_sets = set()
    for l in range(len(possible_events) + 1):
        all_sets.update(
            frozenset(G.Euc.union(comb))
            for comb in itertools.combinations(possible_events, l)
            if frozenset(G.Euc.union(comb)) in Gamma
        )
    return all_sets


def find_violation(A):
    return [v.index for v in A.vs.select(crit_eq=1)]


def generate_ev_uc(Gamma, Euc):
    E = set()
    for ctr in Gamma:
        if ctr == Euc:
            ev = Event(ctr)
        E.add(Event(ctr))
    return (E, ev)


# Adds Q1 state to lists
def Q1_add_state(
    q1, q2, ev, G, Qname, Qcrit, Q1, h2, labelh2, queue, v_counter, X_crit, n
):
    q1f = frozenset(q1)
    if q1f not in Q1:
        Q1[q1f] = v_counter + n
        v = v_counter + n
        # If there is not any critical state in q1 state estimate then add to queue
        if not q1.intersection(X_crit):
            queue.append(q1)
            Qcrit.append(0)
        else:
            Qcrit.append(1)

        q1name = setvs2statename(G, q1)
        # print(q1name)
        Qname.append(q1name)
        v_counter += 1

    else:
        v = Q1[q1f]
    h2.append((q2, v))
    # print(ctr2str(gamma))
    labelh2.append(ev)
    return v_counter


def process_G(G):
    out_list = list()
    for i, s in enumerate(G.vs):
        out = G.vs["out"][i]
        out_dict = {e: t for (t, e) in out}
        out_list.append(out_dict)
    G.vs["out_dict"] = out_list


# Adds Q2 state to lists
def Q2_add_state(q1, q2, G, Qname, Qcrit, Q2, h1, labelh1, queue, v_counter, X_crit, n):
    q20 = frozenset(q2[0])
    if (q20, q2[1]) not in Q2:
        Q2[(q20, q2[1])] = v_counter + n
        v = v_counter + n
        # If there is not any critical state in q2 state estimate then add to queue
        if not q2[0].intersection(X_crit):
            queue.append(q2)
            Qcrit.append(0)
        else:
            Qcrit.append(1)
        q2name = ",".join([setvs2statename(G, q2[0]), ctr2str(q2[1])])
        # print(q2name)
        Qname.append("".join(["(", q2name, ")"]))
        v_counter += 1
    else:
        v = Q2[(q20, q2[1])]
    h1.append((q1, v))
    # print(ctr2str(gamma))
    labelh1.append(Event(q2[1]))
    return v_counter


# checks if Q1 state
def Q1_state(q):
    return isinstance(q, set)


# checks if Q2 state
def Q2_state(q):
    return isinstance(q, tuple)


# Finds all possible compact control decisions
def find_compact_control_decisions_sets(E, Euc, Euo):
    Ec = E.difference(Euc)
    Ecuo = list(Ec.intersection(Euo))
    Eco = list(Ec.intersection(E - Euo))
    # print(Ec,Ecuo,Eco)
    GammaEcuo = set()
    for l in range(len(Ec) + 1):
        GammaEcuo = GammaEcuo.union(
            set(
                [frozenset(Euc.union(comb)) for comb in itertools.combinations(Ecuo, l)]
            )
        )
    # print(GammaEcuo)
    Gamma = set()
    for e in Eco:
        Gamma = Gamma.union(set([frozenset(gamma.union({e})) for gamma in GammaEcuo]))
    Gamma = Gamma.union(GammaEcuo)
    # print(Gamma)
    return Gamma


# Finds all possible control decisions
def find_control_decisions_sets(E, Euc):
    Ec = list(E - Euc)
    # print(Ec)
    Gamma = list()
    for l in range(len(Ec) + 1):
        Gamma.extend(
            [frozenset(Euc.union(comb)) for comb in itertools.combinations(Ec, l)]
        )
    return set(Gamma)


# Transforms a control decision to string
#       set is much more useful
def ctr2str(gamma):
    name = str()
    first = True
    for e in gamma:
        if first:
            name = "".join(["{", str(e.label)])
            first = False
        else:
            name = ",".join([name, str(e.label)])
    return "".join([name, "}"])


# transforms a set of vertices to a string with their respective names
def setvs2statename(G, set_states):
    name = str()
    first = True
    for v in set_states:
        if first:
            name = "".join(["{", G.vs["name"][v]])
            first = False
        else:
            name = ",".join([name, G.vs["name"][v]])
    return "".join([name, "}"])


def extract_AES_super(AES):
    """
    Algorithm 1 in efficient AES paper

    Extracts a supervisor from the AES structure
    """
    if AES.vcount() == 0:
        return DFA()
    # bfs:
    queue = []

    # transitions, init empty
    trans = []
    trans_labels = []

    # store states as vertices in original AES?
    states = dict()
    # add initial state
    states[0] = 0

    queue.append(0)
    while queue:
        v = queue.pop()
        # select largest control decision from this state
        out = AES.vs[v]["out"]
        if not out:
            continue

        events = {l for e in out for l in e[1].label}

        # max control decision is something like the union of the defined control decisions
        q2_e_generator = (
            o for n in AES._graph.neighbors(v, mode="OUT") for o in AES.vs[n]["out"]
        )

        used_events = set()

        for q2_e in q2_e_generator:
            if q2_e[1] in AES.Euo or q2_e[1] in used_events:
                continue
            used_events.add(q2_e[1])
            # Jack: I might be assuming that the exists() clause in line 7 is trivial
            next_v = q2_e[0]

            if next_v not in states.keys():
                states[next_v] = len(states)
                queue.append(next_v)

            trans.append((states[v], states[next_v]))
            trans_labels.append(q2_e[1])

        unused_events = events - used_events
        for e in unused_events:
            # self-loops for all remaining events in control decision
            trans.append((states[v], states[v]))
            trans_labels.append(e)

    sup = DFA()
    sup.add_vertices(len(states))
    sup.add_edges(trans, trans_labels)

    sup.events = AES.events.copy()
    return sup
