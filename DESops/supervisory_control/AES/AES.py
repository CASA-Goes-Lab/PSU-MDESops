import itertools
import os
import subprocess
import time

import igraph as ig

from DESops.automata.DFA import DFA
from DESops.automata.event.event import Event
from DESops.basic_operations.ureach import ureach_from_set_adj
from DESops.supervisory_control import supr_contr


def construct_AES(G, X_crit, compact=False):
    # arena: igraph graph object where resulting arena will be stored, assumed to be empty
    # G: input system automata
    # X_crit: safety specification based on name of the states

    # Computing the control decision set
    Eo = G.events - G.Euo
    if compact:
        # Finding the compact control decision set
        Gamma = find_compact_control_decisions_sets(G.events, G.Euc, G.Euo)
    else:
        Gamma = find_control_decisions_sets(G.events, G.Euc)

    # getting vertices of X_crit
    X_crit_vs = G.vs.select(name_in=X_crit)
    X_crit_vs = [v.index for v in X_crit_vs]
    # Q1 and Q2 states map name to vertex index for BTS and set of vertex indices of G; init state is 0
    Q1, Q2 = dict(), dict()
    Qname, Qcrit = (
        list(),
        list(),
    )  # holds the names of each state in order of their vertex index
    # transitions for igraph constructed using vertex index
    h1, h2 = list(), list()

    # transitions labels map labels to transitions h1, h2
    labelh1, labelh2 = list(), list()
    Q1[frozenset({0})] = 0
    queue = list()
    Qname.append(setvs2statename(G, {0}))
    Qcrit.append(0)
    queue.append({0})

    # constructs the BTS in a BFS manner based on Gamma
    start_time = time.process_time()
    A = construct_T(
        G, Qname, Qcrit, Q1, Q2, h1, h2, labelh1, labelh2, queue, X_crit_vs, Gamma
    )
    print(time.process_time() - start_time)
    # Pruning the BTS: (1) find states that violate X_crit (2) supremal controllable

    # Find states that violate X_crit
    M = find_violation(A)

    # Construct specification. This spec is already a strict subautomaton of A
    Atrim = DFA(A)
    Atrim.delete_vertices(M)

    # Finding supcon based on A and Atrim
    start_time = time.process_time()
    AES = supr_contr.supr_contr(A, Atrim, mark_states=False, preprocess=False)
    print(time.process_time() - start_time)

    return A


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

    # index counter saves the current vertex index
    vertex_counter = 1

    Eo = G.events - G.Euo

    # used to not recompute UR
    UR_state_classes = dict()

    # queue holds states that must be visited
    while queue:
        q = queue.pop(0)
        if Q1_state(q):
            qvs = q
            for gamma in Gamma:
                if not UR_state_classes.get(
                    (frozenset(qvs), frozenset(G.Euo.intersection(gamma)))
                ):
                    q2_state = ureach_from_set_adj(
                        qvs, G._graph, G.Euo.intersection(gamma)
                    )
                    UR_state_classes[
                        (frozenset(qvs), frozenset(G.Euo.intersection(gamma)))
                    ] = q2_state
                # print(setvs2statename(G,q2_state))
                else:
                    q2_state = UR_state_classes[
                        (frozenset(qvs), frozenset(G.Euo.intersection(gamma)))
                    ]
                q2 = (q2_state, gamma)
                vertex_counter = Q2_add_state(
                    Q1[frozenset(q)],
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
                )

        if Q2_state(q):
            gamma = q[1]
            states = q[0]
            # print(gamma,Eo.intersection(gamma))
            for e in Eo.intersection(gamma):
                nxstates = {v[0] for i in states for v in G.vs["out"][i] if v[1] == e}
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
                    )

    # Creating BTS as DFA

    A = DFA()
    A.add_vertices(len(Qname), Qname)
    A.vs["crit"] = Qcrit
    A.add_edges(h1, labelh1)
    A.add_edges(h2, labelh2)

    Ev = generate_ev_uc(Gamma, G.Euc)
    # print(Ev[0], Ev[1])

    A.events = G.events.copy()
    A.events = A.events.union(Ev[0])
    A.Euc = G.events.copy()
    A.Euc.add(Ev[1])
    A.generate_out()

    return A


def find_violation(A):
    return [v.index for v in A.vs.select(crit_eq=1)]


def generate_ev_uc(Gamma, Euc):
    E = set()
    for ctr in Gamma:
        if ctr == Euc:
            ev = Event(ctr2str(ctr))
        E.add(Event(ctr2str(ctr)))
    return (E, ev)


# Adds Q1 state to lists
def Q1_add_state(
    q1, q2, ev, G, Qname, Qcrit, Q1, h2, labelh2, queue, v_counter, X_crit
):
    if not Q1.get(frozenset(q1)):
        Q1[frozenset(q1)] = v_counter
        v = v_counter
        # If there is not any critical state in q1 state estimate then add to queue
        if not q1.intersection(X_crit):
            queue.append(q1)
            Qcrit.insert(v, 0)
        else:
            Qcrit.insert(v, 1)

        q1name = setvs2statename(G, q1)
        # print(q1name)
        Qname.insert(v, q1name)
        v_counter += 1

    else:
        v = Q1[frozenset(q1)]
    h2.append((q2, v))
    # print(ctr2str(gamma))
    labelh2.append(ev)
    return v_counter


# Adds Q2 state to lists
def Q2_add_state(q1, q2, G, Qname, Qcrit, Q2, h1, labelh1, queue, v_counter, X_crit):
    if not Q2.get((frozenset(q2[0]), frozenset(q2[1]))):
        Q2[(frozenset(q2[0]), frozenset(q2[1]))] = v_counter
        v = v_counter
        # If there is not any critical state in q2 state estimate then add to queue
        if not q2[0].intersection(X_crit):
            queue.append(q2)
            Qcrit.insert(v, 0)
        else:
            Qcrit.insert(v, 1)
        q2name = ",".join([setvs2statename(G, q2[0]), ctr2str(q2[1])])
        # print(q2name)
        Qname.insert(v, "".join(["(", q2name, ")"]))
        v_counter += 1
    else:
        v = Q2[(frozenset(q2[0]), frozenset(q2[1]))]
    h1.append((q1, v))
    # print(ctr2str(gamma))
    labelh1.append(Event(ctr2str(q2[1])))
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
    GammaEcuo = list()
    for l in range(len(Ec) + 1):
        GammaEcuo.extend([Euc.union(comb) for comb in itertools.combinations(Ecuo, l)])
    Gamma = list()
    for e in Eco:
        Gamma.extend([gamma.union({e}) for gamma in GammaEcuo])
    Gamma.extend(GammaEcuo)
    # print(Gamma)
    return Gamma


# Finds all possible control decisions
def find_control_decisions_sets(E, Euc):
    Ec = list(E - Euc)
    # print(Ec)
    Gamma = list()
    for l in range(len(Ec) + 1):
        Gamma.extend([Euc.union(comb) for comb in itertools.combinations(Ec, l)])
    return Gamma


# Transforms a control decision to string
def ctr2str(gamma):
    name = str()
    first = True
    for e in gamma:
        if first:
            name = "".join(["{", e.label])
            first = False
        else:
            name = ",".join([name, e.label])
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
