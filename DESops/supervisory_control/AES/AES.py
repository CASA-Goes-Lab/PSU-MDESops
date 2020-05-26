import itertools
import os
import subprocess

import igraph as ig

from DESops.automata.DFA import DFA
from DESops.automata.event.event import Event
from DESops.basic_operations.ureach import ureach_from_set_adj


def construct_compact_AES(G, X_crit, debug=False):
    # arena: igraph graph object where resulting arena will be stored, assumed to be empty
    # G: input system automata
    # X_crit: safety specification based on name of the states
    # debug:   True: print updates for states & time to construct arena
    #          False: no debug information
    #          default: False
    if debug:
        import time

        start_time = time.process_time()

    # getting vertices of X_crit
    X_crit = G.vs.select(name_in=X_crit)
    X_crit = [v.index for v in X_crit]
    # Q1 and Q2 states map name to vertex index for BTS and set of vertex indices of G; init state is 0
    Q1, Q2 = dict(), dict()
    Qname = list()  # holds the names of each state in order of their vertex index
    # transitions for igraph constructed using vertex index
    h1, h2 = list(), list()
    # transitions labels map labels to transitions h1, h2
    labelh1, labelh2 = list(), list()
    Q1[frozenset({0})] = 0
    queue = list()
    Qname.append(setvs2statename(G, {0}))
    queue.append({0})
    construct_Tcomp(G, Qname, Q1, Q2, h1, h2, labelh1, labelh2, queue, X_crit)
    A = DFA()
    A.add_vertices(len(Qname), Qname)
    A.add_edges(h1, labelh1)
    A.add_edges(h2, labelh2)

    return A


def construct_AES(G, X_crit, debug=False):
    # arena: igraph graph object where resulting arena will be stored, assumed to be empty
    # G: input system automata
    # X_crit: safety specification based on name of the states
    # debug:   True: print updates for states & time to construct arena
    #          False: no debug information
    #          default: False
    if debug:
        import time

        start_time = time.process_time()

    # getting vertices of X_crit
    X_crit = G.vs.select(name_in=X_crit)
    X_crit = [v.index for v in X_crit]
    # Q1 and Q2 states map name to vertex index for BTS and set of vertex indices of G; init state is 0
    Q1, Q2 = dict(), dict()
    Qname = list()  # holds the names of each state in order of their vertex index
    # transitions for igraph constructed using vertex index
    h1, h2 = list(), list()
    # transitions labels map labels to transitions h1, h2
    labelh1, labelh2 = list(), list()
    Q1[frozenset({0})] = 0
    queue = list()
    Qname.append(setvs2statename(G, {0}))
    queue.append({0})
    construct_Tmax(G, Qname, Q1, Q2, h1, h2, labelh1, labelh2, queue, X_crit)
    A = DFA()
    A.add_vertices(len(Qname), Qname)
    A.add_edges(h1, labelh1)
    A.add_edges(h2, labelh2)

    return A

    # print(queue)


def construct_Tcomp(G, Qname, Q1, Q2, h1, h2, labelh1, labelh2, queue, X_crit):
    # index counter saves the current vertex index
    vertex_counter = 1
    Eo = G.events - G.Euo
    UR_state_classes = dict()
    Gamma = find_compact_control_decisions_sets(G.events, G.Euc, G.Euo)
    # print(Gamma)
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
                print(nxstates)
                if nxstates:
                    vertex_counter = Q1_add_state(
                        nxstates,
                        Q2[(frozenset(q[0]), frozenset(q[1]))],
                        e,
                        G,
                        Qname,
                        Q1,
                        h2,
                        labelh2,
                        queue,
                        vertex_counter,
                        X_crit,
                    )
    print(Qname)
    print(h1)


def construct_Tmax(G, Qname, Q1, Q2, h1, h2, labelh1, labelh2, queue, X_crit):
    # index counter saves the current vertex index
    vertex_counter = 1
    Eo = G.events - G.Euo
    UR_state_classes = dict()
    Gamma = find_control_decisions_sets(G.events, G.Euc)
    # print(Gamma)
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
                print(nxstates)
                if nxstates:
                    vertex_counter = Q1_add_state(
                        nxstates,
                        Q2[(frozenset(q[0]), frozenset(q[1]))],
                        e,
                        G,
                        Qname,
                        Q1,
                        h2,
                        labelh2,
                        queue,
                        vertex_counter,
                        X_crit,
                    )
    print(Qname)
    print(h1)


def Q1_add_state(q1, q2, ev, G, Qname, Q1, h2, labelh2, queue, v_counter, X_crit):
    if not Q1.get(frozenset(q1)):
        Q1[frozenset(q1)] = v_counter
        v = v_counter
        # If there is not any critical state in q1 state estimate then add to queue
        if not q1.intersection(X_crit):
            queue.append(q1)
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


def Q2_add_state(q1, q2, G, Qname, Q2, h1, labelh1, queue, v_counter, X_crit):
    if not Q2.get((frozenset(q2[0]), frozenset(q2[1]))):
        Q2[(frozenset(q2[0]), frozenset(q2[1]))] = v_counter
        v = v_counter
        # If there is not any critical state in q2 state estimate then add to queue
        if not q2[0].intersection(X_crit):
            queue.append(q2)
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


def Q1_state(q):
    return isinstance(q, set)


def Q2_state(q):
    return isinstance(q, tuple)


def find_compact_control_decisions_sets(E, Euc, Euo):
    Ec = set(E - Euc)
    Ecuo = list(Ec.intersection(Euo))
    Eco = list(Ec.intersection(E - Euo))
    GammaEcuo = list()
    for l in range(len(Ec) + 1):
        GammaEcuo.extend([Euc.union(comb) for comb in itertools.combinations(Ecuo, l)])
    Gamma = list()
    for e in Eco:
        Gamma.extend([gamma.union({e}) for gamma in GammaEcuo])
    Gamma.extend(GammaEcuo)
    print(Gamma)
    return Gamma


def find_control_decisions_sets(E, Euc):
    Ec = list(E - Euc)
    print(Ec)
    Gamma = list()
    for l in range(len(Ec) + 1):
        Gamma.extend([Euc.union(comb) for comb in itertools.combinations(Ec, l)])
    return Gamma


def cd2ev(ct):
    ev = Event()
    return ev


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
