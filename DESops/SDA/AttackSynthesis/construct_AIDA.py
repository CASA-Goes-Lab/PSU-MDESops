import itertools
import os
import subprocess
import time

import igraph as ig

from DESops.automata.DFA import DFA
from DESops.automata.event import Event
from DESops.SDA.event_extensions import deleted_event, inserted_event


# Construct-AIDA algorithm
# Requires system G, supervisor Rt (~R), and set of events vulnerable to attacks Ea
# Returns an AIDA-structure graph
# dead_state is the index in h
# Also optionally requires controllable/observable event sets Euc/Euo
def construct_AIDA(G, R, Ea, X_crit):

    A = DFA()
    Eo = G.events - G.Euo
    # getting vertices of X_crit
    X_crit_vs = G.vs.select(name_in=X_crit)

    dead_vs = len(R.vs) - 1
    # print(dead_vs)
    X_crit_vs = [v.index for v in X_crit_vs]
    # Q1 and Q2 states map name to vertex index for BTS and set of vertex indices of G; init state is 0
    Q1, Q2 = dict(), dict()
    Qname, Qcrit, Qdead = list(), list(), list()
    # holds the names of each state in order of their vertex index
    # transitions for igraph constructed using vertex index
    h1, h2 = list(), list()
    Gamma = set()
    # transitions labels map labels to transitions h1, h2
    labelh1, labelh2 = list(), list()
    Q1[(frozenset({0}), 0, 1)] = 0
    queue = list()
    Qname.append((setvs2statename(G, {0}), R.vs["name"][0], "1"))
    Qcrit.append(0)
    Qdead.append(0)
    queue.append((frozenset({0}), 0, 1))
    UR_state_classes = dict()
    while queue:
        (Gvs, Rvs, p) = queue.pop(0)
        # If Q1 (Supervisor player)
        if p == 1:
            gamma = {e for (target, e) in R.vs["out"][Rvs]}
            ev = Event(gamma)
            Gamma.add(ev)
            """
            if (Gvs, frozenset(G.Euo.intersection(gamma))) not in UR_state_classes:
                next_Gvs = frozenset(
                    ureach_from_set_adj(Gvs, G._graph, G.Euo.intersection(gamma))
                )
                UR_state_classes[(Gvs, frozenset(G.Euo.intersection(gamma)))] = next_Gvs
            else:
                next_Gvs = UR_state_classes[(Gvs, frozenset(G.Euo.intersection(gamma)))]
            """
            next_Gvs = G.UR.from_set(Gvs, G.Euo.intersection(gamma), freeze_result=True)
            q2 = (next_Gvs, Rvs, 2)
            q2name = (setvs2statename(G, next_Gvs), R.vs["name"][Rvs], "2")
            if q2 not in Q2:
                Q2[q2] = len(Qname)
                Qname.append(q2name)
                Qdead.append(0)
                if next_Gvs.issubset(X_crit):
                    Qcrit.append(1)
                elif next_Gvs.intersection(X_crit):
                    queue.append(q2)
                    Qcrit.append(1)
                else:
                    queue.append(q2)
                    Qcrit.append(0)
            h1.append((Q1[(Gvs, Rvs, p)], Q2[q2]))
            labelh1.append(ev)

        else:
            gamma = {e: target for (target, e) in R.vs["out"][Rvs] if e not in G.Euo}
            # active = {e for (target,e) in G.vs["out"][Gvs]}
            for e in gamma.keys():
                if e in Ea:
                    next_Gvs = frozenset(
                        {
                            target
                            for v in Gvs
                            for (target, ev) in G.vs["out"][v]
                            if ev == e
                        }
                    )
                    next_Rvs = gamma[e]
                    if next_Gvs:
                        q1l = (next_Gvs, next_Rvs, 1)
                        q1d = (next_Gvs, Rvs, 1)
                        q1name = (
                            setvs2statename(G, next_Gvs),
                            R.vs["name"][next_Rvs],
                            "1",
                        )
                        q1dname = (setvs2statename(G, next_Gvs), R.vs["name"][Rvs], "1")
                        if q1l not in Q1:
                            Q1[q1l] = len(Qname)
                            Qname.append(q1name)
                            if next_Gvs.issubset(X_crit):
                                Qcrit.append(1)
                                Qdead.append(0)
                            elif next_Rvs == dead_vs:
                                Qdead.append(1)
                                Qcrit.append(0)
                            elif next_Gvs.intersection(X_crit):
                                Qdead.append(0)
                                queue.append(q1l)
                                Qcrit.append(1)
                            else:
                                Qdead.append(0)
                                queue.append(q1l)
                                Qcrit.append(0)
                        h2.append((Q2[(Gvs, Rvs, p)], Q1[q1l]))
                        labelh2.append(e)
                        if q1d not in Q1:
                            Q1[q1d] = len(Qname)
                            Qname.append(q1dname)
                            Qdead.append(0)
                            if next_Gvs.issubset(X_crit):
                                Qcrit.append(1)
                            elif next_Gvs.intersection(X_crit):
                                queue.append(q1d)
                                Qcrit.append(1)
                            else:
                                queue.append(q1d)
                                Qcrit.append(0)
                        h2.append((Q2[(Gvs, Rvs, p)], Q1[q1d]))
                        # labelh2.append(Event("".join([e.name(), "_del"])))
                        labelh2.append(deleted_event(e))
                    q1i = (Gvs, next_Rvs, 1)
                    q1name = (setvs2statename(G, Gvs), R.vs["name"][next_Rvs], "1")
                    if q1i not in Q1:
                        Q1[q1i] = len(Qname)
                        Qname.append(q1name)
                        if next_Gvs.issubset(X_crit):
                            Qcrit.append(1)
                            Qdead.append(0)
                        elif next_Rvs == dead_vs:
                            Qdead.append(1)
                            Qcrit.append(0)
                        elif next_Gvs.intersection(X_crit):
                            queue.append(q1i)
                            Qcrit.append(1)
                            Qdead.append(0)
                        else:
                            queue.append(q1i)
                            Qcrit.append(0)
                            Qdead.append(0)
                    h2.append((Q2[(Gvs, Rvs, p)], Q1[q1i]))
                    # labelh2.append(Event("".join([e.name(), "_ins"])))
                    labelh2.append(inserted_event(e))
                else:
                    next_Gvs = frozenset(
                        {
                            target
                            for v in Gvs
                            for (target, ev) in G.vs["out"][v]
                            if e == ev
                        }
                    )
                    next_Rvs = gamma[e]
                    if next_Gvs:
                        q1l = (next_Gvs, next_Rvs, 1)
                        q1name = (
                            setvs2statename(G, next_Gvs),
                            R.vs["name"][next_Rvs],
                            "1",
                        )
                        if q1l not in Q1:
                            Q1[q1l] = len(Qname)
                            Qname.append(q1name)
                            if next_Gvs.issubset(X_crit):
                                Qcrit.append(1)
                                Qdead.append(0)
                            elif next_Rvs == dead_vs:
                                Qdead.append(1)
                                Qcrit.append(0)
                            elif next_Gvs.intersection(X_crit):
                                queue.append(q1l)
                                Qcrit.append(1)
                                Qdead.append(0)
                            else:
                                queue.append(q1l)
                                Qcrit.append(0)
                                Qdead.append(0)
                        h2.append((Q2[(Gvs, Rvs, p)], Q1[q1l]))
                        labelh2.append(e)
    if Qname:
        A.add_vertices(len(Qname), Qname)
        A.vs["crit"] = Qcrit
        A.vs["dead"] = Qdead
        A.add_edges(h1, labelh1)
        A.add_edges(h2, labelh2)

    A.events = G.events.copy()
    A.events = A.events.union(Gamma)
    ins = {inserted_event(e) for e in Ea}

    dele = {deleted_event(e) for e in Ea}

    A.events = A.events.union(ins)
    A.events = A.events.union(dele)
    A.Euc.update(G.events.copy() - Ea)
    A.Euc.update(A.Euc.union(Gamma))
    A.generate_out()
    return A


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
