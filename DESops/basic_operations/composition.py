"""
Funcions relevant to the composition operations.
"""
from collections import deque
from typing import Set, Tuple, TypeVar

import pydash

from DESops.automata.automata import _Automata
from DESops.automata.DFA import DFA
from DESops.automata.event.event import Event
from DESops.automata.NFA import NFA
from DESops.basic_operations.unary import find_inacc
from DESops.error import IncongruencyError, MissingAttributeError

EventSet = Set[Event]
DFA_NFA = TypeVar("DFA_NFA", DFA, NFA)


def product(*automata: _Automata) -> _Automata:
    """
    Computes the product composition of 2 (or more) Automata, and returns the resulting composition as a new Automata.
    """
    if len(automata) < 2:
        raise MissingAttributeError("More than one automaton are needed.")

    G1 = automata[0]
    input_list = automata[1:]

    for G2 in input_list:
        G_out = _Automata()
        Euc = G1.Euc | G2.Euc
        Euo = G1.Euo | G2.Euo

        vertices = [
            {
                "name": (x1["name"], x2["name"]),
                "marked": x1["marked"] is True and x2["marked"] is True,
                "indexes": (x1.index, x2.index),
            }
            for x1 in G1.vs
            for x2 in G2.vs
        ]
        G_out.add_vertices(
            len(vertices),
            names=[v["name"] for v in vertices],
            marked=[v["marked"] for v in vertices],
            indexes=[v["indexes"] for v in vertices],
        )

        for x in G_out.vs:
            x1 = G1.vs[x["indexes"][0]]
            x2 = G2.vs[x["indexes"][1]]
            active_events = {out[1] for out in x1["out"]} & {
                out[1] for out in x2["out"]
            }
            if not active_events:
                continue

            for e in active_events:
                if e in Euc:
                    G_out.Euc.add(e)
                if e in Euo:
                    G_out.Euo.add(e)

                x1_outs = {G1.vs[out[0]] for out in x1["out"] if out[1] == e}
                x2_outs = {G2.vs[out[0]] for out in x2["out"] if out[1] == e}
                edges = [
                    {
                        "pair": (
                            x.index,
                            G_out.vs.select(indexes_eq=(x1_dst.index, x2_dst.index))[
                                0
                            ].index,
                        ),
                        "label": e,
                    }
                    for x1_dst in x1_outs
                    for x2_dst in x2_outs
                ]
                G_out.add_edges(
                    [edge["pair"] for edge in edges],
                    [edge["label"] for edge in edges],
                    fill_out=True,
                )

        bad_states = find_inacc(G_out)
        G_out.delete_vertices(list(bad_states))
        G1 = G_out

    del G_out.vs["indexes"]

    return G_out


def parallel(*automata: _Automata) -> _Automata:
    """
    Computes the parallel composition of 2 (or more) Automata, and returns the resulting composition as a new Automata.
    """
    if len(automata) < 2:
        raise MissingAttributeError("More than one automaton are needed.")

    G1 = automata[0]
    input_list = automata[1:]

    for G2 in input_list:
        G_out = _Automata()
        Euc = G1.Euc | G2.Euc
        Euo = G1.Euo | G2.Euo
        E1 = set(G1.es["label"])
        E2 = set(G2.es["label"])

        vertices = [
            {
                "name": (x1["name"], x2["name"]),
                "marked": x1["marked"] is True and x2["marked"] is True,
                "indexes": (x1.index, x2.index),
            }
            for x1 in G1.vs
            for x2 in G2.vs
        ]
        G_out.add_vertices(
            len(vertices),
            names=[v["name"] for v in vertices],
            marked=[v["marked"] for v in vertices],
            indexes=[v["indexes"] for v in vertices],
        )

        for x in G_out.vs:
            x1 = G1.vs[x["indexes"][0]]
            x2 = G2.vs[x["indexes"][1]]
            active_x1 = {out[1] for out in x1["out"]}
            active_x2 = {out[1] for out in x2["out"]}
            active_both = active_x1 & active_x2
            x1_ex = active_x1 - E2
            x2_ex = active_x2 - E1
            if not active_both and not x1_ex and not x2_ex:
                continue

            for e in active_x1 | active_x2:
                if e in Euc:
                    G_out.Euc.add(e)
                if e in Euo:
                    G_out.Euo.add(e)

            for e in active_both:
                x1_outs = {G1.vs[out[0]] for out in x1["out"] if out[1] == e}
                x2_outs = {G2.vs[out[0]] for out in x2["out"] if out[1] == e}
                edges = [
                    {
                        "pair": (
                            x.index,
                            G_out.vs.select(indexes_eq=(x1_dst.index, x2_dst.index))[
                                0
                            ].index,
                        ),
                        "label": e,
                    }
                    for x1_dst in x1_outs
                    for x2_dst in x2_outs
                ]
                G_out.add_edges(
                    [edge["pair"] for edge in edges],
                    [edge["label"] for edge in edges],
                    fill_out=True,
                )

            for e in x1_ex:
                x1_outs = {G1.vs[out[0]] for out in x1["out"] if out[1] == e}
                edges = [
                    {
                        "pair": (
                            x.index,
                            G_out.vs.select(indexes_eq=(x1_dst.index, x2.index))[
                                0
                            ].index,
                        ),
                        "label": e,
                    }
                    for x1_dst in x1_outs
                ]
                G_out.add_edges(
                    [edge["pair"] for edge in edges],
                    [edge["label"] for edge in edges],
                    fill_out=True,
                )

            for e in x2_ex:
                x2_outs = {G2.vs[out[0]] for out in x2["out"] if out[1] == e}
                edges = [
                    {
                        "pair": (
                            x.index,
                            G_out.vs.select(indexes_eq=(x1.index, x2_dst.index))[
                                0
                            ].index,
                        ),
                        "label": e,
                    }
                    for x2_dst in x2_outs
                ]
                G_out.add_edges(
                    [edge["pair"] for edge in edges],
                    [edge["label"] for edge in edges],
                    fill_out=True,
                )

        bad_states = find_inacc(G_out)
        G_out.delete_vertices(list(bad_states))
        G1 = G_out

    del G_out.vs["indexes"]

    return G_out


def observer(G: DFA_NFA) -> DFA:
    """
    Constructs an observer of the given automata..
    """
    G_obs = DFA()
    X_m = {state.index for state in G.vs if state["marked"] is True}
    E = set(G.es["label"])
    Eo = E - G.Euo
    G_obs.Euc = G.Euc
    G_obs.Euo = G.Euo

    x0_obs = G.unobservable_reach(0)
    G_obs.add_vertex(
        name=tuple(G.vs[x_e]["name"] for x_e in x0_obs), marked=False, indexes=x0_obs
    )

    B_queue = deque([x0_obs])

    while len(B_queue) > 0:
        B = B_queue.popleft()
        src_vertex = pydash.arrays.find_index(G_obs.vs["indexes"], lambda i: i == B)
        for e in Eo:
            destinations = {
                out[0] for x_e in B for out in G.vs[x_e]["out"] if out[1] == e
            }
            if len(destinations) == 0:
                continue

            u_reaches = G.unobservable_reach(destinations)
            index = pydash.arrays.find_index(
                G_obs.vs["indexes"], lambda i: i == u_reaches
            )
            if index != -1:
                G_obs.add_edge(src_vertex, index, e, fill_out=True)
            else:
                dst_vertex = G_obs.add_vertex(
                    name=tuple(G.vs[i]["name"] for i in u_reaches),
                    marked=False,
                    indexes=u_reaches,
                )
                G_obs.add_edge(src_vertex, dst_vertex.index, e, fill_out=True)
                B_queue.append(u_reaches)

    for state in G_obs.vs:
        if len(state["indexes"] & X_m) > 0:
            G_obs.vs[state.index].update_attributes({"marked": True})

    del G_obs.vs["indexes"]

    return G_obs


def strict_subautomata(H: DFA, G: DFA) -> Tuple[DFA]:
    """
    Constructs language-equivalent automata G_tilde and H_tilde from given G and H such that H_tilde is a strict subautomaton of G_tilde.
    """
    A = H.copy()

    # Step 1:
    #   Adding a new unmarked state "dead"
    dead = A.add_vertex(name="dead", marked=False)

    #   Completing the transition function of A
    all_events = set(H.es["label"]) | set(G.es["label"])
    for x in H.vs:
        active_events = {out[1] for out in H.vs[x.index]["out"]}
        non_active_events = all_events - active_events
        edges_to_dead = [
            {"pair": (x.index, dead.index), "label": event}
            for event in non_active_events
        ]
        A.add_edges(
            [edge["pair"] for edge in edges_to_dead],
            [edge["label"] for edge in edges_to_dead],
            fill_out=True,
        )

    dead_selfloops = [
        {"pair": (dead.index, dead.index), "label": event} for event in all_events
    ]
    A.add_edges(
        [edge["pair"] for edge in dead_selfloops],
        [edge["label"] for edge in dead_selfloops],
        fill_out=True,
    )

    # Step 2: Calculating the product automaton AG = A x G
    AG = product(A, G)

    # Step 3:
    #   Step 3.1: Obtaining G_tilde
    G_tilde = AG.copy()  # Taking AG
    for state in G_tilde.vs:
        name = state["name"][1]
        state_in_G = G.vs.select(name_eq=name)
        if len(state_in_G) > 1:
            raise IncongruencyError(
                'More than one state have the same name "{}" in G'.format(name)
            )
        state_in_G = state_in_G[0]
        # A state of G_tilde is marked if and only if its second state component is marked in G
        if state_in_G["marked"]:
            G_tilde.vs[state.index].update_attributes({"marked": True})
        else:
            G_tilde.vs[state.index].update_attributes({"marked": False})

    #   Step 3.2: Obtaining H_tilde by deleting all state of AG where the first state component is "dead".
    H_tilde = AG.copy()
    dead_states = [state for state in H_tilde.vs if state["name"][0] == "dead"]
    H_tilde.delete_vertices(dead_states)
    for state in H_tilde.vs:
        name = state["name"][0]
        state_in_H = H.vs.select(name_eq=name)
        if len(state_in_H) > 1:
            raise IncongruencyError(
                'More than one state have the same name "{}" in H'.format(name)
            )
        state_in_H = state_in_H[0]
        # A state of H_tilde is marked if and only if its first state component is marked in H
        if state_in_H["marked"]:
            H_tilde.vs[state.index].update_attributes({"marked": True})
        else:
            H_tilde.vs[state.index].update_attributes({"marked": False})

    return H_tilde, G_tilde
