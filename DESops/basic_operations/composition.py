"""
Funcions relevant to the composition operations.
"""
from collections import deque
from typing import Optional, Set, TypeVar

import pydash

from DESops.automata.automata import _Automata
from DESops.automata.automata_ctor import construct_automata
from DESops.automata.DFA import DFA
from DESops.automata.event.event import Event
from DESops.automata.NFA import NFA
from DESops.basic_operations.unary import find_inacc
from DESops.error import MissingAttributeError

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
    G_obs = DFA()
    X_m = {state.index for state in G.vs if state["marked"] is True}
    E = set(G.es["label"])
    Eo = E - G.Euo

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
