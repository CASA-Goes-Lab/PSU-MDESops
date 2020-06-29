"""
Funcions relevant to the composition operations.
"""
from collections import deque
from typing import Dict, List, Optional, Set, Tuple, Union

import pydash
from joblib import Parallel, delayed
from tqdm import tqdm

from DESops.automata.automata import _Automata
from DESops.automata.DFA import DFA
from DESops.automata.event.event import Event
from DESops.automata.NFA import NFA
from DESops.basic_operations.product_comp import product_comp
from DESops.basic_operations.unary import find_inacc
from DESops.error import IncongruencyError, MissingAttributeError

EventSet = Set[Event]
Automata_t = Union[DFA, NFA]
PARALLEL_VERBOSE_LEVEL = 0
PARALLEL_MODE = False
PARALLEL_PREFER = None
SHOW_PROGRESS = False


def product(*automata: Automata_t) -> Automata_t:
    """
    Computes the product composition of 2 (or more) Automata, and returns the resulting composition as a new Automata.
    """
    if len(automata) < 2:
        raise MissingAttributeError("More than one automaton are needed.")

    G1 = automata[0]
    input_list = automata[1:]

    for G2 in tqdm(
        input_list, desc="Product Composition", disable=SHOW_PROGRESS is False
    ):
        G_out = _Automata()

        num_G2_states = len(G2.vs)
        G_out_vertices = [
            {
                "index": i * num_G2_states + j,
                "name": (x1["name"], x2["name"]),
                "marked": x1["marked"] is True and x2["marked"] is True,
                "indexes": (x1.index, x2.index),
            }
            for i, x1 in enumerate(G1.vs)
            for j, x2 in enumerate(G2.vs)
        ]
        G_out.add_vertices(
            len(G_out_vertices),
            names=[v["name"] for v in G_out_vertices],
            marked=[v["marked"] for v in G_out_vertices],
            indexes=[v["indexes"] for v in G_out_vertices],
        )
        G1_vertices = [
            {
                "index": x.index,
                "name": x["name"],
                "marked": x["marked"],
                "out": x["out"],
            }
            for x in G1.vs
        ]
        G2_vertices = [
            {
                "index": x.index,
                "name": x["name"],
                "marked": x["marked"],
                "out": x["out"],
            }
            for x in G2.vs
        ]
        indexes_dict = {
            v: i for i, v in enumerate([v["indexes"] for v in G_out_vertices])
        }

        edges = []
        if PARALLEL_MODE:
            results = Parallel(
                n_jobs=-1, verbose=PARALLEL_VERBOSE_LEVEL, prefer=PARALLEL_PREFER
            )(
                delayed(__find_product_edges_at_state)(
                    x, G1_vertices, G2_vertices, indexes_dict
                )
                for x in G_out_vertices
            )
            for result in results:
                if result is not None:
                    edges.extend(result)
        else:
            for x in tqdm(
                G_out_vertices,
                desc="Processing states",
                unit="states",
                leave=False,
                disable=SHOW_PROGRESS is False,
            ):
                new_edges = __find_product_edges_at_state(
                    x, G1_vertices, G2_vertices, indexes_dict
                )
                if new_edges is not None:
                    edges.extend(new_edges)

        G_out.add_edges(
            [edge["pair"] for edge in edges],
            [edge["label"] for edge in edges],
            fill_out=True,
        )

        bad_states = find_inacc(G_out)
        G_out.delete_vertices(list(bad_states))
        G1 = G_out

    del G_out.vs["indexes"]
    G_out.Euc = pydash.reduce_(automata, lambda euc, g: euc | g.Euc, set()) & set(
        G_out.es["label"]
    )
    G_out.Euo = pydash.reduce_(automata, lambda euo, g: euo | g.Euo, set()) & set(
        G_out.es["label"]
    )

    return G_out


def __find_product_edges_at_state(
    x: dict,
    G1_vertices: List[dict],
    G2_vertices: List[dict],
    G_out_index_dict: Dict[tuple, int],
) -> Optional[List[dict]]:
    x1 = G1_vertices[x["indexes"][0]]
    x2 = G2_vertices[x["indexes"][1]]
    active_events = {out[1] for out in x1["out"]} & {out[1] for out in x2["out"]}
    if not active_events:
        None

    edges = []
    for e in active_events:
        x1_outs = [G1_vertices[out[0]] for out in x1["out"] if out[1] == e]
        x2_outs = [G2_vertices[out[0]] for out in x2["out"] if out[1] == e]
        new_edges = [
            {
                "pair": (
                    x["index"],
                    G_out_index_dict[(x1_dst["index"], x2_dst["index"])],
                ),
                "label": e,
            }
            for x1_dst in x1_outs
            for x2_dst in x2_outs
        ]
        edges.extend(new_edges)

    return edges


def parallel(*automata: Automata_t) -> Automata_t:
    """
    Computes the parallel composition of 2 (or more) Automata, and returns the resulting composition as a new Automata.
    """
    if len(automata) < 2:
        raise MissingAttributeError("More than one automaton are needed.")

    G1 = automata[0]
    input_list = automata[1:]

    for G2 in tqdm(
        input_list, desc="Parallel Composition", disable=SHOW_PROGRESS is False
    ):
        G_out = _Automata()
        E1 = set(G1.es["label"])
        E2 = set(G2.es["label"])

        num_G2_states = len(G2.vs)
        G_out_vertices = [
            {
                "index": i * num_G2_states + j,
                "name": (x1["name"], x2["name"]),
                "marked": x1["marked"] is True and x2["marked"] is True,
                "indexes": (x1.index, x2.index),
            }
            for i, x1 in enumerate(G1.vs)
            for j, x2 in enumerate(G2.vs)
        ]
        G_out.add_vertices(
            len(G_out_vertices),
            names=[v["name"] for v in G_out_vertices],
            marked=[v["marked"] for v in G_out_vertices],
            indexes=[v["indexes"] for v in G_out_vertices],
        )
        G1_vertices = [
            {
                "index": x.index,
                "name": x["name"],
                "marked": x["marked"],
                "out": x["out"],
            }
            for x in G1.vs
        ]
        G2_vertices = [
            {
                "index": x.index,
                "name": x["name"],
                "marked": x["marked"],
                "out": x["out"],
            }
            for x in G2.vs
        ]
        indexes_dict = {
            v: i for i, v in enumerate([v["indexes"] for v in G_out_vertices])
        }

        edges = []
        if PARALLEL_MODE:
            results = Parallel(
                n_jobs=-1, verbose=PARALLEL_VERBOSE_LEVEL, prefer=PARALLEL_PREFER
            )(
                delayed(__find_parallel_edges_at_states)(
                    x, G1_vertices, G2_vertices, E1, E2, indexes_dict
                )
                for x in G_out_vertices
            )
            for result in results:
                if result is not None:
                    edges.extend(result)
        else:
            for x in tqdm(
                G_out_vertices,
                desc="Processing states",
                unit="states",
                leave=False,
                disable=SHOW_PROGRESS is False,
            ):
                new_edges = __find_parallel_edges_at_states(
                    x, G1_vertices, G2_vertices, E1, E2, indexes_dict
                )
                if new_edges is not None:
                    edges.extend(new_edges)

        G_out.add_edges(
            [edge["pair"] for edge in edges],
            [edge["label"] for edge in edges],
            fill_out=True,
        )

        bad_states = find_inacc(G_out)
        G_out.delete_vertices(list(bad_states))
        G1 = G_out

    del G_out.vs["indexes"]
    G_out.Euc = pydash.reduce_(automata, lambda euc, g: euc | g.Euc, set()) & set(
        G_out.es["label"]
    )
    G_out.Euo = pydash.reduce_(automata, lambda euo, g: euo | g.Euo, set()) & set(
        G_out.es["label"]
    )

    return G_out


def __find_parallel_edges_at_states(
    x: dict,
    G1_vertices: List[dict],
    G2_vertices: List[dict],
    E1: EventSet,
    E2: EventSet,
    G_out_index_dict: Dict[tuple, int],
) -> Optional[List[dict]]:
    x1 = G1_vertices[x["indexes"][0]]
    x2 = G2_vertices[x["indexes"][1]]
    active_x1 = {out[1] for out in x1["out"]}
    active_x2 = {out[1] for out in x2["out"]}
    active_both = active_x1 & active_x2
    x1_ex = active_x1 - E2
    x2_ex = active_x2 - E1
    if not active_both and not x1_ex and not x2_ex:
        None

    edges = []
    for e in active_both:
        x1_outs = [G1_vertices[out[0]] for out in x1["out"] if out[1] == e]
        x2_outs = [G2_vertices[out[0]] for out in x2["out"] if out[1] == e]
        new_edges = [
            {
                "pair": (
                    x["index"],
                    G_out_index_dict[(x1_dst["index"], x2_dst["index"])],
                ),
                "label": e,
            }
            for x1_dst in x1_outs
            for x2_dst in x2_outs
        ]
        edges.extend(new_edges)

    for e in x1_ex:
        x1_outs = [G1_vertices[out[0]] for out in x1["out"] if out[1] == e]
        new_edges = [
            {
                "pair": (x["index"], G_out_index_dict[(x1_dst["index"], x2["index"])]),
                "label": e,
            }
            for x1_dst in x1_outs
        ]
        edges.extend(new_edges)

    for e in x2_ex:
        x2_outs = [G2_vertices[out[0]] for out in x2["out"] if out[1] == e]
        new_edges = [
            {
                "pair": (x["index"], G_out_index_dict[(x1["index"], x2_dst["index"])]),
                "label": e,
            }
            for x2_dst in x2_outs
        ]
        edges.extend(new_edges)

    return edges


def observer(G: Automata_t) -> Automata_t:
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
    G_obs.events = set(G_obs.es["label"])

    return G_obs


def strict_subautomata(H: DFA, G: DFA) -> Tuple[DFA, DFA]:
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
    AG = product_comp([A, G])

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

    G_tilde.Euc = G.Euc
    G_tilde.Euo = G.Euo
    G_tilde.events = G.events

    H_tilde.Euc = H.Euc
    H_tilde.Euo = H.Euo
    H_tilde.events = H.events

    return H_tilde, G_tilde
