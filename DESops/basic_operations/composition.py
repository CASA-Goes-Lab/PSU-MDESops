"""
Funcions relevant to the composition operations.
"""
from collections import deque
from typing import Any, Dict, List, Optional, Set, Tuple, Union

import pydash
from tqdm import tqdm

from DESops.automata.automata import _Automata
from DESops.automata.DFA import DFA
from DESops.automata.event.event import Event
from DESops.automata.NFA import NFA
from DESops.basic_operations.unary import find_inacc
from DESops.error import MissingAttributeError

EventSet = Set[Event]
Automata_t = Union[DFA, NFA]
SHOW_PROGRESS = False


def product_bfs(*automata: DFA) -> DFA:
    """
    Computes the product composition of 2 (or more) Automata in a BFS manner, and returns the resulting composition as a new Automata.
    """
    if len(automata) < 2:
        raise MissingAttributeError(
            "Product composition needs more than one automaton."
        )

    G1 = automata[0]
    input_list = automata[1:]

    for G2 in input_list:
        G_out = DFA()
        G1_x0 = G1.vs[0]
        G2_x0 = G2.vs[0]
        G_out_vertices = [
            {
                "name": (G1_x0["name"], G2_x0["name"]),
                "marked": G1_x0["marked"] and G2_x0["marked"],
            }
        ]
        G_out_names = {G_out_vertices[0]["name"]: 0}
        G_out_edges = []  # type: List[Dict[str, Any]]

        queue = deque([(G1_x0, G2_x0)])

        while len(queue) > 0:
            x1, x2 = queue.popleft()
            active_x1 = {e[1]: e[0] for e in x1["out"]}
            active_x2 = {e[1]: e[0] for e in x2["out"]}
            active_both = set(active_x1.keys()) & set(active_x2.keys())
            cur_name = (x1["name"], x2["name"])
            src_index = G_out_names[cur_name]

            for e in active_both:
                x1_dst = G1.vs[active_x1[e]]
                x2_dst = G2.vs[active_x2[e]]
                dst_name = (x1_dst["name"], x2_dst["name"])
                dst_index = G_out_names.get(dst_name)

                if dst_index is None:
                    G_out_vertices.append(
                        {
                            "name": dst_name,
                            "marked": x1_dst["marked"] and x2_dst["marked"],
                        }
                    )
                    dst_index = len(G_out_vertices) - 1
                    G_out_names[dst_name] = dst_index
                    queue.append((x1_dst, x2_dst))

                G_out_edges.append({"pair": (src_index, dst_index), "label": e})

        G_out.add_vertices(
            len(G_out_vertices),
            [v["name"] for v in G_out_vertices],
            [v["marked"] for v in G_out_vertices],
        )
        G_out.add_edges(
            [e["pair"] for e in G_out_edges], [e["label"] for e in G_out_edges]
        )
        G_out.events = G1.events | G2.events
        G_out.Euc = G1.Euc | G2.Euc
        G_out.Euo = G1.Euo | G2.Euo

        G1 = G_out

    return G_out


def product_linear(*automata: Automata_t) -> Automata_t:
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


def parallel_bfs(*automata: DFA) -> DFA:
    """
    Computes the parallel composition of 2 (or more) Automata in a BFS manner, and returns the resulting composition as a new Automata.
    """
    if len(automata) < 2:
        raise MissingAttributeError("More than one automaton are needed.")

    G1 = automata[0]
    input_list = automata[1:]

    for G2 in input_list:
        G_out = DFA()

        G1_x0 = G1.vs[0]
        G2_x0 = G2.vs[0]
        G_out_vertices = [
            {
                "name": (G1_x0["name"], G2_x0["name"]),
                "marked": G1_x0["marked"] and G2_x0["marked"],
            }
        ]
        G_out_names = {G_out_vertices[0]["name"]: 0}
        G_out_edges = []  # type: List[Dict[str, Any]]

        queue = deque([(G1_x0, G2_x0)])

        private_G1 = G1.events - G2.events
        private_G2 = G2.events - G1.events

        while len(queue) > 0:
            x1, x2 = queue.popleft()
            active_x1 = {e[1]: e[0] for e in x1["out"]}
            active_x2 = {e[1]: e[0] for e in x2["out"]}
            active_both = set(active_x1.keys()) & set(active_x2.keys())
            cur_name = (x1["name"], x2["name"])
            src_index = G_out_names[cur_name]

            for e in set(active_x1.keys()) | set(active_x2.keys()):
                if e in active_both:
                    x1_dst = G1.vs[active_x1[e]]
                    x2_dst = G2.vs[active_x2[e]]
                elif e in private_G1:
                    x1_dst = G1.vs[active_x1[e]]
                    x2_dst = x2
                elif e in private_G2:
                    x1_dst = x1
                    x2_dst = G2.vs[active_x2[e]]
                else:
                    continue

                dst_name = (x1_dst["name"], x2_dst["name"])
                dst_index = G_out_names.get(dst_name)

                if dst_index is None:
                    G_out_vertices.append(
                        {
                            "name": dst_name,
                            "marked": x1_dst["marked"] and x2_dst["marked"],
                        }
                    )
                    dst_index = len(G_out_vertices) - 1
                    G_out_names[dst_name] = dst_index
                    queue.append((x1_dst, x2_dst))

                G_out_edges.append({"pair": (src_index, dst_index), "label": e})

        G_out.add_vertices(
            len(G_out_vertices),
            [v["name"] for v in G_out_vertices],
            [v["marked"] for v in G_out_vertices],
        )
        G_out.add_edges(
            [e["pair"] for e in G_out_edges], [e["label"] for e in G_out_edges]
        )
        G_out.events = G1.events | G2.events
        G_out.Euc = G1.Euc | G2.Euc
        G_out.Euo = G1.Euo | G2.Euo

        G1 = G_out

    return G_out


def parallel_linear(*automata: Automata_t) -> Automata_t:
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

    x0_obs = G.unobservable_reach(0)
    G_obs_vertices = [
        {
            "name": tuple(G.vs[x_e]["name"] for x_e in x0_obs),
            "marked": False,
            "indexes": x0_obs,
        }
    ]
    G_obs_indexes = {tuple(x0_obs): 0}
    G_obs_edges = []  # type: List[Dict[str, Any]]

    B_queue = deque([x0_obs])

    while len(B_queue) > 0:
        B = B_queue.popleft()
        src_index = G_obs_indexes[tuple(B)]
        for e in Eo:
            destinations = {
                out[0] for x_e in B for out in G.vs[x_e]["out"] if out[1] == e
            }
            if len(destinations) == 0:
                continue

            u_reaches = G.unobservable_reach(destinations)
            dst_index = G_obs_indexes.get(tuple(u_reaches))
            if dst_index is None:
                G_obs_vertices.append(
                    {
                        "name": tuple(G.vs[i]["name"] for i in u_reaches),
                        "marked": False,
                        "indexes": u_reaches,
                    }
                )
                dst_index = len(G_obs_vertices) - 1
                G_obs_indexes[tuple(u_reaches)] = dst_index
                B_queue.append(u_reaches)

            G_obs_edges.append({"pair": (src_index, dst_index), "label": e})

    G_obs.add_vertices(
        len(G_obs_vertices),
        [v["name"] for v in G_obs_vertices],
        marked=[len(v["indexes"] & X_m) > 0 for v in G_obs_vertices],
    )
    G_obs.add_edges([e["pair"] for e in G_obs_edges], [e["label"] for e in G_obs_edges])

    G_obs.events = set(G_obs.es["label"])
    G_obs.Euc = G.Euc
    G_obs.Euo = G.Euo

    return G_obs


def strict_subautomata(H: DFA, G: DFA, skip_H_tilde=False) -> Tuple[Optional[DFA], DFA]:
    """
    Constructs language-equivalent automata G_tilde and H_tilde from given G and H such that H_tilde is a strict subautomaton of G_tilde.
    """
    A = H.copy()

    # Step 1:
    #   Adding a new unmarked state "dead"
    dead = A.add_vertex(name="dead", marked=False)

    #   Completing the transition function of A
    all_events = set(H.es["label"]) | set(G.es["label"])
    edges_to_dead = []
    for x in H.vs:
        active_events = {out[1] for out in H.vs[x.index]["out"]}
        non_active_events = all_events - active_events
        edges_to_dead.extend(
            [
                {"pair": (x.index, dead.index), "label": event}
                for event in non_active_events
            ]
        )

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
    AG = product_bfs(A, G)

    # Step 3:
    #   Step 3.1: Obtaining G_tilde
    G_tilde = AG.copy()  # Taking AG
    G_states = {x["name"]: x["marked"] for x in G.vs}
    G_tilde.vs["marked"] = [G_states[state["name"][1]] for state in G_tilde.vs]

    G_tilde.Euc = G.Euc
    G_tilde.Euo = G.Euo
    G_tilde.events = G.events

    if skip_H_tilde:
        return None, G_tilde

    #   Step 3.2: Obtaining H_tilde by deleting all state of AG where the first state component is "dead".
    H_tilde = AG.copy()
    dead_states = [state for state in H_tilde.vs if state["name"][0] == "dead"]
    H_tilde.delete_vertices(dead_states)
    H_states = {x["name"]: x["marked"] for x in H.vs}
    H_tilde.vs["marked"] = [H_states[state["name"][0]] for state in H_tilde.vs]

    H_tilde.Euc = H.Euc
    H_tilde.Euo = H.Euo
    H_tilde.events = H.events

    return H_tilde, G_tilde
