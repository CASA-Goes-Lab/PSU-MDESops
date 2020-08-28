"""
Funcions relevant to the composition operations.
"""
from collections import deque
from typing import Any, Dict, List, Optional, Set, Tuple, Union

import pydash
from tqdm import tqdm

from DESops.automata.automata import _Automata
from DESops.automata.DFA import DFA
from DESops.automata.event import Event
from DESops.automata.NFA import NFA
from DESops.basic_operations.unary import find_inacc
from DESops.error import MissingAttributeError

EventSet = Set[Event]
Automata_t = Union[DFA, NFA]
SHOW_PROGRESS = False


def product_bfs(*automata: DFA):
    """
    TODO: legacy; use composition.product instead (same thing but more succinct name)
    """
    import warnings

    warnings.warn(
        "TODO: legacy; use composition.product instead (same thing but more succinct name"
    )


def product(*automata: DFA) -> DFA:
    """
    Computes the product composition of 2 (or more) Automata in a BFS manner, and returns the resulting composition as a new Automata.
    """
    if len(automata) < 2:
        raise MissingAttributeError(
            "Product composition needs more than one automaton."
        )

    if any(g.vcount() == 0 for g in automata):
        return DFA()

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
        G_out.Euc.update(G1.Euc | G2.Euc)
        G_out.Euo.update(G1.Euo | G2.Euo)

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
    G_out.Euc.update(
        pydash.reduce_(automata, lambda euc, g: euc | g.Euc, set())
        & set(G_out.es["label"])
    )
    G_out.Euo.update(
        pydash.reduce_(automata, lambda euo, g: euo | g.Euo, set())
        & set(G_out.es["label"])
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


def parallel_bfs(*automata: DFA):
    """
    TODO: legacy; use composition.parallel instead (same thing but more succinct name)
    """
    import warnings

    warnings.warn(
        "TODO: legacy; use composition.parallel instead (same thing but more succinct name)"
    )


def parallel(*automata: DFA) -> DFA:
    """
    Computes the parallel composition of 2 (or more) Automata in a BFS manner, and returns the resulting composition as a new Automata.
    """
    if len(automata) < 2:
        raise MissingAttributeError("More than one automaton are needed.")

    G1 = automata[0]
    input_list = automata[1:]

    if any(i.vcount() == 0 for i in automata):
        # if any inputs are empty, return empty automata
        return DFA()

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
        G_out.Euc.update(G1.Euc | G2.Euc)
        G_out.Euo.update(G1.Euo | G2.Euo)

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
    G_out.Euc.update(
        pydash.reduce_(automata, lambda euc, g: euc | g.Euc, set())
        & set(G_out.es["label"])
    )
    G_out.Euo.update(
        pydash.reduce_(automata, lambda euo, g: euo | g.Euo, set())
        & set(G_out.es["label"])
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
    Compute the observer automata of the input G
    G should be a DFA, NFA or PFA

    Returns the observer as a DFA
    """
    observer = DFA()
    if not G.vcount() or G is None:
        return observer

    vertice_names = list()  # list of vertex names for igraph construction
    vertice_number = dict()  # dictionary vertex_names -> vertex_id
    outgoing_list = list()  # list of outgoing lists for each vertex
    marked_list = list()  # list with vertices marking
    transition_list = list()  # list of transitions for igraph construction
    transition_label = list()  # list os transitions label for igraph construction

    # BFS queue that holds states that must be visited
    queue = list()

    # index tracks the current number of vertices in the graph
    index = 0

    if isinstance(G, NFA):
        init_states = frozenset(v.index for v in G.vs if v["init"])
    else:
        init_states = frozenset({0})

    # Makes Euo hashable for UR dict key:
    Euo = frozenset(G.Euo)

    # Find UR from initial state(s):
    v0 = G.UR.from_set(init_states, Euo, freeze_result=True)

    name_v0 = frozenset([G.vs["name"][v] for v in v0])
    marking = any([G.vs["marked"][v] for v in v0])
    vertice_names.insert(index, name_v0)
    vertice_number[v0] = index
    marked_list.insert(index, marking)

    index = index + 1
    queue.append(v0)
    while queue:
        v = queue.pop(0)

        # finding observable adjacent from v
        adj_states = dict()
        for vert in v:
            for target, event in G.vs["out"][vert]:
                if event in adj_states and event not in G.Euo:
                    adj_states[event].add(target)
                elif event not in adj_states and event not in G.Euo:
                    s = set()
                    s.add(target)
                    adj_states[event] = s

        # print(adj_states)
        outgoing_v1v2 = list()
        for ev in adj_states.keys():
            next_state = frozenset(adj_states[ev])

            next_state = G.UR.from_set(next_state, Euo, freeze_result=True)
            # updating lists for igraph construction
            if next_state in vertice_number.keys():
                transition_list.append((vertice_number[v], vertice_number[next_state]))
                transition_label.append(ev)
            else:
                name_next_state = frozenset([G.vs["name"][v] for v in next_state])
                transition_list.append((vertice_number[v], index))
                transition_label.append(ev)
                vertice_number[next_state] = index
                marking = any([G.vs["marked"][v] for v in next_state])
                marked_list.insert(index, marking)
                vertice_names.insert(index, name_next_state)
                queue.append(next_state)
                index = index + 1
            outgoing_v1v2.append(observer.Out(vertice_number[next_state], ev))
        outgoing_list.insert(vertice_number[v], outgoing_v1v2)

    # constructing DFA: igraph and events sets
    observer.add_vertices(index, vertice_names)
    observer.events = G.events - G.Euo
    observer.Euc.update(G.Euc - G.Euo)
    observer.Euo.clear()
    observer.vs["marked"] = marked_list
    observer.add_edges(transition_list, transition_label, fill_out=False)
    observer.vs["out"] = outgoing_list
    return observer


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
        active_events = {out[1] for out in x["out"]}
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
    AG = product(A, G)

    # Step 3:
    #   Step 3.1: Obtaining G_tilde
    G_tilde = AG.copy()  # Taking AG
    G_states = {x["name"]: x["marked"] for x in G.vs}
    G_tilde.vs["marked"] = [G_states[state["name"][1]] for state in G_tilde.vs]

    G_tilde.Euc.update(G.Euc)
    G_tilde.Euo.update(G.Euo)
    G_tilde.events = G.events

    if skip_H_tilde:
        return None, G_tilde

    #   Step 3.2: Obtaining H_tilde by deleting all state of AG where the first state component is "dead".
    H_tilde = AG.copy()
    dead_states = [state for state in H_tilde.vs if state["name"][0] == "dead"]
    H_tilde.delete_vertices(dead_states)
    H_states = {x["name"]: x["marked"] for x in H.vs}
    H_tilde.vs["marked"] = [H_states[state["name"][0]] for state in H_tilde.vs]

    H_tilde.Euc.update(H.Euc)
    H_tilde.Euo.update(H.Euo)
    H_tilde.events = H.events

    return H_tilde, G_tilde
