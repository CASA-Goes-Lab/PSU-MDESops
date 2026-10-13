"""
Funcions relevant to the composition operations.
"""
# TODO add description of operations or add reference to textbook
from collections import deque
from typing import Any, Dict, List, Optional, Set, Tuple, Union

import pydash
from tqdm import tqdm

from DESops.core.automata import Automata, UnobservableReach
from DESops.core.automaton import Automaton
from DESops.core.dfa import DFA
from DESops.core.event import Event
from DESops.core.nfa import NFA
from DESops.core.operations.unary import find_inacc
from DESops.error import MissingAttributeError

EventSet = Set[Event]
Automata_t = Union[DFA, NFA]
SHOW_PROGRESS = False

#TODO legacy; use composition.product instead (same thing but more succinct name)
def product_bfs(*automata: DFA):
    """
    Compute the product of multiple `DFA` in a breadth-first manner.

    .. deprecated:: 20.9.2
        use `composition.product` instead of `composition.product_bfs`
        this offers the same behavior but has a more succinct name

    Parameters
    ----------
    automata : list[DFA]

    Returns
    -------
    DFA
        The product of the automata

    """
    import warnings

    warnings.warn(
        "deprecated; use composition.product instead (same thing but more succinct name"
    )
    return product(*automata)

# TODO : generalize to NFA
def product(*automata: DFA, backend: str = "igraph") -> DFA:
    """
    Computes the synchronous product composition of 2 (or more) Automata in a BFS manner,
    Returns the resulting composition as a new automatan.

    Parameters
    ----------
    automata : list[DFA]
    backend : str
        Which implementation to use: "igraph" (default, reads via the
        automata's igraph view) or "native" (pure Python over
        AutomatonData, no igraph dependency). Both produce equivalent
        results; see doc/logs/v2-igraph-decoupling.md.

    Returns
    -------
    DFA
        The product of the automata
    """
    if backend == "igraph":
        return _product_igraph(*automata)
    elif backend == "native":
        return _product_native(*automata)
    else:
        raise ValueError(f"Unknown backend: {backend!r}")


def _product_igraph(*automata: DFA) -> DFA:
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
            [e["pair"] for e in G_out_edges],
            [e["label"] for e in G_out_edges],
            check_DFA=False,
            fill_out=True,
        )
        G_out.events = G1.events | G2.events
        G_out.Euc.update(G1.Euc | G2.Euc)
        G_out.Euo.update(G1.Euo | G2.Euo)

        G1 = G_out

    return G_out


def _product_native(*automata: DFA) -> DFA:
    """
    Pure-Python (no igraph) equivalent of _product_igraph. Same BFS-over-
    state-pairs algorithm as _parallel_native, minus the private-event
    branches (product only follows events active in both automata).
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

        data1 = G1.to_data()
        data2 = G2.to_data()
        adj1 = data1.out_adjacency()
        adj2 = data2.out_adjacency()

        G_out_vertices = [
            {
                "name": (data1.names[0], data2.names[0]),
                "marked": data1.marked[0] and data2.marked[0],
            }
        ]
        G_out_names = {G_out_vertices[0]["name"]: 0}
        G_out_edges = []  # type: List[Dict[str, Any]]

        queue = deque([(0, 0)])

        while len(queue) > 0:
            x1, x2 = queue.popleft()
            active_x1 = {label: target for target, label in adj1[x1]}
            active_x2 = {label: target for target, label in adj2[x2]}
            active_both = set(active_x1.keys()) & set(active_x2.keys())
            cur_name = (data1.names[x1], data2.names[x2])
            src_index = G_out_names[cur_name]

            for e in active_both:
                x1_dst = active_x1[e]
                x2_dst = active_x2[e]
                dst_name = (data1.names[x1_dst], data2.names[x2_dst])
                dst_index = G_out_names.get(dst_name)

                if dst_index is None:
                    G_out_vertices.append(
                        {
                            "name": dst_name,
                            "marked": data1.marked[x1_dst] and data2.marked[x2_dst],
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
            [e["pair"] for e in G_out_edges],
            [e["label"] for e in G_out_edges],
            check_DFA=False,
            fill_out=True,
        )
        G_out.events = G1.events | G2.events
        G_out.Euc.update(G1.Euc | G2.Euc)
        G_out.Euo.update(G1.Euo | G2.Euo)

        G1 = G_out

    return G_out

# TODO Is this bugged?
def product_linear(*automata: Automata_t) -> Automata_t:
    """
    Computes the product composition of 2 (or more) automata, and returns the resulting composition as a new automata.
    If all input automata are `DFA`, the output is also a `DFA`. Otherwise the output is an `NFA`.

    Parameters
    ----------
    automata : list[DFA or NFA]

    Returns
    -------
    DFA or NFA
        The product
    """
    if len(automata) < 2:
        raise MissingAttributeError("More than one automaton are needed.")

    # add init attribute to all automata so that both DFAs and NFAs will work
    for g in automata:
        if "init" not in g.vs.attributes():
            g.vs["init"] = False
            g.vs[0]["init"] = True

    G1 = automata[0]
    input_list = automata[1:]

    for G2 in tqdm(
        input_list, desc="Product Composition", disable=SHOW_PROGRESS is False
    ):
        # result is nondeterministic if any input is nondeterministic
        if any(isinstance(g, NFA) for g in automata):
            G_out = NFA()
        else:
            G_out = DFA()

        num_G2_states = len(G2.vs)
        G_out_vertices = [
            {
                "index": i * num_G2_states + j,
                "name": (x1["name"], x2["name"]),
                "marked": x1["marked"] is True and x2["marked"] is True,
                "init": x1["init"] and x2["init"],
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
            init=[v["init"] for v in G_out_vertices],
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

# TODO: legacy; use composition.parallel instead (same thing but more succinct name)
def parallel_bfs(*automata: DFA):
    """
    Compute the parallel composition of multiple `DFA` in a breadth-first manner.

    .. deprecated:: 20.9.2
        use `composition.parallel` instead of `composition.parallel_bfs`
        this offers the same behavior but has a more succinct name

    Parameters
    ----------
    automata : list[DFA]

    Returns
    -------
    DFA
        The parallel composition of the automata
    """
    import warnings

    warnings.warn(
        "deprecated; use composition.parallel instead (same thing but more succinct name)"
    )

    return parallel_bfs(*automata)


def parallel(*automata: DFA, backend: str = "igraph") -> DFA:
    """
    Computes the parallel composition of 2 (or more) Automata in a BFS manner, and returns the resulting composition as a new Automata.

    Parameters
    ----------
    automata : list[DFA]
    backend : str
        Which implementation to use: "igraph" (default, reads via the
        automata's igraph view) or "native" (pure Python over
        AutomatonData, no igraph dependency). Both produce equivalent
        results; "native" exists so a future non-igraph backend (e.g.
        BDD) can be compared or substituted. See
        doc/logs/v2-igraph-decoupling.md.

    Returns
    -------
    DFA
        The parallel composition
    """
    if automata and all(isinstance(g, Automaton) for g in automata):
        return _parallel_automaton(*automata)
    if backend == "igraph":
        return _parallel_igraph(*automata)
    elif backend == "native":
        return _parallel_native(*automata)
    else:
        raise ValueError(f"Unknown backend: {backend!r}")


def _parallel_automaton(*automata: Automaton) -> Automaton:
    """
    Parallel composition of DESops.core.automaton.Automaton inputs, folded
    left to right. Shared events synchronize; private events interleave.
    Unlike _parallel_igraph/_parallel_native, every combination of initial
    states is a start state, so NFA inputs with several initial states work.
    State names are (name1, name2) tuples, as in the old implementations.
    """
    if len(automata) < 2:
        raise MissingAttributeError("More than one automaton are needed.")
    if any(g.probabilistic for g in automata):
        raise ValueError("parallel composition of probabilistic automata is not supported")

    result = automata[0]
    for other in automata[1:]:
        result = _parallel_pair(result, other)
    return result


def _parallel_pair(G1: Automaton, G2: Automaton) -> Automaton:
    out = Automaton(
        events=G1.events | G2.events, Euc=G1.Euc | G2.Euc, Euo=G1.Euo | G2.Euo
    )
    if not G1.states or not G2.states:
        return out

    shared = G1.events & G2.events
    index = {}
    queue = deque()

    def visit(x1, x2):
        pair = (x1, x2)
        if pair not in index:
            s1, s2 = G1.states[x1], G2.states[x2]
            index[pair] = out.add_state((s1.name, s2.name), s1.marked and s2.marked)
            queue.append(pair)
        return index[pair]

    for x1 in sorted(G1.init):
        for x2 in sorted(G2.init):
            out.init.add(visit(x1, x2))

    while queue:
        x1, x2 = queue.popleft()
        source = index[(x1, x2)]
        out1, out2 = G1.states[x1].out, G2.states[x2].out
        for event, targets1 in out1.items():
            if event in shared:
                for t1 in targets1:
                    for t2 in out2.get(event, ()):
                        out.add_transition(source, event, visit(t1, t2))
            else:
                for t1 in targets1:
                    out.add_transition(source, event, visit(t1, x2))
        for event, targets2 in out2.items():
            if event not in shared:
                for t2 in targets2:
                    out.add_transition(source, event, visit(x1, t2))
    return out


def _parallel_igraph(*automata: DFA) -> DFA:
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
            [e["pair"] for e in G_out_edges],
            [e["label"] for e in G_out_edges],
            check_DFA=False,
            fill_out=True,
        )
        G_out.events = G1.events | G2.events
        G_out.Euc.update(G1.Euc | G2.Euc)
        G_out.Euo.update(G1.Euo | G2.Euo)

        G1 = G_out

    return G_out


def _parallel_native(*automata: DFA) -> DFA:
    """
    Pure-Python (no igraph) equivalent of _parallel_igraph. Same BFS-over-
    state-pairs algorithm; state indices are used directly instead of
    igraph Vertex objects, and adjacency/name/marking lookups go through
    AutomatonData.out_adjacency() and to_data() instead of `.vs`/`.es`.
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

        data1 = G1.to_data()
        data2 = G2.to_data()
        adj1 = data1.out_adjacency()
        adj2 = data2.out_adjacency()

        G_out_vertices = [
            {
                "name": (data1.names[0], data2.names[0]),
                "marked": data1.marked[0] and data2.marked[0],
            }
        ]
        G_out_names = {G_out_vertices[0]["name"]: 0}
        G_out_edges = []  # type: List[Dict[str, Any]]

        queue = deque([(0, 0)])

        private_G1 = G1.events - G2.events
        private_G2 = G2.events - G1.events

        while len(queue) > 0:
            x1, x2 = queue.popleft()
            active_x1 = {label: target for target, label in adj1[x1]}
            active_x2 = {label: target for target, label in adj2[x2]}
            active_both = set(active_x1.keys()) & set(active_x2.keys())
            cur_name = (data1.names[x1], data2.names[x2])
            src_index = G_out_names[cur_name]

            for e in set(active_x1.keys()) | set(active_x2.keys()):
                if e in active_both:
                    x1_dst = active_x1[e]
                    x2_dst = active_x2[e]
                elif e in private_G1:
                    x1_dst = active_x1[e]
                    x2_dst = x2
                elif e in private_G2:
                    x1_dst = x1
                    x2_dst = active_x2[e]
                else:
                    continue

                dst_name = (data1.names[x1_dst], data2.names[x2_dst])
                dst_index = G_out_names.get(dst_name)

                if dst_index is None:
                    G_out_vertices.append(
                        {
                            "name": dst_name,
                            "marked": data1.marked[x1_dst] and data2.marked[x2_dst],
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
            [e["pair"] for e in G_out_edges],
            [e["label"] for e in G_out_edges],
            check_DFA=False,
            fill_out=True,
        )
        G_out.events = G1.events | G2.events
        G_out.Euc.update(G1.Euc | G2.Euc)
        G_out.Euo.update(G1.Euo | G2.Euo)

        G1 = G_out

    return G_out


def parallel_linear(*automata: Automata_t) -> Automata_t:
    """
    Computes the parallel composition of 2 (or more) automata, and returns the resulting composition as a new automata.
    If all input automata are `DFA`, the output is also a `DFA`. Otherwise the output is an `NFA`.

    Parameters
    ----------
    automata : list[DFA or NFA]

    Returns
    -------
    DFA or NFA
        The parallel composition
    """
    if len(automata) < 2:
        raise MissingAttributeError("More than one automaton are needed.")

    G1 = automata[0]
    input_list = automata[1:]

    for G2 in tqdm(
        input_list, desc="Parallel Composition", disable=SHOW_PROGRESS is False
    ):
        if any(isinstance(g, NFA) for g in automata):
            G_out = NFA()
        else:
            G_out = DFA()
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


def observer(G: Automata_t, backend: str = "igraph") -> Automata_t:
    """
    Compute the observer automata of the input `G` with respect to its unobservable events
    `G` should be a `DFA`, `NFA` or `PFA`

    Parameters
    ----------
    G : NFA or DFA or PFA
        The automaton
    backend : str
        Which implementation to use: "igraph" (default) or "native" (pure
        Python over AutomatonData, no igraph dependency). See
        doc/logs/v2-igraph-decoupling.md.

    Returns
    -------
    DFA
        The observer automaton
    """
    if backend == "igraph":
        return _observer_igraph(G)
    elif backend == "native":
        return _observer_native(G)
    else:
        raise ValueError(f"Unknown backend: {backend!r}")


def _observer_igraph(G: Automata_t) -> Automata_t:
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

    observer.vs[0]["init"] = True
    observer.add_edges(
        transition_list, transition_label, check_DFA=False, fill_out=False
    )
    observer.vs["out"] = outgoing_list

    observer.vs["name"] = [tuple(v) for v in observer.vs["name"]]

    return observer


def _observer_native(G: Automata_t) -> Automata_t:
    """
    Pure-Python (no igraph) equivalent of _observer_igraph. Same subset-
    construction algorithm; reads AutomatonData/out_adjacency() instead of
    G.vs, and uses a fresh UnobservableReach wrapping that native
    adjacency (see AutomatonData.out_adjacency()'s docstring) instead of
    G.UR, which is tied to G's igraph view.
    """
    observer = DFA()
    if not G.vcount():
        return observer

    data = G.to_data()
    adjacency = data.out_adjacency()
    n = data.num_states

    vertice_names = list()
    vertice_number = dict()
    marked_list = list()
    transition_list = list()
    transition_label = list()

    queue = list()
    index = 0

    if isinstance(G, NFA):
        init_flags = data.vertex_attrs.get("init", [False] * n)
        init_states = frozenset(i for i in range(n) if init_flags[i])
    else:
        init_states = frozenset({0})

    Euo = frozenset(G.Euo)
    ur = UnobservableReach(G.Euo, {"out": adjacency})

    v0 = ur.from_set(init_states, Euo, freeze_result=True)

    name_v0 = frozenset(data.names[v] for v in v0)
    marking = any(data.marked[v] for v in v0)
    vertice_names.insert(index, name_v0)
    vertice_number[v0] = index
    marked_list.insert(index, marking)

    index = index + 1
    queue.append(v0)
    while queue:
        v = queue.pop(0)

        adj_states = dict()
        for vert in v:
            for target, event in adjacency[vert]:
                if event in adj_states and event not in G.Euo:
                    adj_states[event].add(target)
                elif event not in adj_states and event not in G.Euo:
                    s = set()
                    s.add(target)
                    adj_states[event] = s

        for ev in adj_states.keys():
            next_state = frozenset(adj_states[ev])

            next_state = ur.from_set(next_state, Euo, freeze_result=True)
            if next_state in vertice_number.keys():
                transition_list.append((vertice_number[v], vertice_number[next_state]))
                transition_label.append(ev)
            else:
                name_next_state = frozenset(data.names[v] for v in next_state)
                transition_list.append((vertice_number[v], index))
                transition_label.append(ev)
                vertice_number[next_state] = index
                marking = any(data.marked[v] for v in next_state)
                marked_list.insert(index, marking)
                vertice_names.insert(index, name_next_state)
                queue.append(next_state)
                index = index + 1

    init_kwarg = [i == 0 for i in range(index)]
    observer.add_vertices(
        index, [tuple(v) for v in vertice_names], marked_list, init=init_kwarg
    )
    observer.events = G.events - G.Euo
    observer.Euc.update(G.Euc - G.Euo)
    observer.Euo.clear()
    observer.add_edges(
        transition_list, transition_label, check_DFA=False, fill_out=False
    )

    return observer


def strict_subautomata(H: DFA, G: DFA, skip_H_tilde=False) -> Tuple[Optional[DFA], DFA]:
    """
    Constructs language-equivalent automata G_tilde and H_tilde from given G and H such that H_tilde is a strict subautomaton of G_tilde.

    Parameters
    ----------
    H : DFA
        The automaton to make into a subautomaton
    G : DFA
        The automaton to make into a superautomaton
    skip_H_tilde : bool
        If True, then skip the construction of `H_tilde`, instead only constructing `G_tilde`

    Returns
    -------
    H_tilde : DFA or None
        The constructed subautomaton (or None if `skip_H_tilde` is True)
    G_tilde : DFA
        The constructed superautomaton
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
        check_DFA=False,
        fill_out=True,
    )

    dead_selfloops = [
        {"pair": (dead.index, dead.index), "label": event} for event in all_events
    ]
    A.add_edges(
        [edge["pair"] for edge in dead_selfloops],
        [edge["label"] for edge in dead_selfloops],
        check_DFA=False,
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
