import logging
from collections import deque
from enum import Enum, auto
from typing import Optional, Set, Tuple

import pydash

from DESops.automata import DFA
from DESops.automata.event.event import Event
from DESops.basic_operations import composition, unary


class Mode(Enum):
    CONTROLLABLE = auto()
    NORMAL = auto()
    CONTROLLABLE_NORMAL = auto()


EventSet = Set[Event]
StateSet = Set[int]


def supremal_sublanguage(
    plant: DFA,
    spec: DFA,
    Euc: Optional[EventSet] = None,
    Euo: Optional[EventSet] = None,
    mode: int = Mode.CONTROLLABLE_NORMAL,
) -> DFA:

    if Euc is None:
        Euc = plant.Euc | spec.Euc
    if Euo is None:
        Euo = plant.Euo | spec.Euo

    G_given = plant.copy()
    H_given = spec.copy()
    G_given.Euc, G_given.Euo, H_given.Euc, H_given.Euo = Euc, Euo, Euc, Euo

    G, H = preprocessing(G_given, H_given)
    G_obs = composition.observer(G)

    while True:
        deleted_states = set()
        if mode in [Mode.NORMAL, Mode.CONTROLLABLE_NORMAL]:
            bad_states_to_normal = check_normality(H, G_obs)
            H.delete_vertices(bad_states_to_normal)
            deleted_states |= bad_states_to_normal
        if mode in [Mode.CONTROLLABLE, Mode.CONTROLLABLE_NORMAL]:
            inacc_states = unary.find_inacc(H)
            H.delete_vertices(inacc_states)
            bad_states_to_controllable = check_controllability(H, G)
            H.delete_vertices(bad_states_to_controllable)
            deleted_states |= inacc_states | bad_states_to_controllable

        bad_states_to_trim = unary.trim(H)
        H.delete_vertices(bad_states_to_trim)
        deleted_states |= bad_states_to_trim

        if H.vcount() == 0:
            return None
        elif len(deleted_states) == 0:
            return H


def check_normality(H: DFA, G_obs: DFA) -> StateSet:
    """
    Check the normality condition of states H and returns states violating the condition.
    """
    bad_states = set()
    all_states = set(H.vs["name"])
    for y in H.vs:
        for q in G_obs.vs["name"]:
            if y["name"] in q and not set(q) <= all_states:
                bad_states.add(y.index)
                break

    return bad_states


def check_controllability(H: DFA, G: DFA) -> StateSet:
    """
    Check the controllability condition of states in H and returns states violating the condition.
    """

    dfs_root_states = set()
    H_all_states = set(H.vs["name"])
    G_all_states = set(G.vs["name"])
    out_of_range = G_all_states - H_all_states

    for x in out_of_range:
        state = G.vs.select(name_eq=x)[0]
        pre_with_Euc = {
            pre["name"]
            for pre in state.predecessors()
            if pre["name"] in H_all_states
            and pydash.find(
                pre.out_edges(),
                lambda e: e.target == state.index and e["label"] in G.Euc,
            )
            is not None
        }
        dfs_root_states |= pre_with_Euc  # predecessors in H of out-of-range states

    bad_states = set()

    for root in dfs_root_states:
        visited = {root}
        states_stack = deque(visited)
        while len(states_stack) > 0:
            name = states_stack.pop()
            state = H.vs.select(name_eq=name)[0]
            pre_by_Euc = {
                pre["name"]
                for pre in state.predecessors()
                if pydash.find(
                    pre.out_edges(),
                    lambda e: e.target == state.index and e["label"] in H.Euc,
                )
                is not None
            }
            for pre in pre_by_Euc:
                if pre not in visited and pre not in bad_states:
                    visited.add(pre)
                    states_stack.append(pre)

        bad_states |= visited

    return bad_states


def preprocessing(G_given: DFA, H_given: DFA) -> Tuple[DFA, DFA]:
    """
    Preprocess to obtain G and H such that
        1. H is a strict subautomaton of G
        2. G is an SPA with respect to G.Euo
    """

    # 1. Construct G_tilde and H_tilde from G_given and H_given such that H_tilde is a strict subautomaton of G_tilde.
    H_tilde, G_tilde = composition.strict_subautomata(H_given, G_given)

    # 2. Construct G which is an SPA.
    G_obs = composition.observer(G_tilde)
    G = composition.parallel(G_tilde, G_obs)

    # 3. Extract H from G by deleteing all states ((x, y), z) of G where x = "dead".
    H = G.copy()
    dead_states = [v.index for v in H.vs if v["name"][0][0] == "dead"]
    H.delete_vertices(dead_states)

    H_names = {str(v.index): v["name"] for v in H.vs}
    H.vs["name"] = list(H_names.keys())
    G_name_index = H.vcount()
    for v in G.vs:
        name = pydash.find(H_names.keys(), lambda k: H_names[k] == v["name"])
        if name is not None:
            new_name = name
        else:
            new_name = str(G_name_index)
            G_name_index += 1
        G.vs[v.index].update_attributes({"name": new_name})

    return G, H
