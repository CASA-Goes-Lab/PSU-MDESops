from concurrent.futures import ProcessPoolExecutor, as_completed
from enum import Enum, auto
from os import cpu_count
from typing import List, Optional, Set, Tuple

import pydash
from tqdm import tqdm

from DESops.automata import DFA
from DESops.automata.event.event import Event
from DESops.basic_operations import composition, unary


class Mode(Enum):
    CONTROLLABLE = auto()
    NORMAL = auto()
    CONTROLLABLE_NORMAL = auto()


EventSet = Set[Event]
StateSet = Set[int]

SHOW_PROGRESS = False
MAX_PROCESSES = cpu_count()


def supremal_sublanguage(
    plant: DFA,
    spec: DFA,
    Euc: Optional[EventSet] = None,
    Euo: Optional[EventSet] = None,
    mode: Mode = Mode.CONTROLLABLE_NORMAL,
    preprocess: bool = True,
) -> DFA:
    """
    Computes the supremal controllable and/or normal supervisor for the given plant and specification Automata.
    """

    if Euc is None:
        Euc = plant.Euc | spec.Euc
    if Euo is None:
        Euo = plant.Euo | spec.Euo

    G_given = plant.copy()
    H_given = spec.copy()
    G_given.Euc, G_given.Euo, H_given.Euc, H_given.Euo = Euc, Euo, Euc, Euo

    (G, H) = preprocessing(G_given, H_given) if preprocess else (G_given, H_given)
    G_obs = composition.observer(G)

    while True:
        deleted_states = set()
        if mode in [Mode.NORMAL, Mode.CONTROLLABLE_NORMAL]:
            bad_states_for_normality = check_normality(H, G_obs)
            H.delete_vertices(bad_states_for_normality)
            deleted_states |= bad_states_for_normality
        if mode in [Mode.CONTROLLABLE, Mode.CONTROLLABLE_NORMAL]:
            inacc_states = unary.find_inacc(H)
            H.delete_vertices(inacc_states)
            bad_states_for_controllability = check_controllability(H, G)
            H.delete_vertices(bad_states_for_controllability)
            deleted_states |= inacc_states | bad_states_for_controllability

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
    all_H_names = H.vs["name"]
    all_Gobs_names = G_obs.vs["name"]
    with ProcessPoolExecutor(max_workers=MAX_PROCESSES) as executor:
        futures = []
        for i, H_indecies in enumerate(
            pydash.chunk(range(H.vcount()), H.vcount() // MAX_PROCESSES)
        ):
            futures.append(
                executor.submit(
                    __find_bad_states_nomal, H_indecies, all_Gobs_names, all_H_names, i
                )
            )

        for f in as_completed(futures):
            bad_states |= f.result()

    return bad_states


def __find_bad_states_nomal(
    H_indecies: List[int], Gobs_names: List[str], H_names: List[str], barpos: int
) -> StateSet:
    bad_states = set()
    for index in tqdm(
        H_indecies,
        desc="Nomarlity",
        disable=SHOW_PROGRESS is False,
        leave=False,
        position=barpos,
        mininterval=0.5,
    ):
        y = H_names[index]
        for q in Gobs_names:
            if y in q and not set(q) <= set(H_names):
                bad_states.add(index)
                break

    return bad_states


def check_controllability(H: DFA, G: DFA) -> StateSet:
    """
    Check the controllability condition of states in H and returns states violating the condition.
    """

    G_all_states = {v["name"]: v["out"] for v in G.vs}
    H_all_states = {v["name"]: {"index": v.index, "out": v["out"]} for v in H.vs}
    bad_states = set()
    Euc = G.Euc

    with ProcessPoolExecutor(max_workers=MAX_PROCESSES) as executor:
        futures = []
        for i, H_names in enumerate(
            pydash.chunk(list(H_all_states.keys()), len(H_all_states) // MAX_PROCESSES)
        ):
            futures.append(
                executor.submit(
                    __find_bad_states_controllable,
                    H_names,
                    H_all_states,
                    G_all_states,
                    Euc,
                    i,
                )
            )

        for f in as_completed(futures):
            bad_states |= f.result()

    return bad_states


def __find_bad_states_controllable(
    H_names_to_check: List[str],
    H_all_states: dict,
    G_all_states: dict,
    Euc: EventSet,
    barpos: int,
) -> StateSet:
    bad_states = set()

    # States at which the supervisor improperly disables uncontrollable events must be removed.
    for H_name in tqdm(
        H_names_to_check,
        desc="Controllability",
        disable=SHOW_PROGRESS is False,
        leave=False,
        position=barpos,
        mininterval=0.5,
    ):
        xH = H_all_states[H_name]
        xG = G_all_states[H_name]

        xG_out_events = {x[1] for x in xG}
        xH_out_events = {x[1] for x in xH["out"]}

        if xG_out_events != xH_out_events:
            for e in xG_out_events - xH_out_events:
                if e in Euc:
                    bad_states.add(xH["index"])
                    break

    return bad_states


def preprocessing(
    G_given: DFA, H_given: DFA, skip_subautomata=False
) -> Tuple[DFA, DFA]:
    """
    Preprocess to obtain G and H such that
        1. H is a strict subautomaton of G
        2. G is an SPA with respect to G.Euo
    """

    # 1. Construct G_tilde and H_tilde from G_given and H_given such that H_tilde is a strict subautomaton of G_tilde.
    if skip_subautomata:
        G_tilde = G_given
    else:
        _, G_tilde = composition.strict_subautomata(H_given, G_given, skip_H_tilde=True)

    # 2. Construct G which is an SPA.
    G_obs = composition.observer(G_tilde)
    G = composition.parallel_bfs(G_tilde, G_obs)

    # 3. Extract H from G by deleteing all states ((x, y), z) of G where x = "dead".
    H = G.copy()
    dead_states = [v.index for v in H.vs if v["name"][0][0] == "dead"]
    G.vs["name"] = [str(i) for i in range(G.vcount())]
    H.vs["name"] = [str(i) for i in range(H.vcount())]
    H.delete_vertices(dead_states)

    return G, H
