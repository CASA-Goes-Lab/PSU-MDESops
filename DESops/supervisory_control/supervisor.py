from concurrent.futures import ProcessPoolExecutor, as_completed
from enum import Enum, auto
from os import cpu_count
from typing import List, Optional, Set, Tuple

import pydash
from tqdm import tqdm

from DESops.automata import DFA
from DESops.automata.event import Event
from DESops.basic_operations import composition, unary
from DESops.supervisory_control.AES.AES import construct_AES, extract_AES_super
from DESops.supervisory_control.VLPPO.VLPPO import offline_VLPPO


class Mode(Enum):
    CONTROLLABLE = auto()
    NORMAL = auto()
    CONTROLLABLE_NORMAL = auto()


EventSet = Set[Event]
StateSet = Set[int]

SHOW_PROGRESS = False


def supremal_sublanguage(
    plant: DFA,
    spec: DFA,
    Euc: Optional[EventSet] = None,
    Euo: Optional[EventSet] = None,
    mode: Mode = Mode.CONTROLLABLE_NORMAL,
    preprocess: bool = True,
    prefix_closed: bool = False,
    num_cores: int = None,
) -> DFA:
    """
    Computes the supremal controllable and/or normal supervisor for the given plant and specification Automata.
    """
    if not num_cores:
        MAX_PROCESSES = 1
    else:
        MAX_PROCESSES = max(cpu_count(), num_cores)
    G_given = plant.copy()

    if not isinstance(spec, DFA) and not isinstance(spec, set):
        raise TypeError(
            "Expected spec to be type DFA or set (of names of critical states). Got {}".format(
                type(spec)
            )
        )

    if isinstance(spec, set):
        G_given = plant.copy()
        G_given.vs["name"] = ["dead" if v in spec else v for v in plant.vs["name"]]
        H_given = G_given.copy()
        H_given.delete_vertices([i.index for i in H_given.vs if i["name"] == "dead"])
        skip_SA = True

        G_given.Euc.update(Euc if Euc is not None else plant.Euc)
        G_given.Euo.update(Euo if Euo is not None else plant.Euo)
    else:
        skip_SA = False
        H_given = spec.copy()
        if Euc is None:
            Euc = plant.Euc | spec.Euc
        if Euo is None:
            Euo = plant.Euo | spec.Euo

        G_given.Euc, G_given.Euo, H_given.Euc, H_given.Euo = Euc, Euo, Euc, Euo

    (G, H) = (
        preprocessing(
            G_given,
            H_given,
            mode,
            skip_subautomata=skip_SA,
            prefix_closed=prefix_closed,
        )
        if preprocess
        else (G_given, H_given)
    )

    if mode in [Mode.NORMAL, Mode.CONTROLLABLE_NORMAL]:
        G_obs = composition.observer(G)
        G_obs_names = G_obs.vs["name"]

    while True:
        deleted_states = set()
        if mode in [Mode.NORMAL, Mode.CONTROLLABLE_NORMAL]:
            bad_states_for_normality = check_normality(H, G_obs_names, MAX_PROCESSES)
            H.delete_vertices(bad_states_for_normality)
            deleted_states |= bad_states_for_normality
        if mode in [Mode.CONTROLLABLE, Mode.CONTROLLABLE_NORMAL]:
            inacc_states = unary.find_inacc(H)
            H.delete_vertices(inacc_states)
            bad_states_for_controllability = check_controllability(H, G, MAX_PROCESSES)
            H.delete_vertices(bad_states_for_controllability)
            deleted_states |= inacc_states | bad_states_for_controllability

        if prefix_closed:
            bad_states_to_trim = unary.find_inacc(H)
        else:
            bad_states_to_trim = unary.trim(H)
        H.delete_vertices(bad_states_to_trim)
        deleted_states |= bad_states_to_trim

        if H.vcount() == 0 or 0 in deleted_states:
            return DFA()
        elif len(deleted_states) == 0:
            H.vs["name"] = [str(i) for i in H.vs["name"]]
            return H


def check_normality(H: DFA, G_obs_names: DFA, MAX_PROCESSES: int) -> StateSet:
    """
    Check the normality condition of states H and returns states violating the condition.
    """
    if H.vcount() == 0:
        return set()

    bad_states = set()
    all_H_names = H.vs["name"]
    with ProcessPoolExecutor(max_workers=MAX_PROCESSES) as executor:
        futures = []
        chk = H.vcount() // MAX_PROCESSES
        for i, H_indecies in enumerate(
            pydash.chunk(range(H.vcount()), chk if chk > 0 else H.vcount(),)
        ):
            futures.append(
                executor.submit(
                    __find_bad_states_normal, H_indecies, G_obs_names, all_H_names, i
                )
            )

        for f in as_completed(futures):
            bad_states |= f.result()

    return bad_states


def __find_bad_states_normal(
    H_indecies: List[int], G_obs_names: List[str], H_names: List[str], barpos: int
) -> StateSet:
    bad_states = set()
    for index in tqdm(
        H_indecies,
        desc="Normality",
        disable=SHOW_PROGRESS is False,
        leave=False,
        position=barpos,
        mininterval=0.5,
    ):
        y = H_names[index]
        for q in G_obs_names:
            if y in q and not q <= set(H_names):
                bad_states.add(index)
                break

    return bad_states


def check_controllability(H: DFA, G: DFA, MAX_PROCESSES: int) -> StateSet:
    """
    Check the controllability condition of states in H and returns states violating the condition.
    """
    if H.vcount() == 0:
        return set()

    G_all_states = {v["name"]: [tuple(t) for t in v["out"]] for v in G.vs}
    H_all_states = {
        v["name"]: {"index": v.index, "out": [tuple(t) for t in v["out"]]} for v in H.vs
    }
    bad_states = set()
    Euc = G.Euc

    with ProcessPoolExecutor(max_workers=MAX_PROCESSES) as executor:
        futures = []
        chk = len(H_all_states) // MAX_PROCESSES
        for i, H_names in enumerate(
            pydash.chunk(
                list(H_all_states.keys()), chk if chk > 0 else len(H_all_states),
            )
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
    G_given: DFA,
    H_given: DFA,
    mode=Mode.CONTROLLABLE_NORMAL,
    skip_subautomata=False,
    prefix_closed=False,
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

    if mode == Mode.CONTROLLABLE:
        H, G = composition.strict_subautomata(H_given, G_given, skip_H_tilde=False)
        return G, H

    # 2. Construct G which is an SPA.
    G_obs = composition.observer(G_tilde)
    G = composition.parallel(G_tilde, G_obs)

    # 3. Extract H from G by deleteing all states ((x, y), z) of G where x = "dead".
    #       Names are (x, z) if skip_subautomata is True
    H = G.copy()
    if skip_subautomata:
        dead_states = [v.index for v in H.vs if v["name"][0] == "dead"]
    else:
        dead_states = [v.index for v in H.vs if v["name"][0][0] == "dead"]
    if not prefix_closed:

        H_given_name_marked = {v["name"]: v["marked"] for v in H_given.vs}
        if skip_subautomata:
            H.vs["marked"] = [
                H_given_name_marked.get(name[0], False) for name in H.vs["name"]
            ]
        else:
            H.vs["marked"] = [
                H_given_name_marked.get(name[0][0], False) for name in H.vs["name"]
            ]
    G.vs["name"] = [i for i in range(G.vcount())]
    H.vs["name"] = [i for i in range(H.vcount())]
    H.delete_vertices(dead_states)

    return G, H
