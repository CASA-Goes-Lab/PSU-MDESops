"""
Functions related to automaton languages
"""
import warnings

from DESops.automata.event.event import Event
from DESops.basic_operations.construct_complement import complement
from DESops.basic_operations.observer_comp import observer_comp_old
from DESops.basic_operations.product_NFA import product_NFA


def language_inclusion(g, h, Eo, return_num_states=False, return_unincluded_path=False):
    """
    Returns whether the language marked by g is a subset of the language marked by h

    Returns: opaque(, num_states)(, unincluded_path)

    Note: Only use this if the event sets are the same for both automata

    g, h: the two automata
    Eo: the set of observable events
    return_num_states: if True, the number of states in the product g x det(h)^c is returned as an additional value
    return_unincluded_path: if True, a list of observable events representing a path marked in g but not h is returned as an additional value
    """
    h_det = observer_comp_old(h, save_marked_states=True)
    complement(h_det, inplace=True, events=Eo)

    prod = product_NFA([g, h_det], save_marked_states=True)

    opaque = True
    for v in prod.vs:
        if v["marked"]:
            opaque = False
            violating_id = v.index
            break

    return_list = [opaque]

    if return_num_states:
        return_list.append(prod.vcount())

    if return_unincluded_path:
        if opaque:
            return_list.append(None)
        else:
            inits = [v.index for v in prod.vs if v["init"]]
            return_list.append(find_path_between(prod, inits, violating_id))

    if len(return_list) == 1:
        return return_list[0]
    else:
        return tuple(return_list)


def find_path_between(g, source, target):
    """
    Finds a shortest path from a source vertex to a target vertex
    Returns the list of event labels associated with the path
    If any vertex is in both a source and a target, returns an empty list
    If no target vertex can be reached from any source vertex, returns None

    g: the automaton
    source: a vertex ID or a list of vertex IDs
    target: a vertex ID or a list of vertex IDs

    Only one of source and target can be a list
    """
    with warnings.catch_warnings():
        # suppress warning when not every target is reachable from every source
        warnings.simplefilter("ignore")

        if isinstance(source, list):
            if isinstance(target, list):
                raise ValueError("Only one of source and target can be a list")

            # return empty list if source and target intersect
            if target in source:
                return []

            paths = g._graph.get_shortest_paths(
                target, source, mode="IN", output="epath"
            )

        else:
            # return empty list if source and target intersect
            if isinstance(target, list) and source in target:
                return []
            if source == target:
                return []

            paths = g._graph.get_shortest_paths(source, target, output="epath")

        # if all paths were empty, then target can't be reached from source
        if all([(path == []) for path in paths]):
            return None

        # get shortest non-empty path
        while [] in paths:
            paths.remove([])
        path = min(paths)

        path_labels = list()
        for i in path:
            t = g.es[i]["label"]
            if isinstance(t, Event):
                path_labels.append(t.label)
            else:
                path_labels.append(t)

        return path_labels
