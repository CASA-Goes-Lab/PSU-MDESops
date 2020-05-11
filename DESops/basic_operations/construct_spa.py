# pylint: disable=C0103
"""
Process for constructing a state-partitioned automaton.
"""

from DESops.automata.automata_ctor import construct_automata
from DESops.basic_operations.observer_comp import observer_comp
from DESops.basic_operations.parallel_comp import parallel_comp


def construct_spa(G_given, G, Euo=set()):
    """
    Construct state partitioned Automaton G from G_given (and G_o, observer of G_given).
    Optionally provide unobservable events (or can be found from G_given)

    G = G_given || Obs(G_given)
    """
    G_o = construct_automata(G_given)
    if not Euo:
        # Safe using set() default arg, since it never gets modified.
        Euo = {edge["label"] for edge in G_given.es if not edge["obs"]}
    observer_comp(G_given, G_o, Euo, True, True)
    print(G_given.es["label"])
    print(G_o.es["label"])
    parallel_comp([G_given, G_o], G, True, True)
    names = [
        (G_given.vs["name"][pair[0]], G_o.vs["name"][pair[1]]) for pair in G.vs["name"]
    ]
    G.vs["name"] = names
