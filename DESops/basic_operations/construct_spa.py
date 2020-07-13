# pylint: disable=C0103
"""
Process for constructing a state-partitioned automaton.
"""

from DESops.basic_operations import composition
from DESops.basic_operations.observer_comp import observer_comp
from DESops.basic_operations.parallel_comp import parallel_comp


def construct_spa(G_given, G_state_names, Euo=set()):
    """
    Construct state partitioned Automaton G from G_given (and G_o, observer of G_given).
    Optionally provide unobservable events (or can be found from G_given)

    G = G_given || Obs(G_given)
    """

    G_o = composition.observer(G_given)

    # G_given.vs["name"] = G_state_names
    G = parallel_comp([G_given, G_o])

    return G
