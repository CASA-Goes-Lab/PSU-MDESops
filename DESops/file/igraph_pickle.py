# Keeping these here for organization
# but doesn't actually work, loses some edge info from write to read
# Not bothering to fix until after changes to event class

import igraph as ig


def write_pickle(filename, automata, compress=False):
    """
    Serialize Automata instance with pickle.
    Requires an output filename, e.g. filename = 'ex_out.pickle'
    compress (default False): if true, pickle with compression (use .picklez extension)
        If zipped, have to read_pickle w/ compress=True as well.
    Pickling is done via an igraph Graph method write_pickle.

    Need to package any relevant Automata info into igraph Graph object.
    """
    automata._graph["events"] = automata.events
    automata._graph["Euc"] = automata.Euc
    automata._graph["Euo"] = automata.Euo

    if hasattr(automata, "Ea"):
        automata._graph["Ea"] = automata.Ea

    if hasattr(automata, "X_crit"):
        automata._graph["X_crit"] = automata.X_crit

    automata._graph["type"] = automata.type

    # clear out attirubute since it can't be pickled
    # it is regenerated when reading pickle
    automata._graph.vs["out"] = None

    if not compress:
        automata._graph.write_pickle(filename)
    else:
        automata._graph.write_picklez(filename)


def read_pickle(filename, automata, compress=False):
    """
    Unserialize pickle file, obtaining original Automata.
    Requires an input filename, e.g. filename = 'ex_in.pickle'
    compress (default False): set true if converting a zipped pickle file e.g. picklez.
    Uses Read_pickle(z), an igraph Graph class method.

    Unpacks relevant Automata info stored in the igraph Graph object.
    """
    if not compress:
        automata._graph = ig.Graph.Read_Pickle(filename)
    else:
        automata._graph = ig.Graph.Read_Picklez(filename)
    # Retrieve any other releveant info from graph object e.g. obs/contr sets.
    automata.events = automata._graph["events"]
    automata.Euc.update(automata._graph["Euc"])
    automata.Euo.update(automata._graph["Euo"])

    if "Ea" in automata._graph.attributes():
        automata.Ea = automata._graph["Ea"]

    if "X_crit" in automata._graph.attributes():
        automata.X_crit = automata._graph["X_crit"]

    automata.type = automata._graph["type"]

    automata.vs = automata._graph.vs
    automata.es = automata._graph.es

    # regenerate out attribute
    automata.generate_out()
