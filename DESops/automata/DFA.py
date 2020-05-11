import sys

import igraph as ig

from DESops.automata.automata import _Automata


class DFA(_Automata):
    """docstring for """

    def __init__(self, init=None, Euc=set(), Euo=set(), E=set()):
        super(DFA, self).__init__(init, Euc, Euo, E)
        if isinstance(init, ig.Graph):
            all_out = self.check_DFA()
            if not all(all_out):
                # TODO: THIS NEEDS TO BE TESTED
                sys.exit(
                    "ERROR:\nTRIED TO CREATE A DFA BUT IT IS A NFA\n State %s is nondeterministic"
                    % self._graph.vs["name"][all_out.index(False)]
                )
            elif "prob" in self._graph.es.attributes():
                sys.exit("ERROR:\nTRIED TO CREATE A DFA BUT IT IS A PFA")
        pass

        # ADD SOME CONSTRAINTS ON CREATING THE OBJECT
        # LIKE NOT HAVING ATTRIBUTES PROB
        # CHECK IF IT IS DETERMINISTIC
        # AVOID MULTIPLE TESTS. IF IT IS A DFA COPY, DEFINED BASED ON OPERATIONS ON DFAS THEN NO NEED TO CHECK
        # ONLY CHECK IF init IS A FRESH IGRAPH INSTANCE

    def add_edges(self, pair_list, labels):
        """
				Add an iterable of edges to the DFA instance.
				Calls the igraph Graph add_edges() method on the underlying graph
				object.
				Additionally adds label information as
				edge attributes.
				It checks if all transitions are deterministic

				Parameters:
				pair_list:
					an iterable to be passed to the igraph Graph add_edges() method,
					which accepts iterables of pairs or an EdgeSeq (see igraph documentation
					for more details on what is acceptable here).
				labels:
					(default None) optionally provide an iterable of labels to attach as
					keyword attributes. Should be parallel to pair_list (e.g., pair n of
					pair_list corresponding to label n of labels). To be stored in the "label" edge keyword attribute.
				Returns nothing.
				"""
        if labels:
            if len(pair_list) != len(labels):
                raise IncongruencyError("Length of pairs != length of labels")
            new_labels = list(self._graph.es["label"])
            new_labels.extend(labels)
        self._graph.add_edges(pair_list)
        if labels:
            self._graph.es["label"] = new_labels

    def check_DFA(self):
        out_event = lambda v: {el[1] for el in v}
        return [len(out_event(v)) == len(v) for v in self._graph.vs["out"]]
