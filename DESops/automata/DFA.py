import sys

import igraph as ig

from DESops.automata.automata import _Automata
from DESops.automata.event.event import Event
from DESops.error import IncongruencyError

# MUST HAVE A DEFINITION NFA TO DFA
# CHECKS IF THERE IS NONDETERMINISM
# IF NO NONDETERMINISM THEN OUTPUTS A COPY OF THE NFA
# IF THERE IS NONDETERMINISM THEN OUTPUTS THE DETERMINIZING OF NFA


class DFA(_Automata):
    """docstring for """

    def __init__(
        self, init=None, Euc=set(), Euo=set(), E=set(), check_DFA=True, **args
    ):
        super(DFA, self).__init__(init, Euc, Euo, E)
        if isinstance(init, ig.Graph) and check_DFA:
            all_out = self.check_DFA()
            if not all(all_out):
                sys.exit(
                    "ERROR:\nTRIED TO CREATE A DFA BUT IT IS A NFA\n State %s is nondeterministic"
                    % self._graph.vs["name"][all_out.index(False)]
                )
            elif "prob" in self._graph.es.attributes():
                sys.exit("ERROR:\nTRIED TO CREATE A DFA BUT IT IS A PFA")
        # if symbolic arguments
        self.symbolic = dict()
        if args:
            for key, value in args.items():
                if key == "bdd":
                    self.symbolic[key] = value
                elif key == "transitions":
                    self.symbolic[key] = value
                elif key == "uctr":
                    self.symbolic[key] = value
                elif key == "uobs":
                    self.symbolic[key] = value
                elif key == "states":
                    self.symbolic[key] = value[1]
                    self.symbolic["states_dict"] = value[0]
                elif key == "events":
                    self.symbolic[key] = value[1]
                    self.symbolic["events_dict"] = value[0]
                else:
                    sys.exit(
                        "ERROR:\nTRIED TO CREATE SYMBOLIC DFA ARG ERROR\nARG KEYS ARE:bdd,transitions,uctr,uobs,states,events"
                    )

        pass

        # ADD SOME CONSTRAINTS ON CREATING THE OBJECT
        # LIKE NOT HAVING ATTRIBUTES PROB
        # CHECK IF IT IS DETERMINISTIC
        # AVOID MULTIPLE TESTS. IF IT IS A DFA COPY, DEFINED BASED ON OPERATIONS ON DFAS THEN NO NEED TO CHECK
        # ONLY CHECK IF init IS A FRESH IGRAPH INSTANCE

    def add_edges(self, pair_list, labels, check_DFA=True, fill_out=True):
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
            provide an iterable of labels to attach as
            keyword attributes. Should be parallel to pair_list (e.g., pair n of
            pair_list corresponding to label n of labels). To be stored in the "label" edge keyword attribute.
        Returns nothing.
        """
        # WE SHOULD ADD A WARNING IF IT CHECK_DFA IS DISABLE FOR UNKNOWN FUNCTIONS
        # IF THE CALLER IS PARALLEL COMP, OBSERVER, ETC, THEN NOT WARNING SHOULD BE PRINTED
        # THIS CAN BE DONE BY CHECKING THE FUNCTION CALLER

        if len(pair_list) != len(labels):
            raise IncongruencyError("Length of pairs != length of labels")

        if not pair_list:
            # no transitions provided
            return

        if isinstance(labels[0], str):
            # convert labels from str to Event
            labels = [Event(s) for s in labels]

        new_labels = list(self._graph.es["label"])
        new_labels.extend(labels)
        self.events.update(labels)
        self._graph.add_edges(pair_list)
        self._graph.es["label"] = new_labels

        if fill_out:
            self.generate_out()

        if check_DFA:
            dict_out = dict()
            for (i, p) in enumerate(pair_list):
                if p[0] not in dict_out.keys():
                    dict_out[p[0]] = list()
                    dict_out[p[0]].append(labels[i])
                else:
                    dict_out[p[0]].append(labels[i])
            out_event = [
                True if len(set(v)) == len(v) else False for v in dict_out.values()
            ]
            if not all(out_event):
                # TODO: THIS NEEDS TO BE TESTED
                sys.exit("ERROR:\nTRIED TO CREATE A DFA BUT IT IS A NFA")

    def check_DFA(self):
        out_event = lambda v: {el[1] for el in v}
        return [len(out_event(v)) == len(v) for v in self._graph.vs["out"]]
