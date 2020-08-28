from collections import namedtuple

from DESops import error
from DESops.automata.automata import _Automata
from DESops.automata.event import Event


class PFA(_Automata):
    """docstring for """

    def __init__(self, init=None, Euc=set(), Euo=set(), E=set(), prob=None):
        super(PFA, self).__init__(init, Euc, Euo, E)

        if not prob and self.ecount() > 0:
            if "prob" not in self.es.attributes():
                import warnings

                warnings.warn(
                    "prob attribute not defined for type PFA, setting to default"
                )

        elif prob:
            if len(prob) != self.ecount():
                raise error.IncongruencyError(
                    "ERROR: {0} probabilities specified does not match {1} graph ecount".format(
                        len(prob), self.ecount()
                    )
                )

            self._graph.es["prob"] = prob.copy()
        else:
            self._graph.es["prob"] = []

        self.Out = namedtuple("Out", ["target", "label", "prob"])

        self.type = "PFA"

    def copy(self):
        """
        Copy from self to other, as in:
        >>> other = self.copy()
        """
        A = PFA(self)
        return A

    def add_edge(self, source, target, label, prob, fill_out=True):
        """
        Adds an edge to the Automata instance. Edge is created across pair, a tuple
        of vertex indices according to the igraph Graph add_edge() method.
        Additionlly adds label and probability information as edge attributes, if
        they are optionally provided.

        Note: much faster to add multiple edges at once using add_edges

        Parameters:
        source, target: vertex indicies. See igraph documentation of
            the add_edge() method for more details on what is acceptable here.
        label:  optionally provide label for this transition, to be stored
            in the "label" edge keyword attribute.
        prob: (default None) optionally provide probability for this transition (indicating
            stochastic transition), to be stored in the "prob" edge keyword attribute.
        """
        self._graph.add_edge(source, target)
        if not isinstance(label, Event):
            # convert labels from str to Event
            label = Event(label)
        self.es[self.ecount() - 1].update_attributes({"label": label})

        self.events.add(label)
        self.es[self.ecount() - 1].update_attributes({"prob": prob})

        if fill_out:
            out = self.vs[source]["out"]
            if out is not None:
                out.append(self.Out(target, label))
            else:
                out = [self.Out(target, label)]

            self.vs[source].update_attributes({"out": out})

    def add_edges(self, pair_list, labels, probs, fill_out=True, **kwargs):

        if len(pair_list) != len(labels):
            raise IncongruencyError("Length of pairs != length of labels")
        labels = [Event(l) if not isinstance(l, Event) else l for l in labels]
        self.events.update(labels)
        new_labels = list(self._graph.es["label"])
        new_labels.extend(labels)

        self._graph.add_edges(pair_list)

        self._graph.es["label"] = new_labels

        if len(pair_list) != len(probs):
            raise IncongruencyError("Length of pairs != length of probs")
        new_probs = list(self._graph.es["prob"])
        new_probs.extend(probs)

        self._graph.es["prob"] = new_probs

        if kwargs:
            for key, value in kwargs.items():
                if len(pair_list) != len(value):
                    raise IncongruencyError(
                        "Length of pairs != length of kwarg {}".format(key)
                    )
                self.es[key] = value

        if fill_out:
            out_list = self.vs["out"]
            for label, pair, prob in zip(labels, pair_list, probs):
                out = out_list[pair[0]]
                if out is not None:
                    out.append(self.Out(pair[1], label, prob))
                else:
                    out = [self.Out(pair[1], label, prob)]
            self.vs["out"] = out_list

    def generate_out(self):
        """
        PFA version of generate_out:
        Generates the "out" attribute for a graph
        >>> automata.vs["out"][v] // -> [(target vert, event transition), (...), ...]
        """
        adj_list = self._graph.get_inclist()
        self.vs["out"] = [
            [
                (
                    self._graph.es[e].target,
                    self._graph.es[e]["label"],
                    self._graph.es[e]["prob"],
                )
                for e in row
            ]
            for row in adj_list
        ]
