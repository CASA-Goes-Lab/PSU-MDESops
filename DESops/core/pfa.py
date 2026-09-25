from collections import namedtuple

from DESops import error
from DESops.core.automata import Automata
from DESops.core.event import Event
from DESops.error import IncongruencyError


class PFA(Automata):
    """docstring for """

    def __init__(self, init=None, Euc=set(), Euo=set(), E=set(), prob=None):
        super(PFA, self).__init__(init, Euc, Euo, E)

        if not prob and self.ecount() > 0:
            if self._data.probs is None:
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

            self._data.probs = list(prob)
            self._invalidate_graph()
        else:
            self._data.probs = []
            self._invalidate_graph()

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
        self._resync_data()
        if not isinstance(label, Event):
            # convert labels from str to Event
            label = Event(label)

        self._data.edges.append((source, target))
        self._data.labels.append(label)
        self.events.add(label)

        if self._data.probs is None:
            self._data.probs = [None] * (self._data.num_edges - 1)
        self._data.probs.append(prob)

        for key in self._data.edge_attrs:
            self._data.edge_attrs[key].append(None)

        self._invalidate_graph()

    def add_edges(self, pair_list, labels, probs, fill_out=True, **kwargs):
        self._resync_data()
        if len(pair_list) != len(labels):
            raise IncongruencyError("Length of pairs != length of labels")
        if len(pair_list) != len(probs):
            raise IncongruencyError("Length of pairs != length of probs")
        if kwargs:
            for key, value in kwargs.items():
                if len(pair_list) != len(value):
                    raise IncongruencyError(
                        "Length of pairs != length of kwarg {}".format(key)
                    )

        labels = [Event(l) if not isinstance(l, Event) else l for l in labels]
        self.events.update(labels)

        old_count = self._data.num_edges
        self._data.edges.extend(pair_list)
        self._data.labels.extend(labels)

        if self._data.probs is None:
            self._data.probs = [None] * old_count
        self._data.probs.extend(probs)

        for key, value in kwargs.items():
            if key not in self._data.edge_attrs:
                self._data.edge_attrs[key] = [None] * old_count
            self._data.edge_attrs[key].extend(value)
        for key in self._data.edge_attrs:
            if key not in kwargs:
                self._data.edge_attrs[key].extend([None] * len(pair_list))

        self._invalidate_graph()

    def generate_out(self):
        """
        PFA version of generate_out:
        Generates the "out" attribute for a graph
        >>> automata.vs["out"][v] // -> [(target vert, event transition), (...), ...]
        """
        adj_list = self._graph.get_inclist()
        # "prob" may not be declared yet the first time this runs during
        # __init__, before PFA's own constructor body has set self._data.probs
        # (see _build_graph()).
        has_prob = "prob" in self._graph.es.attributes()
        self.vs["out"] = [
            [
                (
                    self._graph.es[e].target,
                    self._graph.es[e]["label"],
                    self._graph.es[e]["prob"] if has_prob else None,
                )
                for e in row
            ]
            for row in adj_list
        ]
