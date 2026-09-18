from typing import Set

from DESops.core import automata
from DESops.core.event import Event
from DESops.error import IncongruencyError


class NFA(automata.Automata):
    def __init__(self, init=None, Euc=set(), Euo=set(), E=set()):
        super(NFA, self).__init__(init, Euc, Euo, E)

        if init is None:
            self._data.vertex_attrs["init"] = []

        elif not isinstance(init, NFA):
            self._data.vertex_attrs["init"] = [False] * self._data.num_states
            self._data.vertex_attrs["init"][0] = True

        self._sync_graph()

        self.type = "NFA"

    def copy(self):
        """
        Copy from self to other, as in:
        >>> other = self.copy()
        """
        A = NFA(self)
        return A

    def delete_vertices(self, vs):
        """
        Deletes vertex seq vs.
        Uses igraph delete_vertices method.

        Updates out attr: since there is no default "in" attribute,
        out is regenerated entirely.

        Faster to use fewer delete_vertices() calls with larger inputs vs
        than multiple calls with smaller inputs.
        """
        self._resync_data()
        self._remove_vertices_by_index(automata._vertex_indices(vs))

        if not any(self._data.vertex_attrs.get("init", [])):
            import warnings

            warnings.warn("All initial states deleted.")
            self._remove_vertices_by_index(range(self._data.num_states))

    def delete_vertices_no_warning(self, vs):
        """
        Deletes vertex seq vs.
        Uses igraph delete_vertices method.

        No warnings.
        """
        self._resync_data()
        self._remove_vertices_by_index(automata._vertex_indices(vs))

    def get_destinations(self, state: int, event: Event) -> Set[int]:
        return {out[0] for out in self.vs[state]["out"] if out[1] == event}

    def add_edge(self, source, target, label, prob=None, fill_out=True, **kwargs):
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
        self._data.edges.append((source, target))
        self._data.labels.append(label)
        self.events.add(label)

        if prob:
            if self._data.probs is None:
                self._data.probs = [None] * (self._data.num_edges - 1)
            self._data.probs.append(prob)
        elif self._data.probs is not None:
            self._data.probs.append(None)

        for key in self._data.edge_attrs:
            if key not in kwargs:
                self._data.edge_attrs[key].append(None)
        for key, value in kwargs.items():
            if key not in self._data.edge_attrs:
                self._data.edge_attrs[key] = [None] * (self._data.num_edges - 1)
            self._data.edge_attrs[key].append(value)

        self._sync_graph()
        return self.es[self._data.num_edges - 1]

    def add_edges(self, pair_list, labels, probs=None, fill_out=True, **kwargs):
        """
        Add an iterable of edges to the Automata instance.
        Calls the igraph Graph add_edges() method on the underlying graph
        object. Additionally adds label and probability information as
        edge attributes, if they are optionally provided as parallel iterables.

        Parameters:
        pair_list: an iterable to be passed to the igraph Graph add_edges() method,
            which accepts iterables of pairs or an EdgeSeq (see igraph documentation
            for more details on what is acceptable here).
        labels: optionally provide an iterable of labels to attach as
            keyword attributes. Should be parallel to pair_list (e.g., pair n of
            pair_list corresponding to label n of labels). To be stored in the "label"
            edge keyword attribute.
        probs: (default None) optionally provide an iterable of probabilities to attach
            as keyword attributes (indicating stochastic transitions). Should be
            parallel to pair_list (e.g., pair n of pair_list corresponds to probability
            n of probs). To be stored in the "prob" edge keyword attribute.

        Returns nothing.
        """
        self._resync_data()
        if len(pair_list) != len(labels):
            raise IncongruencyError("Length of pairs != length of labels")

        # labels = [Event(l) if not isinstance(l, Event) else l for l in labels]

        self.events.update(labels)

        if probs is not None:
            if len(pair_list) != len(probs):
                raise IncongruencyError("Length of pairs != length of probs")

        if kwargs:
            for key, value in kwargs.items():
                if len(pair_list) != len(value):
                    raise IncongruencyError(
                        "Length fo pairs != length of kwarg {}".format(key)
                    )

        if not pair_list:
            # no transitions provided
            return

        old_count = self._data.num_edges
        self._data.edges.extend(pair_list)
        self._data.labels.extend(labels)

        if probs is not None:
            if self._data.probs is None:
                self._data.probs = [None] * old_count
            self._data.probs.extend(probs)
        elif self._data.probs is not None:
            self._data.probs.extend([None] * len(pair_list))

        for key, value in kwargs.items():
            if key not in self._data.edge_attrs:
                self._data.edge_attrs[key] = [None] * old_count
            self._data.edge_attrs[key].extend(value)
        for key in self._data.edge_attrs:
            if key not in kwargs:
                self._data.edge_attrs[key].extend([None] * len(pair_list))

        self._sync_graph()
        return self.es[old_count : old_count + len(pair_list)]

    def trans(self, source, event):
        """
        Return the set of target vertex indices reached when the given event occurs from the given source vertex index
        """
        targets = set()
        for out in self.vs[source]["out"]:
            if out.label == event:
                targets.add(out.target)
        return targets
