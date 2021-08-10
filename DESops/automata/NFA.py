from typing import Set

from DESops.automata import automata
from DESops.automata.event import Event


class NFA(automata._Automata):
    def __init__(self, init=None, Euc=set(), Euo=set(), E=set()):
        super(NFA, self).__init__(init, Euc, Euo, E)

        if init is None:
            self.vs["init"] = []

        elif not isinstance(init, NFA):
            self.vs["init"] = False
            self.vs[0]["init"] = True

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
        self._graph.delete_vertices(vs)

        if not any([v["init"] for v in self.vs]):
            import warnings

            warnings.warn("All initial states deleted.")
            self._graph.delete_vertices([v.index for v in self.vs])
            return

        self.generate_out()

    def delete_vertices_no_warning(self, vs):
        """
        Deletes vertex seq vs.
        Uses igraph delete_vertices method.

        No warnings.
        """
        self._graph.delete_vertices(vs)

        self.generate_out()    

    def get_destinations(self, state: int, event: Event) -> Set[int]:
        return {out[0] for out in self.vs[state]["out"] if out[1] == event}

    def add_edge(self, source, target, label, prob=None, fill_out=True):
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
            # label = Event(label)
            pass
        self.es[self.ecount() - 1].update_attributes({"label": label})
        self.events.add(label)
        if prob:
            self.es[self.ecount() - 1].update_attributes({"prob": prob})

        if fill_out:
            out = self.vs[source]["out"]
            if out is not None:
                out.append(self.Out(target, label))
            else:
                out = [self.Out(target, label)]

            self.vs[source].update_attributes({"out": out})

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
        if len(pair_list) != len(labels):
            raise IncongruencyError("Length of pairs != length of labels")

        # labels = [Event(l) if not isinstance(l, Event) else l for l in labels]

        new_labels = list(self._graph.es["label"])
        new_labels.extend(labels)

        self.events.update(labels)

        if probs is not None:
            if len(pair_list) != len(probs):
                raise IncongruencyError("Length of pairs != length of probs")
            new_probs = list(self._graph.es["prob"])
            new_probs.extend(probs)

        if not pair_list:
            # no transitions provided
            return

        self._graph.add_edges(pair_list)

        if labels:
            self.es["label"] = new_labels

        if probs is not None:
            self.es["prob"] = new_probs

        if kwargs:
            for key, value in kwargs.items():
                if len(pair_list) != len(value):
                    raise IncongruencyError(
                        "Length fo pairs != length of kwarg {}".format(key)
                    )
                self.es[key] = value

        if fill_out:
            out_list = self.vs["out"]
            for label, pair in zip(labels, pair_list):
                out = out_list[pair[0]]
                if out is not None:
                    out.append(self.Out(pair[1], label))
                else:
                    out = [self.Out(pair[1], label)]
                out_list[pair[0]] = out
            self.vs["out"] = out_list
