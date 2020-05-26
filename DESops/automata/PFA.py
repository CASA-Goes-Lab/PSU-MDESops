import sys
from DESops.automata.automata import _Automata

class PFA(_Automata):
    """docstring for """

    def __init__(self, init=None, Euc=set(), Euo=set(), E=set(), prob=None):
        super(PFA, self).__init__(init, Euc, Euo, E)

        if not prob and self.ecount() > 0:
            if "prob" not in self.es.attributes():
                import warnings
                #sys.exit("ERROR: prob attribute not defined for type PFA")
                warnings.warn("prob attribute not defined for type PFA, setting to default")

        elif prob:
            if len(prob) != self.ecount():
                sys.exit("ERROR: {0} probabilities specified does not match {1} graph ecount".format(len(prob), self.ecount()))

            self._graph.es["prob"] = prob.copy()
        else:
            self._graph.es["prob"] = []
            
        
    def add_edges(self, pair_list, labels, probs):
  
        if len(pair_list) != len(labels):
            raise IncongruencyError("Length of pairs != length of labels")
        new_labels = list(self._graph.es["label"])
        new_labels.extend(labels)
        
        self._graph.add_edges(pair_list)

        self._graph.es["label"] = new_labels

        if len(pair_list) != len(probs):
            raise IncongruencyError("Length of pairs != length of probs")
        new_probs = list(self._graph.es["prob"])
        new_probs.extend(probs)

        self._graph.es["prob"] = new_probs
