import sys
from DESops.automata.automata import _Automata

class PFA(_Automata):
    """docstring for """

    def __init__(self, init=None, Euc=set(), Euo=set(), E=set(), prob=list()):
        super(PFA, self).__init__(init, Euc, Euo, E)

        if not prob:
            if "prob" not in init.es.attributes():
                import warnings
                #sys.exit("ERROR: prob attribute not defined for type PFA")
                warnings.warn("prob attribute not defined for type PFA, setting to default")

        else:
            if len(prob) != self.ecount():
                sys.exit("ERROR: {0} probabilities specified does not match {1} graph ecount".format(len(prob), self.ecount()))

            self._graph.es["prob"] = prob.copy()
