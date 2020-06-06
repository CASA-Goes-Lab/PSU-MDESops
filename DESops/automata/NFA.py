from DESops.automata.automata import _Automata


class NFA(_Automata):
    def __init__(self, init=None, Euc=set(), Euo=set(), E=set()):
        super(NFA, self).__init__(init, Euc, Euo)
        pass
