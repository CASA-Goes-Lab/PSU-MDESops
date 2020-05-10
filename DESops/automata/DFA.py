from DESops.automata.automata import _Automata


class DFA(_Automata):
    """docstring for """

    def __init__(self, init=None, Euc=set(), Euo=set(), E=set()):
        super(DFA, self).__init__(init, Euc, Euo, E)

        # ADD SOME CONSTRAINTS ON CREATING THE OBJECT
        # LIKE NOT HAVING ATTRIBUTES PROB
        # CHECK IF IT IS DETERMINISTIC
        # AVOID MULTIPLE TESTS. IF IT IS A DFA COPY, DEFINED BASED ON OPERATIONS ON DFAS THEN NO NEED TO CHECK
        # ONLY CHECK IF init IS AN FRESH IGRAPH INSTANCE
        pass
