from typing import Set

from DESops.automata.automata import _Automata
from DESops.automata.event import Event


class NFA(_Automata):
    def __init__(self, init=None, Euc=set(), Euo=set(), E=set()):
        super(NFA, self).__init__(init, Euc, Euo)
        pass

    def get_destinations(self, state: int, event: Event) -> Set[int]:
        return {out[0] for out in self.vs[state]["out"] if out[1] == event}
