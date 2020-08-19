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

    def get_destinations(self, state: int, event: Event) -> Set[int]:
        return {out[0] for out in self.vs[state]["out"] if out[1] == event}
