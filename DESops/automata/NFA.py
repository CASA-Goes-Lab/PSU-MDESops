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

    def copy(self):
        """
        Copy from self to other, as in:
        >>> other = self.copy()
        """
        A = PFA(self)
        return A

    def delete_vertices(self, vs):
        self._graph.delete_vertices(vs)

        if not any([v["init"] for v in self.vs]):
            import warnings

            warnings.warn("All initial states deleted.")
            self._graph.delete_vertices([v.index for v in self.vs])
            return

        for state in self.vs:
            new_out = [
                automata.Out_Tuple(e.target, e["label"]) for e in state.out_edges()
            ]
            self.vs[state.index].update_attributes({"out": new_out})

    def get_destinations(self, state: int, event: Event) -> Set[int]:
        return {out[0] for out in self.vs[state]["out"] if out[1] == event}
