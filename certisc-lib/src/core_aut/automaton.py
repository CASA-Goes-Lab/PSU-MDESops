"""
Automaton: a plain container for G = (X, E, delta, X0, Xm) plus Euc and Euo.

Trusted, not verified. It only holds data and checks nothing; whether an automaton is valid is
decided by the verified checker (core_aut.wrapper.check_or_raise). Fields, as in
certisc-proof/spec/automaton.md:

- X      -> self.states: list[State]; a state is identified by its index.
- E      -> self.events: set of events (may include events with no transition).
- delta  -> each State.out: dict[event, list[target index]].
- X0     -> self.init: set of initial state indices.
- Xm     -> State.marked (bool).
- Euc, Euo -> self.Euc, self.Euo.

Same field layout as the legacy DESops.core.automaton.Automaton, so the two can be compared.
"""

from typing import Any, Dict, Iterable, Iterator, List, Set, Tuple


class State:
    """One state: its name, marking and outgoing transitions."""

    __slots__ = ("name", "marked", "out")

    def __init__(self, name: Any, marked: bool = False):
        self.name = name
        self.marked = marked
        self.out: Dict[Any, List[int]] = {}

    def __repr__(self):
        return f"State({self.name!r}, marked={self.marked}, out={self.out})"


class Automaton:
    def __init__(self, events: Iterable = (), Euc: Iterable = (), Euo: Iterable = ()):
        self.states: List[State] = []
        self.Euc: Set[Any] = set(Euc)
        self.Euo: Set[Any] = set(Euo)
        self.events: Set[Any] = set(events) | self.Euc | self.Euo
        self.init: Set[int] = set()

    @property
    def num_states(self) -> int:
        return len(self.states)

    def add_state(self, name: Any = None, marked: bool = False, init: bool = False) -> int:
        """Add a state and return its index. Default name is the index as a str."""
        index = len(self.states)
        self.states.append(State(str(index) if name is None else name, marked))
        if init:
            self.init.add(index)
        return index

    def add_transition(self, source: int, event: Any, target: int) -> bool:
        """Add source --event--> target. Returns False (and changes nothing) if it exists."""
        targets = self.states[source].out.setdefault(event, [])
        if target in targets:
            return False
        targets.append(target)
        return True

    def transitions(self) -> Iterator[Tuple[int, Any, int]]:
        for x, state in enumerate(self.states):
            for event, targets in state.out.items():
                for t in targets:
                    yield x, event, t

    def __repr__(self):
        return f"Automaton({self.num_states} states, {len(self.events)} events)"
