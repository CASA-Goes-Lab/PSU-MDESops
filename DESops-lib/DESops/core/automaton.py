"""
Automaton: a single class for DFA, NFA and PFA, holding exactly
G = (X, E, delta, X0, Xm) plus the controllability/observability sets.

- X      -> self.states: list[State]; a state is identified by its index.
- E      -> self.events: set of events (may include events with no transition).
- delta  -> each State.out: dict[event, list[target index]].
- X0     -> self.init: set of initial state indices.
- Xm     -> State.marked.
- Euc, Euo -> self.Euc, self.Euo: the authoritative sets (events carry no
            controllability/observability flags of their own).

Whether an automaton is a DFA, NFA or PFA is a property (`kind`), derived
from its structure, not a separate class. PFA transition probabilities live
in State.prob, keyed by (event, target), so State.out has the same shape for
every kind and reachability-style algorithms need no special case for PFA.

Mutate through Automaton's methods (add_transition, remove_transition, ...),
not by editing State.out directly: the Automaton keeps a running count of
nondeterministic (state, event) pairs so `is_deterministic` is O(1), and a
direct edit would bypass it.

Replaces DESops.core.automata.Automata and its DFA/NFA/PFA subclasses; see
doc/logs/v2-automata-redesign.md. Until the rest of the library is ported,
from_automata()/to_automata() convert to and from those old classes.
"""

import warnings
from collections.abc import Iterable, Iterator
from typing import Any, Dict, List, Optional, Set, Tuple

Event_t = Any


class State:
    """One state of an Automaton. Holds its own outgoing transitions."""

    __slots__ = ("name", "marked", "out", "prob", "attrs")

    def __init__(self, name: Any, marked: bool = False, **attrs: Any):
        self.name = name
        self.marked = marked
        self.out: Dict[Event_t, List[int]] = {}
        self.prob: Dict[Tuple[Event_t, int], float] = {}
        self.attrs: Dict[str, Any] = dict(attrs)

    def __repr__(self):
        return f"State({self.name!r}, marked={self.marked}, out={self.out})"


class Automaton:
    def __init__(
        self,
        events: Iterable = (),
        Euc: Iterable = (),
        Euo: Iterable = (),
        probabilistic: bool = False,
    ):
        self.states: List[State] = []
        self.events: Set[Event_t] = set(events)
        self.Euc: Set[Event_t] = set(Euc)
        self.Euo: Set[Event_t] = set(Euo)
        self.events |= self.Euc | self.Euo
        self.init: Set[int] = set()
        self.probabilistic = probabilistic
        self._nondeterministic = 0
        self._incoming: Optional[List[Dict[Event_t, List[int]]]] = None

    # --- kind ---------------------------------------------------------------

    @property
    def is_probabilistic(self) -> bool:
        return self.probabilistic

    @property
    def is_deterministic(self) -> bool:
        return (
            not self.probabilistic
            and len(self.init) <= 1
            and self._nondeterministic == 0
        )

    @property
    def kind(self) -> str:
        if self.probabilistic:
            return "PFA"
        return "DFA" if self.is_deterministic else "NFA"

    # --- states ---------------------------------------------------------------

    @property
    def num_states(self) -> int:
        return len(self.states)

    def add_state(
        self, name: Any = None, marked: bool = False, init: bool = False, **attrs: Any
    ) -> int:
        """Add a state and return its index. Default name is the index as a str."""
        index = len(self.states)
        self.states.append(State(str(index) if name is None else name, marked, **attrs))
        if init:
            self.init.add(index)
        self._incoming = None
        return index

    def add_states(
        self,
        names: Iterable,
        marked: Optional[Iterable[bool]] = None,
    ) -> List[int]:
        names = list(names)
        marked = [False] * len(names) if marked is None else list(marked)
        if len(marked) != len(names):
            raise ValueError("names and marked must have the same length")
        return [self.add_state(n, m) for n, m in zip(names, marked)]

    def index_of(self, name: Any) -> int:
        """Index of the first state with this name (linear scan)."""
        for i, state in enumerate(self.states):
            if state.name == name:
                return i
        raise KeyError(name)

    def remove_states(self, indices: Iterable[int]) -> None:
        """Remove states (and every transition touching them), reindexing the rest."""
        to_remove = set(indices)
        keep = [i for i in range(len(self.states)) if i not in to_remove]
        new_index = {old: new for new, old in enumerate(keep)}

        new_states = []
        nondeterministic = 0
        for old in keep:
            state = self.states[old]
            out = {}
            for event, targets in state.out.items():
                kept = [new_index[t] for t in targets if t in new_index]
                if kept:
                    out[event] = kept
                    if len(kept) > 1:
                        nondeterministic += 1
            state.out = out
            state.prob = {
                (event, new_index[t]): p
                for (event, t), p in state.prob.items()
                if t in new_index
            }
            new_states.append(state)

        self.states = new_states
        self.init = {new_index[i] for i in self.init if i in new_index}
        self._nondeterministic = nondeterministic
        self._incoming = None

    # --- transitions ----------------------------------------------------------

    @property
    def num_transitions(self) -> int:
        return sum(len(targets) for s in self.states for targets in s.out.values())

    def add_transition(
        self, source: int, event: Event_t, target: int, prob: Optional[float] = None
    ) -> bool:
        """
        Add source --event--> target. If that exact transition already exists,
        warns, changes nothing, and returns False. The same (source, event)
        with a different target is allowed (that is what makes an NFA).
        Probabilistic automata require `prob`; others reject it.
        """
        if self.probabilistic and prob is None:
            raise ValueError("probabilistic automaton: transition needs a prob")
        if not self.probabilistic and prob is not None:
            raise ValueError("prob given, but automaton is not probabilistic")
        if not 0 <= target < len(self.states):
            raise IndexError(f"no state {target}")

        state = self.states[source]
        targets = state.out.setdefault(event, [])
        if target in targets:
            warnings.warn(
                f"duplicate transition {state.name!r} --{event}--> "
                f"{self.states[target].name!r} ignored",
                stacklevel=2,
            )
            return False
        targets.append(target)
        if len(targets) == 2:
            self._nondeterministic += 1
        if prob is not None:
            state.prob[(event, target)] = prob
        self.events.add(event)
        self._incoming = None
        return True

    def add_transitions(self, transitions: Iterable[Tuple]) -> None:
        """Add (source, event, target) or (source, event, target, prob) tuples."""
        for t in transitions:
            self.add_transition(*t)

    def remove_transition(self, source: int, event: Event_t, target: int) -> None:
        state = self.states[source]
        targets = state.out[event]
        targets.remove(target)
        if len(targets) == 1:
            self._nondeterministic -= 1
        elif not targets:
            del state.out[event]
        state.prob.pop((event, target), None)
        self._incoming = None

    def transitions(self) -> Iterator[Tuple[int, Event_t, int]]:
        """Every transition as (source, event, target)."""
        for source, state in enumerate(self.states):
            for event, targets in state.out.items():
                for target in targets:
                    yield source, event, target

    # --- queries used by BFS-style algorithms ---------------------------------

    def active_events(self, x: int) -> Set[Event_t]:
        return set(self.states[x].out)

    def next_states(self, x: int, event: Optional[Event_t] = None) -> List[int]:
        """Targets of `event` from x, or of every event if event is None."""
        out = self.states[x].out
        if event is not None:
            return list(out.get(event, ()))
        return [t for targets in out.values() for t in targets]

    def incoming(self, x: int) -> Dict[Event_t, List[int]]:
        """{event: [sources]} for transitions into x. Built once, on first use."""
        if self._incoming is None:
            incoming: List[Dict[Event_t, List[int]]] = [{} for _ in self.states]
            for source, event, target in self.transitions():
                incoming[target].setdefault(event, []).append(source)
            self._incoming = incoming
        return self._incoming[x]

    # --- misc -----------------------------------------------------------------

    def copy(self) -> "Automaton":
        other = Automaton(self.events, self.Euc, self.Euo, self.probabilistic)
        for state in self.states:
            new = State(state.name, state.marked, **state.attrs)
            new.out = {e: list(t) for e, t in state.out.items()}
            new.prob = dict(state.prob)
            other.states.append(new)
        other.init = set(self.init)
        other._nondeterministic = self._nondeterministic
        return other

    def __repr__(self):
        return (
            f"<{self.kind}: {self.num_states} states, "
            f"{self.num_transitions} transitions, {len(self.events)} events>"
        )

    def summary(self) -> str:
        lines = [repr(self), f"Euc: {self.Euc}", f"Euo: {self.Euo}"]
        for i, state in enumerate(self.states):
            flags = ("->" if i in self.init else "  ") + ("*" if state.marked else " ")
            lines.append(f"{flags} {i} {state.name}: {state.out}")
        return "\n".join(lines)

    # --- bridge to the old DFA/NFA/PFA classes --------------------------------

    @classmethod
    def from_automata(cls, g) -> "Automaton":
        """Build from an old DESops DFA/NFA/PFA (DESops.core.automata.Automata)."""
        from DESops.core.nfa import NFA
        from DESops.core.pfa import PFA

        data = g.to_data()
        probabilistic = isinstance(g, PFA)
        a = cls(g.events, g.Euc, g.Euo, probabilistic)

        init_flags = data.vertex_attrs.get("init")
        for i in range(data.num_states):
            attrs = {
                k: v[i]
                for k, v in data.vertex_attrs.items()
                if k != "init" and v[i] is not None
            }
            a.add_state(data.names[i], bool(data.marked[i]), **attrs)

        if isinstance(g, NFA) and init_flags is not None:
            a.init = {i for i, flag in enumerate(init_flags) if flag}
        elif data.num_states:
            a.init = {0}

        for k, (source, target) in enumerate(data.edges):
            prob = None
            if probabilistic:
                prob = data.probs[k] if data.probs is not None else None
                if prob is None:
                    raise ValueError(f"PFA transition {k} has no probability")
                prob = float(prob)
            a.add_transition(source, data.labels[k], target, prob)
        return a

    def to_automata(self):
        """
        Convert to an old DESops DFA/NFA/PFA, for operations not yet ported.
        The old DFA/PFA assume state 0 is initial, so for those kinds the
        initial state is moved to index 0.
        """
        from DESops.core.dfa import DFA
        from DESops.core.nfa import NFA
        from DESops.core.pfa import PFA

        kind = self.kind
        order = list(range(len(self.states)))
        if kind in ("DFA", "PFA") and self.init:
            if len(self.init) > 1:
                raise ValueError("the old PFA class supports exactly one initial state")
            (first,) = self.init
            order.remove(first)
            order.insert(0, first)
        position = {old: new for new, old in enumerate(order)}

        names = [self.states[i].name for i in order]
        marked = [self.states[i].marked for i in order]
        pairs, labels, probs = [], [], []
        for source, event, target in self.transitions():
            pairs.append((position[source], position[target]))
            labels.append(event)
            if self.probabilistic:
                probs.append(self.states[source].prob[(event, target)])

        if kind == "PFA":
            g = PFA()
            g.add_vertices(len(names), names, marked)
            g.add_edges(pairs, labels, probs)
        elif kind == "DFA":
            g = DFA()
            g.add_vertices(len(names), names, marked)
            g.add_edges(pairs, labels, check_DFA=False)
        else:
            g = NFA()
            init = [i in self.init for i in order]
            g.add_vertices(len(names), names, marked, init=init)
            g.add_edges(pairs, labels)

        # update(), not reassignment: g.UR holds a reference to the g.Euo set.
        g.events.update(self.events)
        g.Euc.update(self.Euc)
        g.Euo.update(self.Euo)
        return g
