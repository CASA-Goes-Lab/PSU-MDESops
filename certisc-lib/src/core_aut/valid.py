"""
ValidAutomaton: a read-only automaton that passed the verified checker.

To the user it reads like an Automaton: `num_states`, `states[i].name / .marked / .out`,
`events`, `Euc`, `Euo`, `init`, `transitions()`. Inside, it stores the automaton once, in the
encoded form the verified operations use (as tuples, so it cannot change after the check);
`states` and the sets are views computed from it on access, not second copies.

Made only by `validate(G)` (core_aut/trusted/wrapper.py) or by the readers (io_aut). "Valid"
can never go stale, and operations use it without checking or encoding again. To edit, take an
editable copy with `to_automaton()` and validate the result again.
"""

import sys
from types import MappingProxyType
from typing import Any, FrozenSet, Iterator, Mapping, Optional, Tuple

from core_aut.automaton import Automaton
from core_aut.trusted.encoding import Encoded, decode


class StateView:
    """A state of a ValidAutomaton, read-only: like State, with `name`, `marked`, and `out`
    (event -> tuple of target indices). `name` and `marked` are direct lookups; `out` is built
    from the encoding each time it is read (nothing is stored twice)."""

    __slots__ = ("_V", "_i")

    def __init__(self, V, i: int):
        object.__setattr__(self, "_V", V)
        object.__setattr__(self, "_i", i)

    @property
    def name(self) -> Any:
        return self._V._names[self._i]

    @property
    def marked(self) -> bool:
        return self._V._enc.marked[self._i]

    @property
    def out(self) -> Mapping[Any, Tuple[int, ...]]:
        V, i = self._V, self._i
        enc = V._enc
        out = {}
        for k in range(enc.start[i], enc.start[i + 1]):     # one block, sorted by event
            out.setdefault(V._event_of[enc.evt[k]], []).append(enc.dst[k])
        return MappingProxyType({e: tuple(t) for e, t in out.items()})

    def __setattr__(self, name, value):
        raise AttributeError("states of a ValidAutomaton are read-only")

    def __repr__(self):
        return f"State({self.name!r}, marked={self.marked}, out={dict(self.out)})"


class _States:
    """The sequence V.states: V.states[i] is a StateView (made on access; cheap)."""

    __slots__ = ("_V",)

    def __init__(self, V):
        self._V = V

    def __len__(self) -> int:
        return self._V.num_states

    def __getitem__(self, i: int) -> StateView:
        n = self._V.num_states
        if not -n <= i < n:
            raise IndexError("state index out of range")
        return StateView(self._V, i % n)

    def __iter__(self):
        return (StateView(self._V, i) for i in range(self._V.num_states))

    def __repr__(self):
        return repr(list(self))


class ValidAutomaton:
    """A validated automaton (read-only). Create it with validate(G) or io_aut.read_aut."""

    __slots__ = ("_enc", "_event_of", "_number", "_names", "_deterministic", "_active")

    def __init__(self, *args, **kwargs):
        raise TypeError("ValidAutomaton is made by validate(G) or a reader (io_aut), "
                        "not directly")

    @classmethod
    def _make(cls, enc: Encoded, event_of: list, names: list, deterministic: bool):
        """Internal: called only after the verified checker accepted `enc`."""
        self = object.__new__(cls)
        frozen = Encoded(enc.n, enc.m, tuple(enc.in_E), tuple(enc.in_Euc), tuple(enc.in_Euo),
                         tuple(enc.init), tuple(enc.marked), tuple(enc.start), tuple(enc.evt),
                         tuple(enc.dst))
        object.__setattr__(self, "_enc", frozen)
        object.__setattr__(self, "_event_of", tuple(event_of))
        object.__setattr__(self, "_number", {e: k for k, e in enumerate(event_of)})
        object.__setattr__(self, "_names", tuple(names))
        object.__setattr__(self, "_deterministic", deterministic)
        object.__setattr__(self, "_active", None)       # active-event index, built on first use
        return self

    def __setattr__(self, name, value):
        raise AttributeError("ValidAutomaton is read-only; use to_automaton() to edit a copy")

    # --- reading -----------------------------------------------------------------------------

    @property
    def num_states(self) -> int:
        return self._enc.n

    @property
    def states(self) -> _States:
        """Read-only states, like Automaton.states: V.states[i].name, .marked, .out."""
        return _States(self)

    @property
    def names(self) -> Tuple[Any, ...]:
        """State names; state i is names[i]."""
        return self._names

    def index_of(self, name: Any) -> int:
        """The index of the state called `name` (the first, if names repeat)."""
        return self._names.index(name)

    @property
    def events(self) -> FrozenSet[Any]:
        return frozenset(e for k, e in enumerate(self._event_of) if self._enc.in_E[k])

    @property
    def Euc(self) -> FrozenSet[Any]:
        return frozenset(e for k, e in enumerate(self._event_of) if self._enc.in_Euc[k])

    @property
    def Euo(self) -> FrozenSet[Any]:
        return frozenset(e for k, e in enumerate(self._event_of) if self._enc.in_Euo[k])

    @property
    def init(self) -> FrozenSet[int]:
        return frozenset(x for x in range(self._enc.n) if self._enc.init[x])

    @property
    def marked(self) -> FrozenSet[int]:
        return frozenset(x for x in range(self._enc.n) if self._enc.marked[x])

    @property
    def is_deterministic(self) -> bool:
        """Decided by the verified checker (at most one initial state, and no state with two
        transitions on one event)."""
        return self._deterministic

    def transitions(self) -> Iterator[Tuple[int, Any, int]]:
        """(source, event, target) for every transition, grouped by source, sorted by event."""
        enc = self._enc
        for x in range(enc.n):
            for k in range(enc.start[x], enc.start[x + 1]):
                yield x, self._event_of[enc.evt[k]], enc.dst[k]

    def to_automaton(self) -> Automaton:
        """An editable copy (validate it again after editing)."""
        return decode(self._enc, list(self._event_of), list(self._names))

    def __repr__(self):
        return (f"ValidAutomaton({self.num_states} states, {len(self.events)} events"
                f"{', deterministic' if self._deterministic else ''})")

    # --- printing ----------------------------------------------------------------------------

    _PRINT_LIMIT = 20          # states shown by print(V); V.show() shows all

    def _format(self, max_states: Optional[int]) -> str:
        """The readable layout of show() / print(): sets first, then one state per line."""
        def names(xs):
            return ", ".join(str(self._names[x]) for x in sorted(xs)) or "(none)"

        def labels(es):
            return ", ".join(sorted(map(str, es))) or "(none)"

        lines = [repr(self),
                 f"  events:         {labels(self.events)}",
                 f"  uncontrollable: {labels(self.Euc)}",
                 f"  unobservable:   {labels(self.Euo)}",
                 f"  initial:        {names(self.init)}",
                 f"  marked:         {names(self.marked)}",
                 "  transitions:"]
        n = self.num_states
        shown = n if max_states is None else min(n, max_states)
        width = max((len(str(self._names[x])) for x in range(shown)), default=0)
        for x in range(shown):
            moves = []
            for e, targets in self.states[x].out.items():
                ts = [str(self._names[t]) for t in targets]
                moves.append(f"{e} -> {ts[0]}" if len(ts) == 1 else f"{e} -> {{{', '.join(ts)}}}")
            lines.append(f"    {str(self._names[x]).ljust(width)} : {', '.join(moves) or '(none)'}")
        if shown < n:
            lines.append(f"    ... {n - shown} more states (V.show() prints all)")
        return "\n".join(lines)

    def __str__(self) -> str:
        """print(V): the readable layout, up to 20 states."""
        return self._format(self._PRINT_LIMIT)

    def show(self, max_states: Optional[int] = None, file=None) -> None:
        """Print the automaton readably: the event sets, initial and marked states, then each
        state with its transitions (`event -> target`, or `event -> {t1, t2}` when
        nondeterministic). All states by default, or the first `max_states`."""
        print(self._format(max_states), file=file if file is not None else sys.stdout)

    # --- for the operations (internal) -------------------------------------------------------

    def _encoding(self) -> Encoded:
        return self._enc

    def _active_index(self) -> Tuple[Tuple[int, ...], Tuple[int, ...]]:
        """The active-event index (A, H) (core_aut/trusted/active_index.py): built and checked by
        the verified checker on first use, then kept (it depends only on the frozen encoding)."""
        if self._active is None:
            from core_aut.trusted.active_index import checked_active_index
            object.__setattr__(self, "_active", checked_active_index(self._enc))
        return self._active

    def _event_number(self, event: Any) -> Optional[int]:
        """The number of `event` in the encoding, or None if no transition or set uses it."""
        return self._number.get(event)
