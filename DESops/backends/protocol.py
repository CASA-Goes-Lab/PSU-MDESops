"""
Backend-agnostic automaton representation.

AutomatonData is plain Python data (lists, sets, tuples) with no
dependency on any graph library. It is the intended long-term source of
truth for DESops.core.automata.Automata; today it is a read-only
snapshot (see Automata.to_data()) built on demand from the underlying
igraph.Graph. A future change will make it the primary storage and
build igraph views from it instead, without changing this shape.

See doc/scoping-report.md for the migration plan.
"""

from dataclasses import dataclass
from typing import Any, List, Optional, Set, Tuple

# Transition labels are typically DESops.core.event.Event instances, not
# plain strings, but nothing here depends on that -- any hashable value
# works.
Label = Any


@dataclass
class AutomatonData:
    """Plain-data snapshot of an automaton's states, transitions, and events.

    Attributes
    ----------
    names : list[str]
        State names. State ids are positions in this list.
    marked : list[bool]
        Per-state marking, parallel to `names`.
    edges : list[tuple[int, int]]
        (source, target) state id pairs. Edge ids are positions in this list.
    labels : list[Label]
        Per-edge transition label, parallel to `edges`.
    events : set[Label]
        The set of all event labels used across `labels`.
    probs : list[float] or None
        Per-edge transition probability, parallel to `edges`. None unless
        the automaton is stochastic (PFA).
    """

    names: List[str]
    marked: List[bool]
    edges: List[Tuple[int, int]]
    labels: List[Label]
    events: Set[Label]
    probs: Optional[List[float]] = None

    @property
    def num_states(self) -> int:
        return len(self.names)

    @property
    def num_edges(self) -> int:
        return len(self.edges)
