"""
Backend-agnostic automaton representation.

AutomatonData is plain Python data (lists, dicts, sets, tuples) with no
dependency on any graph library. It is the intended long-term source of
truth for DESops.core.automata.Automata; today it is a read-only
snapshot (see Automata.to_data()) built on demand from the underlying
igraph.Graph. A future change will make it the primary storage and
build igraph views from it instead, without changing this shape.

See doc/logs/v2-igraph-decoupling.md for the migration plan.
"""

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Set, Tuple

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
    vertex_attrs : dict[str, list]
        Extra per-state attributes beyond name/marked (e.g. "init",
        "forbidden", or dynamic proposition names read from a .wmod
        file), keyed by attribute name, each value list parallel to
        `names`. Mirrors igraph's own free-form vertex attributes.
    edge_attrs : dict[str, list]
        Extra per-transition attributes beyond label/prob, keyed by
        attribute name, each value list parallel to `edges`.
    """

    names: List[str]
    marked: List[bool]
    edges: List[Tuple[int, int]]
    labels: List[Label]
    events: Set[Label]
    probs: Optional[List[float]] = None
    vertex_attrs: Dict[str, list] = field(default_factory=dict)
    edge_attrs: Dict[str, list] = field(default_factory=dict)

    @property
    def num_states(self) -> int:
        return len(self.names)

    @property
    def num_edges(self) -> int:
        return len(self.edges)
