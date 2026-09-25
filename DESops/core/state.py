"""
State: a mutable, self-contained representation of one automaton state,
owning its own outgoing and incoming transitions.

This is a working representation used *inside* the native (pure Python,
no igraph) implementations of core/operations/ algorithms -- both for
reading an input automaton (via states_from_data(), built once from
AutomatonData) and for incrementally building up an output automaton
during a BFS-style construction (composition.parallel, composition.observer,
etc.), replacing ad-hoc per-operation bookkeeping (parallel dicts of
names/marked/edges indexed by a separately-tracked vertex counter) with a
single list of States that already knows its own adjacency.

It is not part of Automata's own storage: Automata still stores
AutomatonData (backends/protocol.py) as its source of truth, with
self._graph/.vs/.es rebuilt from it on every mutation (see
DESops.core.automata.Automata._sync_graph). A State list built here is a
snapshot/scratch structure for the duration of one native operation call;
mutating it does not write back to any Automata instance. Persisting
State-based adjacency on Automata itself (so it survives across separate
operation calls, closing the "native re-derives adjacency every call"
performance gap measured in doc/logs/v2-igraph-decoupling.md) would mean
Automata's own mutation methods maintaining it incrementally -- a much
larger change to code that's already been carefully migrated and tested
once. Deliberately out of scope here; see that log for the reasoning.

Lives in core/ (alongside Event, DFA, NFA, PFA) rather than backends/,
since State represents a domain concept -- an automaton state -- not
storage/conversion plumbing the way AutomatonData and igraph_backend.py
are. It's built from and depends on the storage layer (AutomatonData,
imported from backends/protocol.py below), the same direction
core/automata.py already depends on backends/.
"""

from typing import Any, Dict, List, Optional

from DESops.backends.protocol import AutomatonData, Label


class Transition:
    """
    One directed transition, as recorded on the source state's `out` list
    and the target state's `incoming` list.

    Supports `target, label = transition` unpacking and `transition[0]`/
    `transition[1]` indexing, matching the (target, label) tuple/
    namedtuple convention used throughout the codebase (e.g.
    DESops.core.automata.Automata.Out, which DESops.core.automata.
    UnobservableReach indexes with t[0]/t[1] rather than unpacking).
    """

    __slots__ = ("index", "label", "prob")

    def __init__(self, index: int, label: Label, prob: Optional[float] = None):
        self.index = index
        self.label = label
        self.prob = prob

    def __iter__(self):
        yield self.index
        yield self.label

    def __getitem__(self, i):
        return (self.index, self.label)[i]

    def __repr__(self):
        return f"Transition(index={self.index!r}, label={self.label!r}, prob={self.prob!r})"

    def __eq__(self, other):
        if isinstance(other, Transition):
            return (self.index, self.label, self.prob) == (
                other.index,
                other.label,
                other.prob,
            )
        if isinstance(other, tuple):
            return other in ((self.index, self.label), (self.index, self.label, self.prob))
        return NotImplemented

    def __hash__(self):
        return hash((self.index, self.label, self.prob))


class State:
    """
    One automaton state: a name, marking/initial flags, and its own
    outgoing/incoming transitions.

    `is_deterministic` is tracked incrementally in true O(1) amortized
    time per add/remove: a running per-label count, not a rescan of the
    whole outgoing list. (An earlier version of this class recomputed it
    by rescanning `out` on every add_transition() call regardless of
    whether anything needed the flag -- O(out-degree) per call, silently
    paid by every caller. Measured as a real, avoidable regression: see
    doc/logs/v2-igraph-decoupling.md.) Checking the flag elsewhere is
    always a plain attribute access.
    """

    __slots__ = (
        "index",
        "name",
        "marked",
        "init",
        "out",
        "incoming",
        "is_deterministic",
        "attrs",
        "_label_counts",
        "_duplicate_labels",
    )

    def __init__(
        self,
        index: int,
        name: str,
        marked: Optional[bool] = None,
        init: bool = False,
        **attrs: Any,
    ):
        self.index = index
        self.name = name
        self.marked = marked
        self.init = init
        self.out: List[Transition] = []
        self.incoming: List[Transition] = []
        self.is_deterministic = True
        self.attrs: Dict[str, Any] = dict(attrs)
        self._label_counts: Dict[Label, int] = {}
        self._duplicate_labels = 0

    def add_transition(
        self,
        target: "State",
        label: Label,
        prob: Optional[float] = None,
        *,
        track_incoming: bool = True,
        track_determinism: bool = True,
    ) -> Transition:
        """Add a transition from self to target. Updates self's outgoing
        adjacency, both O(1). Also updates target's incoming adjacency
        unless track_incoming=False -- pass that when incoming lists
        aren't needed (see populate_incoming() for building them
        separately, later, only if they turn out to be needed after all).

        Updates determinism tracking unless track_determinism=False --
        pass that when the caller already knows the answer (e.g. the
        source is a DFA, deterministic by construction) and wants to set
        is_deterministic directly instead of paying to re-derive it. A
        state built this way must not later go through remove_transitions_to
        expecting live tracking: removals are then no-ops against
        is_deterministic, since nothing was counted for them to undo."""
        t_out = Transition(target.index, label, prob)
        if track_incoming:
            target.incoming.append(Transition(self.index, label, prob))
        self.out.append(t_out)
        if track_determinism:
            self._label_added(label)
        return t_out

    def remove_transitions_to(self, target: "State", label: Optional[Label] = None) -> None:
        """Remove this state's transition(s) to target -- all of them, or
        just the one with the given label if provided. Updates both
        endpoints' adjacency and this state's determinism tracking."""

        def matches(t: Transition) -> bool:
            return t.index == target.index and (label is None or t.label == label)

        kept = []
        for t in self.out:
            if matches(t):
                self._label_removed(t.label)
            else:
                kept.append(t)
        self.out = kept

        target.incoming = [
            t for t in target.incoming
            if not (t.index == self.index and (label is None or t.label == label))
        ]

    def _label_added(self, label: Label) -> None:
        count = self._label_counts.get(label, 0) + 1
        self._label_counts[label] = count
        if count == 2:
            self._duplicate_labels += 1
            self.is_deterministic = False

    def _label_removed(self, label: Label) -> None:
        count = self._label_counts.get(label, 0)
        if count == 0:
            # Nothing was counted for this label -- either it was never
            # added, or it was added with track_determinism=False (e.g.
            # assume_deterministic in states_from_data). Either way there's
            # nothing to undo; leave is_deterministic exactly as it is.
            return
        count -= 1
        if count == 0:
            del self._label_counts[label]
        else:
            self._label_counts[label] = count
        if count == 1:
            self._duplicate_labels -= 1
            if self._duplicate_labels == 0:
                self.is_deterministic = True

    def __repr__(self):
        return (
            f"State(index={self.index!r}, name={self.name!r}, marked={self.marked!r}, "
            f"init={self.init!r}, out={len(self.out)}, incoming={len(self.incoming)}, "
            f"is_deterministic={self.is_deterministic!r})"
        )


def states_from_data(
    data: AutomatonData, *, build_incoming: bool = False, assume_deterministic: bool = False
) -> List[State]:
    """
    Build a State-per-index snapshot from AutomatonData, wiring up
    outgoing adjacency by replaying every edge through
    State.add_transition() (so determinism is computed the same
    incremental way it would be for freshly-built states, not
    special-cased for bulk loading) -- unless assume_deterministic
    skips that, see below.

    Incoming adjacency is *not* built by default: measured cost is
    roughly 3x the outgoing-only build (twice the list appends, plus
    Transition construction for both directions), and most operations
    (complement, parallel, observer) never read .incoming at all -- see
    doc/logs/v2-igraph-decoupling.md. Pass build_incoming=True to build
    it eagerly here, or call populate_incoming() on the result later,
    only if an operation turns out to need it after all.

    assume_deterministic=True skips per-edge determinism tracking
    entirely and sets every state's is_deterministic to True directly.
    Use it when the caller already knows the source is deterministic --
    e.g. `data` came from a DFA, which checks for duplicate outgoing
    labels at insertion time by default. That check is not an absolute
    guarantee, though: DFA.add_edge(s) can be called with
    check_DFA=False (some operations in this codebase do so internally,
    for the same reason -- they already know the result is deterministic
    from the algorithm and don't want to re-derive it), so a DFA-typed
    source is a strong, usually-true signal, not a runtime-enforced
    invariant. Pass assume_deterministic=True only when that trust is
    warranted; DFA.check_DFA() can verify it first if there's any doubt.

    Read-only snapshot: mutating the returned States does not write back
    to `data` or to any Automata instance. The "init" vertex attribute
    (present for NFA-sourced data, absent for DFA-sourced data, per
    DESops.core.nfa.NFA.__init__) becomes each State's `.init` flag if
    present; any other vertex_attrs become `.attrs`. No policy decision
    (e.g. "state 0 is implicitly initial for a DFA") is made here --
    that's left to callers, matching how the existing igraph-backed
    operations already handle it themselves.
    """
    init_flags = data.vertex_attrs.get("init")
    other_attrs = {key: values for key, values in data.vertex_attrs.items() if key != "init"}

    states = [
        State(
            i,
            data.names[i],
            data.marked[i],
            init=bool(init_flags[i]) if init_flags is not None else False,
            **{key: values[i] for key, values in other_attrs.items()},
        )
        for i in range(data.num_states)
    ]
    if assume_deterministic:
        for state in states:
            state.is_deterministic = True

    for edge_index, (source, target) in enumerate(data.edges):
        label = data.labels[edge_index]
        prob = data.probs[edge_index] if data.probs is not None else None
        states[source].add_transition(
            states[target],
            label,
            prob,
            track_incoming=build_incoming,
            track_determinism=not assume_deterministic,
        )

    return states


def populate_incoming(states: List[State]) -> None:
    """
    Populate .incoming for every state in `states`, from their already-
    complete .out lists. O(E) one-time pass, meant to be called at most
    once per states list (states_from_data() defaults to leaving
    .incoming empty; call this afterward only if an operation actually
    ends up needing predecessor lookups).
    """
    for state in states:
        for t in state.out:
            states[t.index].incoming.append(Transition(state.index, t.label, t.prob))
