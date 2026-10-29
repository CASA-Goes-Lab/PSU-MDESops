"""
Operations on automata (part of the certisc distribution). Public API:

- next_states(G, states, event, witnesses=False, backend="verified")
- active_events(G, states, witnesses=False, backend="verified")
- active_events_at(G, state)
- reachable(G, states=None, witnesses=False, backend="verified")
- coreachable(G, states=None, witnesses=False, backend="verified")
- delete_states(G, states, backend="verified") -> ValidAutomaton (a new automaton)
- accessible(G), coaccessible(G), trim(G) -> ValidAutomaton (new automata)
- EmptyAutomatonWarning  (when one of these returns the empty automaton)

Layout:
- basic_ops.py    public functions, calling an implementation
- verified_ops/   Nagini-verified implementations (internal; see its __init__ for how to verify)
- (later: numpy_ops/)
"""

import core_aut  # noqa: F401  (installs the contract stand-ins before any verified module)
from ops_aut.basic_ops import (EmptyAutomatonWarning, accessible, active_events,
                               active_events_at, coaccessible, coreachable, delete_states,
                               next_states, reachable, trim)

__all__ = ["next_states", "active_events", "active_events_at", "reachable", "coreachable",
           "delete_states", "accessible", "coaccessible", "trim", "EmptyAutomatonWarning"]
