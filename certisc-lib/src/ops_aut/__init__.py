"""
Operations on automata (part of the certisc distribution). Public API:

- next_states(G, states, event, witnesses=False, backend="rust")
- active_events(G, states, witnesses=False, backend="rust")
- active_events_at(G, state)
- reachable(G, states=None, witnesses=False, backend="rust")
- coreachable(G, states=None, witnesses=False, backend="rust")
- delete_states(G, states, backend="rust") -> ValidAutomaton (a new automaton)
- accessible(G), coaccessible(G), trim(G) -> ValidAutomaton (new automata)
- parallel_2aut(G1, G2), product_2aut(G1, G2) -> ValidAutomaton (new automata)
- EmptyAutomatonWarning  (when one of these returns the empty automaton)

Layout:
- basic_ops.py    public functions, calling the Verus-verified Rust code
                  (certisc-lib/rust/verified/src/ops_aut/) through rust_core._rs
- (later: numpy_ops/)
"""

from ops_aut.basic_ops import (EmptyAutomatonWarning, accessible, active_events,
                               active_events_at, coaccessible, coreachable, delete_states,
                               next_states, parallel_2aut, product_2aut, reachable,
                               trim)

__all__ = ["next_states", "active_events", "active_events_at", "reachable", "coreachable",
           "delete_states", "accessible", "coaccessible", "trim", "parallel_2aut",
           "product_2aut", "EmptyAutomatonWarning"]
