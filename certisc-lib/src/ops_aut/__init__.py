"""
Operations on automata (part of the certisc distribution). Public API:

- next_states(G, states, event, witnesses=False, backend="verified")

Layout:
- basic_ops.py    public functions, calling an implementation
- verified_ops/   Nagini-verified implementations (internal; see its __init__ for how to verify)
- (later: numpy_ops/)
"""

import core_aut  # noqa: F401  (installs the contract stand-ins before any verified module)
from ops_aut.basic_ops import next_states

__all__ = ["next_states"]
