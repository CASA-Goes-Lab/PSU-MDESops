"""
Supervisory control (part of the certisc distribution). Public API:

- supervisor(G, H, mode="prefix_closed", method="fast", backend="rust") -> ValidAutomaton

Modes: "prefix_closed" (now); "nonblocking" and partial observation come later.
Methods: "fast" (verified: Rust + Verus, proved in Lean) and "naive" (plain Python, not
verified; the textbook iteration, quadratic).

Layout:
- supervisor.py   the public function, calling the Verus-verified Rust code
                  (certisc-lib/rust/verified/src/sup/) through rust_core._rs
Spec: certisc-proof/spec/supervisor.md.
"""

from sup.supervisor import supervisor

__all__ = ["supervisor"]
