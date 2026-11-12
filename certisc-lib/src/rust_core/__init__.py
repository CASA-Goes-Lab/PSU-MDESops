"""
The compiled Rust core (part of the certisc distribution; internal, not for direct use).

This package holds only the extension module `_rs` (`_rs.abi3.so`, not in git), which maturin
builds from certisc-lib/rust/: the Verus-verified crate (rust/verified/) behind the PyO3 glue
(rust/binding/, class RsAut). `pip install -e "certisc-lib[dev]"` (re)builds it here; a normal
install puts it in site-packages instead.

The Python packages reach it only through core_aut/trusted/wrapper.py (`RsAut.from_lists`) and
through `ValidAutomaton._rs`. What is proved and what is trusted: certisc-lib/DEVELOPING.md.
"""
