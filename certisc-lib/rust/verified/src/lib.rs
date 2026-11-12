//! certisc_verified: the verified core of certisc in Rust + Verus.
//!
//! The modules follow the Python packages they serve:
//! - `core_aut::aut`: the automaton (flat storage) and its view (the mathematical automaton,
//!   as in Lean's `Automaton`).
//! - `core_aut::check`: the validity checker.
//! - `ops_aut::basic_ops`: `next_states`, `active_events`.
//! - `ops_aut::reach`: `reachable`, `coreachable` (and the reverse index).
//! - `ops_aut::delete`: `delete_states`, `accessible`, `coaccessible`, `trim`.
//! - `ops_aut::parallel`: the search behind the composition (pairs of states).
//! - `ops_aut::compose`: the parallel composition and the product.
//! - `sup::supcon`: supervisory control, prefix-closed (bad states, uncontrollable part).
//!
//! Verify (from certisc-lib/rust/verified/): `verus --crate-type=lib src/lib.rs`.
//! Verus checks the whole crate at once, because the proofs use each other across modules.
#![allow(non_snake_case)]

pub mod core_aut;
pub mod ops_aut;
pub mod sup;
