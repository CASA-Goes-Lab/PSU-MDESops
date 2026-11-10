//! PyO3 binding (trusted glue): the Python extension module `core_aut._rs`.
//!
//! Python lists in and out, verified Rust (crate `certisc_verified`) in between. Users never
//! import this module: `core_aut` and `ops_aut` call it (core_aut/valid.py,
//! ops_aut/basic_ops.py).
//!
//! `RsAut` holds a Rust `Aut` that passed the verified `check_code` (so `wf()` holds for it), or
//! that a verified operation returned (whose `ensures` gives `wf()`). Every operation's other
//! preconditions (state indices in range, one flag per state) are checked here before the call,
//! and raise `ValueError` when they fail. That check is the trusted part: it must imply the
//! `requires` of the verified function it guards.
use std::sync::OnceLock;

use certisc_verified::core_aut::aut::Aut;
use certisc_verified::core_aut::check;
use certisc_verified::ops_aut::{basic_ops, compose as vcompose, delete, reach};
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;

type Witness = Vec<Option<(usize, usize)>>;
type Lists = (usize, usize, Vec<bool>, Vec<bool>, Vec<bool>, Vec<bool>, Vec<bool>, Vec<usize>, Vec<usize>, Vec<usize>);

/// A valid automaton held in Rust.
#[pyclass(name = "RsAut", frozen, module = "core_aut._rs")]
struct RsAut {
    g: Aut,
    /// `check_code(g, true)`: 0 if deterministic, else 6 or 7. Computed on first use.
    det: OnceLock<u8>,
    /// Reverse index (verified builder); built on the first `coreachable`, then kept.
    rev: OnceLock<Vec<Vec<(usize, usize)>>>,
}

impl RsAut {
    fn wrap(g: Aut) -> RsAut {
        RsAut { g, det: OnceLock::new(), rev: OnceLock::new() }
    }

    /// Trusted guard for `states_in(g, s)`.
    fn states(&self, s: Vec<usize>) -> PyResult<Vec<usize>> {
        if let Some(x) = s.iter().find(|&&x| x >= self.g.n) {
            return Err(PyValueError::new_err(format!("{x} is not a state index")));
        }
        Ok(s)
    }

    fn deleted(py: Python<'_>, r: (Aut, Vec<usize>)) -> PyResult<(Py<RsAut>, Vec<usize>)> {
        Ok((Py::new(py, RsAut::wrap(r.0))?, r.1))
    }
}

#[pymethods]
impl RsAut {
    /// Build from the grouped encoding; runs the verified checker (`check_code(g, false)`).
    /// Raises ValueError(code) if the lists are not a valid automaton: `code` is the checker's
    /// result code (1-5, 8; messages in core_aut/trusted/wrapper.py).
    #[staticmethod]
    #[allow(clippy::too_many_arguments)]
    fn from_lists(
        n: usize, m: usize, in_e: Vec<bool>, in_euc: Vec<bool>, in_euo: Vec<bool>, init: Vec<bool>,
        marked: Vec<bool>, start: Vec<usize>, evt: Vec<usize>, dst: Vec<usize>,
    ) -> PyResult<RsAut> {
        let g = Aut { n, m, in_e, in_euc, in_euo, init, marked, start, evt, dst };
        let code = check::check_code(&g, false);
        if code != 0 {
            return Err(PyValueError::new_err(code));
        }
        Ok(RsAut::wrap(g))
    }

    /// The grouped encoding: (n, m, in_e, in_euc, in_euo, init, marked, start, evt, dst).
    fn to_lists(&self) -> Lists {
        let g = &self.g;
        (g.n, g.m, g.in_e.clone(), g.in_euc.clone(), g.in_euo.clone(), g.init.clone(),
         g.marked.clone(), g.start.clone(), g.evt.clone(), g.dst.clone())
    }

    #[getter]
    fn n(&self) -> usize {
        self.g.n
    }

    #[getter]
    fn m(&self) -> usize {
        self.g.m
    }

    /// The verified checker's code for "deterministic automaton" (cached): 0 if deterministic,
    /// 6 if there are two initial states, 7 if a state has two transitions on one event.
    #[getter]
    fn det_code(&self) -> u8 {
        *self.det.get_or_init(|| check::check_code(&self.g, true))
    }

    /// Deterministic (verified check, cached).
    #[getter]
    fn is_deterministic(&self) -> bool {
        self.det_code() == 0
    }

    /// (out, src): the states reached from `states` by event `e`, each once; out[i] is reached
    /// from states[src[i]].
    fn next_states(&self, py: Python<'_>, states: Vec<usize>, e: usize) -> PyResult<(Vec<usize>, Vec<usize>)> {
        let s = self.states(states)?;
        Ok(py.detach(|| basic_ops::next_states(&self.g, &s, e)))
    }

    /// (out, src): the events enabled at some state of `states`, each once.
    fn active_events(&self, py: Python<'_>, states: Vec<usize>) -> PyResult<(Vec<usize>, Vec<usize>)> {
        let s = self.states(states)?;
        Ok(py.detach(|| basic_ops::active_events(&self.g, &s)))
    }

    /// (out, parents): the states reachable from `states`; parents[i] is None or (p, e).
    fn reachable(&self, py: Python<'_>, states: Vec<usize>) -> PyResult<(Vec<usize>, Witness)> {
        let s = self.states(states)?;
        Ok(py.detach(|| reach::reachable(&self.g, &s)))
    }

    /// (out, nexts): the states that reach `states`; nexts[i] is None or (p, e).
    fn coreachable(&self, py: Python<'_>, states: Vec<usize>) -> PyResult<(Vec<usize>, Witness)> {
        let s = self.states(states)?;
        Ok(py.detach(|| {
            let rev = self.rev.get_or_init(|| reach::reverse_index(&self.g));
            reach::coreachable_with(&self.g, rev, &s)
        }))
    }

    /// (G', old): G without the states x with dele[x]; old[i] is the state state i comes from.
    fn delete_states(&self, py: Python<'_>, dele: Vec<bool>) -> PyResult<(Py<RsAut>, Vec<usize>)> {
        if dele.len() != self.g.n {
            return Err(PyValueError::new_err("one flag per state is needed"));
        }
        let r = py.detach(|| delete::delete_states(&self.g, &dele));
        RsAut::deleted(py, r)
    }

    fn accessible(&self, py: Python<'_>) -> PyResult<(Py<RsAut>, Vec<usize>)> {
        let r = py.detach(|| delete::accessible(&self.g));
        RsAut::deleted(py, r)
    }

    fn coaccessible(&self, py: Python<'_>) -> PyResult<(Py<RsAut>, Vec<usize>)> {
        let r = py.detach(|| delete::coaccessible(&self.g));
        RsAut::deleted(py, r)
    }

    fn trim(&self, py: Python<'_>) -> PyResult<(Py<RsAut>, Vec<usize>)> {
        let r = py.detach(|| delete::trim(&self.g));
        RsAut::deleted(py, r)
    }

    /// (H, p1, p2): the parallel composition (par=True) or product (par=False) of self and
    /// other; output event numbers: self's, and other's event e2 is map2[e2] (m in all).
    /// Raises ValueError if map2 is not a valid numbering (verified `check_map`) or n1 * n2
    /// does not fit in 64 bits.
    fn compose(&self, py: Python<'_>, other: &RsAut, map2: Vec<usize>, m: usize, par: bool)
        -> PyResult<(Py<RsAut>, Vec<usize>, Vec<usize>)> {
        let (g1, g2) = (&self.g, &other.g);
        if (g1.n as u64).checked_mul(g2.n as u64).is_none() {
            return Err(PyValueError::new_err("too many state pairs"));
        }
        if !vcompose::check_map(g1, g2, &map2, m) {
            return Err(PyValueError::new_err("invalid event numbering map2"));
        }
        let (h, p1, p2) = py.detach(|| vcompose::compose_aut(g1, g2, &map2, m, par));
        Ok((Py::new(py, RsAut::wrap(h))?, p1, p2))
    }
}

#[pymodule]
fn _rs(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<RsAut>()?;
    Ok(())
}
