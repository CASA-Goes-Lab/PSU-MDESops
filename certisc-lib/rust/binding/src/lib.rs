//! PyO3 binding (trusted glue): the Python extension module `rust_core._rs`.
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
use certisc_verified::sup::{complete, supcon};
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;

type Witness = Vec<Option<(usize, usize)>>;
type Lists = (usize, usize, Vec<bool>, Vec<bool>, Vec<bool>, Vec<bool>, Vec<bool>, Vec<usize>, Vec<usize>, Vec<usize>);

/// A valid automaton held in Rust.
#[pyclass(name = "RsAut", frozen, module = "rust_core._rs")]
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

    /// (code, e2): the verified `check_agree`. code 0: self and other agree on every shared
    /// event; 1: other's event e2 is shared and controllable in one, uncontrollable in the other;
    /// 2: the same for observability. Raises ValueError if map2 is not a valid numbering.
    fn agree(&self, other: &RsAut, map2: Vec<usize>, m: usize) -> PyResult<(u8, usize)> {
        let (g1, g2) = (&self.g, &other.g);
        if !vcompose::check_map(g1, g2, &map2, m) {
            return Err(PyValueError::new_err("invalid event numbering map2"));
        }
        Ok(vcompose::check_agree(g1, g2, &map2, m))
    }

    /// (H, p1, p2): the parallel composition (par=True) or product (par=False) of self and
    /// other; output event numbers: self's, and other's event e2 is map2[e2] (m in all).
    /// Raises ValueError if map2 is not a valid numbering (verified `check_map`), if the inputs
    /// disagree on a shared event (verified `check_agree`; call `agree` first for the event),
    /// or if n1 * n2 does not fit in 64 bits.
    fn compose(&self, py: Python<'_>, other: &RsAut, map2: Vec<usize>, m: usize, par: bool)
        -> PyResult<(Py<RsAut>, Vec<usize>, Vec<usize>)> {
        let (g1, g2) = (&self.g, &other.g);
        if (g1.n as u64).checked_mul(g2.n as u64).is_none() {
            return Err(PyValueError::new_err("too many state pairs"));
        }
        if !vcompose::check_map(g1, g2, &map2, m) {
            return Err(PyValueError::new_err("invalid event numbering map2"));
        }
        if vcompose::check_agree(g1, g2, &map2, m).0 != 0 {
            return Err(PyValueError::new_err("the automata disagree on a shared event"));
        }
        let (h, p1, p2) = py.detach(|| vcompose::compose_aut(g1, g2, &map2, m, par));
        Ok((Py::new(py, RsAut::wrap(h))?, p1, p2))
    }

    /// (S, old): the prefix-closed supervisor (verified `supcon::supervisor_pc`). self is
    /// P0 = G ‖ H (from `compose`, G first), `plant` is G, and `p1[i]` is the plant state of
    /// state i of self (the `p1` that `compose` returned). old[i] is the state of self that
    /// state i of S comes from. Raises ValueError if p1 does not fit (one entry per state,
    /// each a state of G) or G has more event numbers than self.
    fn supervisor_pc(&self, py: Python<'_>, plant: &RsAut, p1: Vec<usize>) -> PyResult<(Py<RsAut>, Vec<usize>)> {
        let (p, g) = (&self.g, &plant.g);
        if p1.len() != p.n || p1.iter().any(|&a| a >= g.n) {
            return Err(PyValueError::new_err("p1 must give one plant state per state"));
        }
        if g.m > p.m {
            return Err(PyValueError::new_err("the plant has more event numbers than P0"));
        }
        let (s, old, _, _, _, _) = py.detach(|| supcon::supervisor_pc(p, g, &p1));
        Ok((Py::new(py, RsAut::wrap(s))?, old))
    }

    /// Hc: the completion of self (verified `complete::complete`): a dump state (number n),
    /// `extra` new events (numbers m .. m+extra-1, flags `euc_x`, `euo_x`) that self-loop, and
    /// every missing event of self going to the dump state. Raises ValueError if self has no
    /// states or the flag lists do not have `extra` entries.
    fn complete(&self, py: Python<'_>, extra: usize, euc_x: Vec<bool>, euo_x: Vec<bool>) -> PyResult<Py<RsAut>> {
        let h = &self.g;
        if h.n == 0 {
            return Err(PyValueError::new_err("the specification has no states"));
        }
        if euc_x.len() != extra || euo_x.len() != extra {
            return Err(PyValueError::new_err("one flag per extra event is needed"));
        }
        if h.n.checked_add(1).is_none() || h.m.checked_add(extra).is_none() {
            return Err(PyValueError::new_err("too many states or events"));
        }
        let hc = py.detach(|| complete::complete(h, extra, &euc_x, &euo_x));
        Py::new(py, RsAut::wrap(hc))
    }

    /// (S, old): the supervisor on a strict subautomaton (verified `supcon::supervisor_sub`):
    /// `inside[x]` marks the states of I. Raises ValueError without one flag per state.
    fn supervisor_sub(&self, py: Python<'_>, inside: Vec<bool>) -> PyResult<(Py<RsAut>, Vec<usize>)> {
        if inside.len() != self.g.n {
            return Err(PyValueError::new_err("one flag per state is needed"));
        }
        let (s, old, _, _, _, _) = py.detach(|| supcon::supervisor_sub(&self.g, &inside));
        Ok((Py::new(py, RsAut::wrap(s))?, old))
    }

    /// (S, old): as `supervisor_sub`, for self = G × Hc with I = the states whose Hc label
    /// (`p2`, from `compose`) is not the dump state `d` (verified `supcon::not_label`).
    fn supervisor_sub_label(&self, py: Python<'_>, p2: Vec<usize>, d: usize) -> PyResult<(Py<RsAut>, Vec<usize>)> {
        if p2.len() != self.g.n {
            return Err(PyValueError::new_err("one label per state is needed"));
        }
        let inside = supcon::not_label(&p2, d);
        let (s, old, _, _, _, _) = py.detach(|| supcon::supervisor_sub(&self.g, &inside));
        Ok((Py::new(py, RsAut::wrap(s))?, old))
    }

    /// Whether `sub` is self with the states outside `inside` deleted (verified
    /// `delete::delete_states`, then the verified identity check `supcon::same_aut`).
    fn restricts(&self, py: Python<'_>, sub: &RsAut, inside: Vec<bool>) -> PyResult<bool> {
        if inside.len() != self.g.n {
            return Err(PyValueError::new_err("one flag per state is needed"));
        }
        let g = &self.g;
        let dele = supcon::negate(&inside);
        Ok(py.detach(|| {
            let (q, _old) = delete::delete_states(g, &dele);
            supcon::same_aut(&q, &sub.g)
        }))
    }

    /// As `restricts`, for a `sub` in its own event numbering and state order: `sub` is first
    /// re-encoded (trusted, `reencode`: its event e2 becomes `emap[e2]` of self's `m` events,
    /// state `order[k]` becomes state k), then compared with the verified deletion. A wrong
    /// re-encoding can only make the comparison fail. Malformed maps give False.
    fn restricts_mapped(&self, py: Python<'_>, sub: &RsAut, inside: Vec<bool>, emap: Vec<usize>, order: Vec<usize>) -> PyResult<bool> {
        if inside.len() != self.g.n {
            return Err(PyValueError::new_err("one flag per state is needed"));
        }
        let g = &self.g;
        let dele = supcon::negate(&inside);
        Ok(py.detach(|| match reencode(&sub.g, &emap, g.m, &order) {
            None => false,
            Some(h) => {
                let (q, _old) = delete::delete_states(g, &dele);
                supcon::same_aut(&q, &h)
            }
        }))
    }
}

/// `h` re-encoded (trusted glue, not verified): event e2 becomes `emap[e2]` (in `0 .. m`), state
/// `order[k]` becomes state k, and each block is sorted again by (event, target). None if the
/// maps are malformed (emap not injective or out of range, order not a permutation).
fn reencode(h: &Aut, emap: &[usize], m: usize, order: &[usize]) -> Option<Aut> {
    let n = h.n;
    if emap.len() != h.m || order.len() != n {
        return None;
    }
    let mut used = vec![false; m];
    for &o in emap {
        if o >= m || used[o] {
            return None;
        }
        used[o] = true;
    }
    let mut new_of = vec![usize::MAX; n];
    for (k, &x) in order.iter().enumerate() {
        if x >= n || new_of[x] != usize::MAX {
            return None;
        }
        new_of[x] = k;
    }
    let (mut in_e, mut in_euc, mut in_euo) = (vec![false; m], vec![false; m], vec![false; m]);
    for e2 in 0..h.m {
        in_e[emap[e2]] = h.in_e[e2];
        in_euc[emap[e2]] = h.in_euc[e2];
        in_euo[emap[e2]] = h.in_euo[e2];
    }
    let init = order.iter().map(|&x| h.init[x]).collect();
    let marked = order.iter().map(|&x| h.marked[x]).collect();
    let mut start = Vec::with_capacity(n + 1);
    let mut evt = Vec::with_capacity(h.evt.len());
    let mut dst = Vec::with_capacity(h.dst.len());
    start.push(0);
    let mut blk: Vec<(usize, usize)> = Vec::new();
    for &x in order {
        blk.clear();
        blk.extend((h.start[x]..h.start[x + 1]).map(|k| (emap[h.evt[k]], new_of[h.dst[k]])));
        blk.sort_unstable();
        for &(e, y) in &blk {
            evt.push(e);
            dst.push(y);
        }
        start.push(evt.len());
    }
    Some(Aut { n, m, in_e, in_euc, in_euo, init, marked, start, evt, dst })
}

#[pymodule]
fn _rs(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<RsAut>()?;
    Ok(())
}
