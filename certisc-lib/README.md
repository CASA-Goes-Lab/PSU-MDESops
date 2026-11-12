# CertiSC

Certified supervisory control for discrete event systems, in Python. Every operation runs in a
formally verified Rust backend: its results are proved correct, not only tested.

Developing certisc (layout, the Rust core, tests, proofs): [DEVELOPING.md](DEVELOPING.md).

## Install

You need Python 3.11 or newer and the Rust compiler: certisc's backend is written in Rust and
is compiled on your machine during the install.

**1. Install Rust (once per machine).** On macOS or Linux:

    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

Accept the default option. Then open a new terminal (or run `source ~/.cargo/env`) and check:

    rustc --version

On Windows, download and run `rustup-init.exe` from https://rustup.rs instead, and accept its
offer to install the Visual Studio C++ build tools (Rust needs them).

**2. Install certisc**, from the repository root:

    python3 -m venv .venv
    .venv/bin/pip install ./certisc-lib

The first install compiles the backend (under a minute). Activate the environment with
`source .venv/bin/activate` to use `python` directly.

## Use

```python
from core_aut import Automaton, validate
from ops_aut import reachable, trim

G = Automaton(events=["start", "finish", "break", "repair"], Euc=["break"])
idle = G.add_state("Idle", init=True, marked=True)
work = G.add_state("Working")
down = G.add_state("Down")
G.add_transition(idle, "start", work)
G.add_transition(work, "finish", idle)
G.add_transition(work, "break", down)
G.add_transition(down, "repair", idle)

V = validate(G)          # checked once; raises InvalidAutomatonError if G is not valid
reachable(V)             # [0, 1, 2]
T = trim(V)              # a new automaton; V is unchanged
T.show()
```

Build an `Automaton`, then `validate` it once: the result (a read-only `ValidAutomaton`) can be
passed to every operation without being checked again. To change it, take an editable copy
with `V.to_automaton()`.

| Package | Functions |
|---|---|
| `core_aut` | `Automaton`, `validate`, `check_or_raise`, `ValidAutomaton`, `InvalidAutomatonError`; EFSMs: `EfsmSystem`, `Efsm`, `Edge`, `Variable` |
| `ops_aut` | `next_states`, `active_events`, `active_events_at`, `reachable`, `coreachable`, `delete_states`, `accessible`, `coaccessible`, `trim`, `parallel_2aut`, `product_2aut` |
| `io_aut` | `read_aut`, `write_aut` (JSON), `read_fsm` (DESUMA `.fsm` files), `read_cif` (CIF models, as EFSMs) |
| `sup` | `supervisor` (supervisory control; prefix-closed so far) |
| `viz_aut` | `write_svg`, `write_dot`, `svg`, `to_dot` (drawings with Graphviz) |

`reachable` and `coreachable` can also return witnesses (`witnesses=True`), from which a
shortest word to each state follows. `parallel_2aut(G1, G2)` and `product_2aut(G1, G2)` name
each state of the result by the pair of names `(name1, name2)`; a composed automaton cannot be
written to JSON yet (writing needs string names).

`supervisor(G, H)` returns the supervisor for the plant `G` and the specification `H`: the
largest behaviour of `G` allowed by `H` that never needs to prevent an uncontrollable event.
`G` and `H` must be deterministic, and `H` may use only events of `G` (the events it does not
mention are left free). `method="naive"` runs the textbook iteration instead (not verified,
much slower on large automata). `construction="refine"` (complete `H`, then work on `G × H`)
and `construction="subautomaton"` (when `H` is `G` with some states deleted, same names, or
just the list of indices of the states of `G` to keep, the fastest form) give the same result
by other routes; the default is `"escape"`. A forbidden-state specification needs no `H`:
`supervisor(G, forbidden=[x1, x2, ...])` keeps `G` away from those states.

Drawings: `write_svg(G, "g.svg")` draws any automaton with Graphviz (install the `dot`
program; macOS: `brew install graphviz`): marked states as double circles, an arrow into the
initial state, uncontrollable events dashed.

Examples, one script per topic:
`Examples/v2/testing/certisc/` (outer repository).

## Automata in files

certisc's format is JSON, with transitions grouped by source state:

```json
{
  "events": ["start", "finish", "break", "repair"],
  "uncontrollable": ["break"],
  "unobservable": [],
  "states": ["Idle", "Working", "Down"],
  "initial": ["Idle"],
  "marked": ["Idle"],
  "transitions": {
    "Idle":    {"start": "Working"},
    "Working": {"finish": "Idle", "break": "Down"},
    "Down":    {"repair": "Idle"}
  }
}
```

`read_aut(path)` and `read_fsm(path)` return a `ValidAutomaton`, ready to use. `read_cif(path)`
reads a CIF model (Eclipse ESCET) as an `EfsmSystem`: extended finite-state machines with
shared variables, not yet flattened into an automaton (unfolding comes next). More on reading
and writing: [src/io_aut/IO.md](src/io_aut/IO.md).

License: BSD-3-Clause ([license.txt](license.txt)).
