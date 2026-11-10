# CertiSC

Certified supervisory control for discrete event systems. The operations run in a Rust core
verified with [Verus](https://github.com/verus-lang/verus) (`rust/`), behind a Python API. The
algorithms are proved in Lean, in [`../certisc-proof/`](../certisc-proof/). (The earlier
Python implementation, verified with [Nagini](https://github.com/marcoeilers/nagini), is kept
for reference in `../legacy/nagini/`.)

    src/core_aut/                public: Automaton, ValidAutomaton, validate, check_or_raise
        _rs.abi3.so              the compiled Rust core (built by pip install; not in git)
        trusted/                 trusted helpers: encoding, wrapper, error
    src/io_aut/                  public: read_aut, write_aut (JSON), read_fsm (DESUMA import)
    src/ops_aut/                 public (basic_ops.py): next_states, active_events,
                                 active_events_at, reachable, coreachable, delete_states,
                                 accessible, coaccessible, trim
    tests/                       one folder per package
    rust/                        the Rust core (rust/README.md):
        verified/                Verus-verified crate, modules core_aut/ and ops_aut/
        binding/                 PyO3 glue (trusted): the extension core_aut._rs

Public functions take a ValidAutomaton (or validate a plain Automaton first) and call the
Rust code. `validate` encodes the automaton (core_aut/trusted/encoding.py) and hands it to
Rust, whose verified checker accepts it; the ValidAutomaton then holds it in Rust.

What is verified, what is trusted, and how to check the proofs: [rust/README.md](rust/README.md). Reading and writing automata: [src/io_aut/IO.md](src/io_aut/IO.md). End-user examples: `Examples/v2/testing/certisc/` (outer repository).

## Automata in files

certisc's format is JSON, with transitions grouped by source state (details in
`src/io_aut/aut_json.py`):

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

`read_aut(path)` and `read_fsm(path)` return a **ValidAutomaton**: checked once by the verified
checker, then read-only, so operations never check or encode it again (validate a hand-built
`Automaton` with `validate(G)`). In a loop of 2000-state reachability this is 0.02 s instead of
4 s.

## Install

From the repository root (Python 3.11+), with a Rust toolchain (https://rustup.rs; the build
compiles the Rust core, about 30 s the first time):

    $ python3 -m venv .venv && source .venv/bin/activate
    $ pip install -e "certisc-lib[dev]"

The build backend is [maturin](https://www.maturin.rs). Python edits take effect at once;
after editing Rust, run the `pip install -e` line again. Verus is not needed to build, only to
check the proofs (rust/README.md). A released wheel will need neither Rust nor Verus.

## Use

```python
from core_aut import Automaton, check_or_raise, validate
from ops_aut import next_states

g = Automaton(events=["a", "b"])
g.add_state("x0", init=True)
g.add_state("x1", marked=True)
g.add_transition(0, "a", 1)
check_or_raise(g, deterministic=True)   # raises InvalidAutomatonError if invalid
next_states(g, [0], "a")                 # [1]
V = validate(g)                          # read-only ValidAutomaton: checked once
next_states(V, [0], "a")                 # [1], without checking again
```

## Test and verify

From `certisc-lib/`:

    $ pytest                                                  # 50 passed
    $ cd rust/verified && verus --crate-type=lib src/lib.rs   # 164 verified (rust/README.md)

## Adding a package

1. Create `src/<name>/__init__.py`; its verified code goes into `rust/verified/src/<name>/`
   (a module of the same crate), and its binding into `rust/binding/src/lib.rs`.
2. Add `"<name>"` to `python-packages` in `pyproject.toml` (`[tool.maturin]`).
3. Add `tests/<name>/`, then run `pip install -e "certisc-lib[dev]"` again.

Don't use standard-library names such as `io`; they would shadow Python's own modules.

License: BSD-3-Clause ([license.txt](license.txt)).
