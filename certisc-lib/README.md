# CertiSC

Certified supervisory control for discrete event systems. The Python code is verified with
[Nagini](https://github.com/marcoeilers/nagini). The algorithms are proved in Lean, in
[`../certisc-proof/`](../certisc-proof/).

    src/core_aut/                public: Automaton, ValidAutomaton, validate, check_or_raise
        trusted/                 trusted helpers: encoding, wrapper, _strip, error
        verified_core/           Nagini-verified implementations (internal): check.py
    src/io_aut/                  public: read_aut, write_aut (JSON), read_fsm (DESUMA import)
    src/ops_aut/                 public: next_states, active_events
        verified_ops/            Nagini-verified implementations (internal):
                                 basic_ops.py, parallel.py (in progress), parallel_check.py
    tests/                       one folder per package

Public functions validate the automaton, encode it (core_aut/trusted/encoding.py), and call an
implementation (`backend="verified"`; a NumPy backend may come later). The verified code is
stripped of its contracts at import (core_aut/trusted/_strip.py).

What is verified, and why it works: [VERIFICATION.md](VERIFICATION.md). Reading and writing automata: [src/io_aut/IO.md](src/io_aut/IO.md). End-user examples: `Examples/v2/testing/certisc/` (outer repository).

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

From the repository root (Python 3.11+, or 3.12+ with Java for Nagini):

    $ python3 -m venv .venv && source .venv/bin/activate
    $ pip install -e "certisc-lib[dev,verify]"     # drop ",verify" to skip Nagini

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

    $ pytest                                              # 42 passed
    $ nagini src/core_aut/verified_core/check.py          # about 20 s
    $ nagini src/ops_aut/verified_ops/basic_ops.py        # about 30 s
    $ nagini src/ops_aut/verified_ops/parallel.py         # about 30 s
    $ nagini src/ops_aut/verified_ops/parallel_check.py   # about 65 s

## Adding a package

1. Create `src/<name>/__init__.py`. Start it with `import core_aut` if the package has verified
   code, so the no-op contracts are installed.
2. Add `"<name>*"` to `include` in `pyproject.toml`.
3. Add `tests/<name>/`, then run `pip install -e "certisc-lib[dev,verify]"` again.

Don't use standard-library names such as `io`; they would shadow Python's own modules.

License: BSD-3-Clause ([license.txt](license.txt)).
