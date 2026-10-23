# Reading and writing automata (`io_aut`)

```python
from io_aut import read_aut, write_aut, read_fsm

V = read_aut("machine.json")      # a ValidAutomaton: checked, read-only
write_aut(V, "copy.json")
W = read_fsm("M1.fsm")            # DESUMA models: also a ValidAutomaton
```

## 1. The file format

certisc's format is JSON. The transitions are grouped by source state: each state is named once,
followed by its events and their targets.

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

| Key | Required | Meaning |
|---|---|---|
| `"states"` | yes | the state names, unique strings. Their order gives the state numbers: `"Idle"` is state 0, `"Working"` state 1, … |
| `"initial"` | yes | the initial states (one or more; none only if there are no states) |
| `"transitions"` | yes | `source → {event: target}`. A state without transitions can be left out |
| `"events"` | no | the alphabet E. If left out: the events used by the transitions, plus the uncontrollable and unobservable ones |
| `"uncontrollable"` | no | Euc (default: none) |
| `"unobservable"` | no | Euo (default: none) |
| `"marked"` | no | the marked states (default: none) |

**Several targets for one event** (a nondeterministic automaton) are written as a list:

```json
"transitions": {
  "x0": {"a": ["x1", "x2"], "b": "x0"}
}
```

**Rules checked when reading:**
- only the seven keys above;
- `"states"` has no repeated names;
- every state named in `"initial"`, `"marked"` and `"transitions"` is listed in `"states"`;
- a target list is not empty;
- every transition's event is in `"events"`, if `"events"` is given;
- an initial state exists whenever there are states;
- `"uncontrollable"` and `"unobservable"` events are part of E.

## 2. What you get after reading

`read_aut` and `read_fsm` return a **`ValidAutomaton`**. It reads like an `Automaton`: the same
`num_states`, `states[i].name / .marked / .out`, `events`, `Euc`, `Euo`, `init` and
`transitions()`, with states numbered `0 … n−1` and events by their labels. It has passed the
verified checker and **cannot be changed**. The encoding the verified code uses stays inside;
the user never sees it.

Example: reading `models/M1.json` from the examples gives:

```
V                    ValidAutomaton(3 states, 4 events, deterministic)
V.names              ('I1', 'W1', 'D1')
V.num_states         3
V.events             {'f_M1', 'in_M1', 'out_B1', 'to_M1'}
V.Euc, V.Euo         {'f_M1'}, set()
V.init, V.marked     {0}, set()
V.is_deterministic   True
V.index_of('W1')     1
V.transitions()      (0, 'in_M1', 1), (0, 'to_M1', 1), (1, 'f_M1', 2), (2, 'out_B1', 0)
V.states[1]          State('W1', marked=False, out={'f_M1': (2,)})
```

| What | Gives |
|---|---|
| `V.num_states` | the number of states n |
| `V.states[i]` | state i, as in `Automaton`: `.name`, `.marked`, `.out` (event → tuple of targets). Read-only |
| `V.names` | the state names; state i is `V.names[i]` |
| `V.index_of(name)` | the number of a state, from its name |
| `V.events`, `V.Euc`, `V.Euo` | the event sets (labels) |
| `V.init`, `V.marked` | the initial and marked states (numbers) |
| `V.is_deterministic` | at most one initial state, and no state with two transitions on one event. Decided by the verified checker |
| `V.transitions()` | every transition as `(source, event, target)`, sources in order, events sorted |
| `V.to_automaton()` | an editable copy (an `Automaton`) |
| `print(V)` | the readable layout below, up to 20 states |
| `V.show()` | the readable layout, all states (or `V.show(max_states=k)`) |

`print(V)` for the M2 model:

```
ValidAutomaton(3 states, 5 events, deterministic)
  events:         f_M2, in_M2, to_B2, to_M1, to_M2
  uncontrollable: f_M2
  unobservable:   (none)
  initial:        I2
  marked:         (none)
  transitions:
    I2 : in_M2 -> W2, to_M2 -> W2
    W2 : f_M2 -> D2
    D2 : to_M1 -> I2, to_B2 -> I2
```

A nondeterministic event shows its targets in braces: `start -> {Working, Down}`. Larger
automata print their first 20 states, then `... N more states (V.show() prints all)`.

`V.states`, `print(V)` and `V.show()` are for reading and debugging. Each `V.states[i].out` is
built from the encoding when read, slower than an `Automaton`'s stored dict (measurements in
`doc/logs/performance.md`). Loops should use `V.names`, `V.transitions()`, or the operations;
`V.to_automaton()` gives a full `Automaton` copy when one is needed.

**Operations take it directly** and never check or encode it again:

```python
from ops_aut import next_states
next_states(V, [V.index_of("I1")], "in_M1")      # [1]
```

**To change an automaton,** take an editable copy, change it, and validate it again:

```python
from core_aut import validate
G = V.to_automaton()
x = G.add_state("Broken")
G.add_transition(V.index_of("W1"), "fail", x)
G.events.add("fail")            # "fail" must be an event (W1)
V2 = validate(G)                # a new ValidAutomaton; V is unchanged
```

An automaton built by hand (an `Automaton`) becomes a `ValidAutomaton` with `validate(G)`.

## 3. What happens inside `read_aut`

```
 file ──json──► dict ──from_dict──► Automaton ──encode──► lists ──verified checker──► ValidAutomaton
                       (trusted)     (temporary)  (trusted)          (proved)          (read-only)
```

1. **Parse** the JSON; the structure is checked (§1, the first four rules). A problem raises
   `AutFormatError`, with the key or state concerned.
2. **Build** an `Automaton` (`from_dict`). This is plain trusted code; it decides nothing about
   validity.
3. **Encode** it into the lists the verified code works on (numbered events, transitions grouped
   by state and sorted by event; `core_aut/trusted/encoding.py`).
4. **Check** with the **verified** checker, once. A problem raises `InvalidAutomatonError`, with
   the condition (e.g. "W1").
5. **Return** a `ValidAutomaton` that keeps the checked encoding, read-only, plus the names and
   labels.

The `Automaton` from step 2 is temporary. The `ValidAutomaton` stores the automaton **once**, in
encoded form. `V.states`, `V.events`, `V.init`, … are views computed from it when asked for, not
second copies. The user sees names, labels and states as in an `Automaton`; the operations use
the encoding.

**Why validity is safe even though the reader is not verified:** the reader only builds; the
verified checker decides. A bug in the reader becomes an error message, never an invalid
automaton passed to verified code. That is also why new readers (e.g. CIF) can be added without
growing what has to be trusted. See `VERIFICATION.md` §3 and §6.

## 4. Writing

`write_aut(G, path)` writes a `ValidAutomaton` or an `Automaton` in the format of §1:
- one key per line;
- one source state per line under `"transitions"`;
- event lists sorted;
- a single target as a string, several as a list.

Writing needs unique string state names and string event labels; otherwise it raises
`AutFormatError`.

`to_dict(G)` and `from_dict(d)` do the same without files, e.g. to embed an automaton in
another JSON document.

Reading what was written gives the same automaton (tested on 100 random automata).

## 5. DESUMA `.fsm` models

`read_fsm(path)` imports the classic format, for existing models. It returns a `ValidAutomaton`,
validated like `read_aut`. To convert a model once:

```python
write_aut(read_fsm("M1.fsm"), "M1.json")
```

The `.fsm` format is more limited than certisc's:
- exactly one initial state, the first state listed;
- no events without transitions;
- controllability and observability given per transition. An event marked `uc` (or `uo`) on any
  transition is uncontrollable (or unobservable).

A malformed file raises `FsmFormatError`.

## 6. Errors

| Error | Meaning | Example |
|---|---|---|
| `AutFormatError` | the file does not follow the format | unknown key `"intial"`; a target not in `"states"` |
| `FsmFormatError` | the `.fsm` file is malformed | a state announces 2 transitions but lists 1 |
| `InvalidAutomatonError` | well-formed file, but not a valid automaton (verified checker) | a transition on an event missing from `"events"` (W1); no initial state (W3) |

## 7. Examples

`Examples/v2/testing/certisc/` (outer repository):
- `04_read_write.py`: `.fsm` → JSON → read back → edit a copy → validate;
- `02_next_states.py`, `03_reachable.py`: use models read from `models/*.json`.
