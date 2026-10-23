"""
certisc's file format for automata: JSON, transitions grouped by source state.

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

- "states" fixes the state order (state i is states[i]); names are unique strings.
- "transitions": source -> {event: target}; a list of targets for a nondeterministic event,
  e.g. {"a": ["x1", "x2"]}. States without transitions may be left out.
- "events" is optional: if left out, E = the events of the transitions, plus "uncontrollable"
  and "unobservable". If given, every transition must use one of them (else the verified
  checker rejects the automaton: W1).
- "uncontrollable", "unobservable", "marked" are optional (default: empty).

Trusted code: it only builds the automaton. read_aut then validates it with the verified
checker and returns a ValidAutomaton.
"""

import json
from typing import Any, Dict, Union

from core_aut import Automaton, ValidAutomaton, validate

_KEYS = {"events", "uncontrollable", "unobservable", "states", "initial", "marked", "transitions"}


class AutFormatError(ValueError):
    """The file is not in certisc's automaton format (a structural error, before validity)."""


def _names(d: Dict[str, Any], key: str) -> list:
    value = d.get(key, [])
    if not isinstance(value, list) or not all(isinstance(v, str) for v in value):
        raise AutFormatError(f'"{key}" must be a list of strings')
    return value


def from_dict(d: Dict[str, Any]) -> Automaton:
    """Build an Automaton from the format above (not yet validated)."""
    if not isinstance(d, dict):
        raise AutFormatError("the top level must be a JSON object")
    unknown = set(d) - _KEYS
    if unknown:
        raise AutFormatError(f"unknown keys: {sorted(unknown)}; allowed: {sorted(_KEYS)}")
    for key in ("states", "initial", "transitions"):
        if key not in d:
            raise AutFormatError(f'missing "{key}"')
    states = _names(d, "states")
    if len(set(states)) != len(states):
        raise AutFormatError('"states" has repeated names')
    index = {name: i for i, name in enumerate(states)}

    def state(name: Any, where: str) -> int:
        if name not in index:
            raise AutFormatError(f"{where}: {name!r} is not in \"states\"")
        return index[name]

    trans = d["transitions"]
    if not isinstance(trans, dict):
        raise AutFormatError('"transitions" must be an object: source -> {event: target}')
    moves = []                                   # (source, event, target)
    for src, out in trans.items():
        x = state(src, '"transitions"')
        if not isinstance(out, dict):
            raise AutFormatError(f'"transitions" of {src!r} must be an object: event -> target')
        for event, targets in out.items():
            if isinstance(targets, str):
                targets = [targets]
            if not isinstance(targets, list) or not targets:
                raise AutFormatError(f"{src!r} --{event}-->: target must be a state name or a "
                                     "non-empty list of state names")
            for t in targets:
                moves.append((x, event, state(t, f"{src!r} --{event}-->")))

    euc, euo = _names(d, "uncontrollable"), _names(d, "unobservable")
    if "events" in d:
        events = _names(d, "events")
    else:
        events = sorted({e for _, e, _ in moves})
    G = Automaton(events=events, Euc=euc, Euo=euo)
    initial = {state(n, '"initial"') for n in _names(d, "initial")}
    marked = {state(n, '"marked"') for n in _names(d, "marked")}
    for i, name in enumerate(states):
        G.add_state(name, i in marked, init=i in initial)
    for x, event, y in moves:
        G.add_transition(x, event, y)
    return G


def to_dict(G: Union[ValidAutomaton, Automaton]) -> Dict[str, Any]:
    """The format above, for a ValidAutomaton or an Automaton with unique string names and
    string events."""
    if isinstance(G, ValidAutomaton):
        names, events, euc, euo = list(G.names), G.events, G.Euc, G.Euo
        init, marked, moves = G.init, G.marked, list(G.transitions())
    else:
        names = [s.name for s in G.states]
        events, euc, euo, init = G.events, G.Euc, G.Euo, G.init
        marked = {x for x, s in enumerate(G.states) if s.marked}
        moves = list(G.transitions())
    if not all(isinstance(n, str) for n in names) or len(set(names)) != len(names):
        raise AutFormatError("writing needs unique string state names")
    if not all(isinstance(e, str) for e in set(events) | set(euc) | set(euo)):
        raise AutFormatError("writing needs string event labels")
    trans: Dict[str, Dict[str, Any]] = {}
    for x, e, y in moves:
        out = trans.setdefault(names[x], {})
        if e in out:
            out[e] = (out[e] if isinstance(out[e], list) else [out[e]]) + [names[y]]
        else:
            out[e] = names[y]
    return {
        "events": sorted(events), "uncontrollable": sorted(euc), "unobservable": sorted(euo),
        "states": names, "initial": [names[x] for x in sorted(init)],
        "marked": [names[x] for x in sorted(marked)],
        "transitions": {names[x]: trans[names[x]] for x in range(len(names)) if names[x] in trans},
    }


def read_aut(path) -> ValidAutomaton:
    """Read an automaton in certisc's JSON format and validate it (verified checker)."""
    with open(path) as f:
        try:
            d = json.load(f)
        except json.JSONDecodeError as err:
            raise AutFormatError(f"{path}: not valid JSON ({err})") from None
    return validate(from_dict(d))


def write_aut(G: Union[ValidAutomaton, Automaton], path) -> None:
    """Write G in certisc's JSON format: one key per line, one source state per line."""
    d = to_dict(G)
    dump = lambda v: json.dumps(v, ensure_ascii=False)     # noqa: E731
    lines = ["{"]
    for key in ("events", "uncontrollable", "unobservable", "states", "initial", "marked"):
        lines.append(f'  "{key}": {dump(d[key])},')
    if d["transitions"]:
        width = max(len(dump(s)) for s in d["transitions"]) + 1
        lines.append('  "transitions": {')
        items = list(d["transitions"].items())
        for i, (src, out) in enumerate(items):
            comma = "," if i + 1 < len(items) else ""
            lines.append(f"    {(dump(src) + ':').ljust(width)} {dump(out)}{comma}")
        lines.append("  }")
    else:
        lines.append('  "transitions": {}')
    lines.append("}")
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")
