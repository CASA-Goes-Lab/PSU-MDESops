"""
Read a DESUMA .fsm file into a DESops.core.automaton.Automaton.

Format (tab-separated):
    <number of states>
    <blank line>
    STATE   MARKED(0/1)   NUM_TRANSITIONS
    EVENT   TARGET   c|uc   o|uo   [PROB]
    ...

The first state listed is the initial state. A transition line with a fifth
column (probability) makes the automaton probabilistic (PFA). Controllability
and observability are recorded per event in Euc/Euo, not per transition.
"""

import ast
from typing import Any, Dict, List

from DESops import error
from DESops.core.automaton import Automaton
from DESops.core.event import Event


def _parse_name(text: str) -> Any:
    return ast.literal_eval(text) if text.startswith("(") else text


def read_automaton(path: str) -> Automaton:
    states: List[tuple] = []  # (name, marked)
    transitions: List[tuple] = []  # (source name, event, target name, prob)
    euc, euo = set(), set()
    probabilistic = None

    with open(path, "r") as f:
        lines = [line.rstrip("\r\n") for line in f]

    try:
        declared = int(lines[0])
    except (IndexError, ValueError):
        raise error.FileFormatError(f"{path}: first line must be the number of states")

    i = 1
    while i < len(lines):
        line = lines[i]
        i += 1
        if not line.strip():
            continue
        fields = line.split("\t")
        if len(fields) < 3:
            raise error.FileFormatError(
                f"{path} line {i}: state lines are STATE\\tMARKED\\t#TRANSITIONS"
            )
        try:
            count = int(fields[2])
        except ValueError:
            raise error.FileFormatError(
                f"{path} line {i}: expected an integer number of transitions"
            )
        source = _parse_name(fields[0])
        states.append((source, fields[1] == "1"))

        for _ in range(count):
            if i >= len(lines) or not lines[i].strip():
                raise error.FileFormatError(
                    f"{path}: state {source!r} declares {count} transitions but has fewer"
                )
            t = lines[i].split("\t")
            i += 1
            if len(t) not in (4, 5):
                raise error.FileFormatError(
                    f"{path} line {i}: transitions are EVENT\\tTARGET\\tc|uc\\to|uo[\\tPROB]"
                )
            is_prob = len(t) == 5
            if probabilistic is None:
                probabilistic = is_prob
            elif probabilistic != is_prob:
                raise error.FileFormatError(
                    f"{path} line {i}: mixes probabilistic and non-probabilistic transitions"
                )

            event = Event(t[0])
            if t[2] == "uc":
                euc.add(event)
            if t[3] == "uo":
                euo.add(event)
            prob = None
            if is_prob:
                try:
                    prob = float(t[4])
                except ValueError:
                    prob = -1.0
                if not 0 <= prob <= 1:
                    raise error.FileFormatError(
                        f"{path} line {i}: probability must be between 0 and 1"
                    )
            transitions.append((source, event, _parse_name(t[1]), prob))

    if len(states) != declared:
        raise error.FileFormatError(
            f"{path}: declares {declared} states but lists {len(states)}"
        )

    g = Automaton(Euc=euc, Euo=euo, probabilistic=bool(probabilistic))
    for name, marked in states:
        g.add_state(name, marked)
    if states:
        g.init.add(0)

    index = _name_index([name for name, _ in states])
    for source, event, target, prob in transitions:
        g.add_transition(index(source), event, index(target), prob)
    return g


def _name_index(names: List[Any]):
    """name -> index; falls back to a linear search for unhashable names."""
    table: Dict[Any, int] = {}
    for i, name in enumerate(names):
        try:
            table.setdefault(name, i)
        except TypeError:
            pass

    def lookup(name: Any) -> int:
        try:
            return table[name]
        except (TypeError, KeyError):
            try:
                return names.index(name)
            except ValueError:
                raise error.FileFormatError(f"transition to undeclared state {name!r}")

    return lookup
