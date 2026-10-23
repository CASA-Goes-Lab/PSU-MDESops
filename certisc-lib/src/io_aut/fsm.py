"""
Import of DESUMA .fsm models (read only), for existing models.

Format: the number of states on the first line; then, for each state, a line
"name  marked  number_of_transitions", followed by one line per transition
"event  target  c|uc  o|uo". The first state listed is the initial state. Controllability and
observability are given per transition; an event marked "uc" (or "uo") anywhere is
uncontrollable (or unobservable).

Trusted code: it only builds the automaton; read_fsm validates it with the verified checker.
"""

from core_aut import Automaton, ValidAutomaton, validate


class FsmFormatError(ValueError):
    """The file is not a well-formed .fsm file."""


def read_fsm(path) -> ValidAutomaton:
    with open(path) as f:
        lines = [(no, line.split()) for no, line in enumerate(f, 1) if line.strip()]
    try:
        n = int(lines[0][1][0])
        blocks, i = [], 1
        for _ in range(n):
            no, head = lines[i]
            name, marked, count = head[0], head[1] == "1", int(head[2])
            trans = [t for _, t in lines[i + 1:i + 1 + count]]
            if len(trans) != count or any(len(t) != 4 for t in trans):
                raise FsmFormatError(f"{path}, line {no}: state {name!r} announces {count} "
                                     "transitions of 4 fields each")
            blocks.append((name, marked, trans))
            i += 1 + count
    except (IndexError, ValueError) as err:
        if isinstance(err, FsmFormatError):
            raise
        raise FsmFormatError(f"{path}: not a well-formed .fsm file ({err})") from None
    names = [b[0] for b in blocks]
    if len(set(names)) != len(names):
        raise FsmFormatError(f"{path}: repeated state names")
    index = {name: k for k, name in enumerate(names)}
    events, euc, euo = set(), set(), set()
    for _, _, trans in blocks:
        for event, target, c, o in trans:
            if target not in index:
                raise FsmFormatError(f"{path}: transition to unknown state {target!r}")
            events.add(event)
            if c == "uc":
                euc.add(event)
            if o == "uo":
                euo.add(event)
    G = Automaton(events=events, Euc=euc, Euo=euo)
    for k, (name, marked, _) in enumerate(blocks):
        G.add_state(name, marked, init=(k == 0))
    for name, _, trans in blocks:
        for event, target, _, _ in trans:
            G.add_transition(index[name], event, index[target])
    return validate(G)
