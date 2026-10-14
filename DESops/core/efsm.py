"""
Extended finite-state machines (EFSMs): automata with locations, bounded
discrete variables, and edges carrying events, guards and updates.

This is the format-independent model that readers such as DESops.io.cif
produce, and unfold() turns into DESops Automaton objects.

- An EfsmSystem holds events (with controllability) and automata.
- Automata synchronize on shared events, as in parallel(): an event occurs
  only if every automaton with it in its alphabet has an enabled edge for it.
  Guards are evaluated, and all updates computed, in the state before the
  event.
- A guard may read other automata's locations and variables; an automaton
  only updates its own variables.
- Expressions are tuples: ("lit", value), ("var", automaton, name),
  ("loc", automaton, location), ("un", op, e), ("bin", op, a, b),
  ("if", [(cond, value), ...], else_value), ("call", function, [args]).

Unfolding:
- unfold() unfolds each group of linked automata on its own. Two automata are
  linked when an expression of one reads the other's location or variable;
  shared events alone do not link them (parallel() handles those).
- unfold(flat=True) unfolds the whole system into one automaton.
Only reachable states are built. An update outside a variable's range raises
EfsmError: guard the edge instead.
"""

import itertools
import operator
from collections import deque
from dataclasses import dataclass, field
from typing import Any, Callable, Dict, List, Optional, Sequence, Tuple

from DESops.core.automaton import Automaton
from DESops.core.event import Event
from DESops.error import EfsmError

Expr = tuple


@dataclass
class Variable:
    name: str
    kind: str  # "int", "bool" or "enum"
    domain: Tuple  # (lo, hi) for int; the literals for enum; () for bool
    init: Any

    def contains(self, value) -> bool:
        if self.kind == "int":
            lo, hi = self.domain
            return isinstance(value, int) and not isinstance(value, bool) and lo <= value <= hi
        if self.kind == "bool":
            return isinstance(value, bool)
        return value in self.domain


@dataclass
class Edge:
    events: Tuple[str, ...]
    guard: List[Expr] = field(default_factory=list)  # conjunction
    updates: List[Tuple[str, Expr]] = field(default_factory=list)
    target: Optional[str] = None  # None: stay in the same location


@dataclass
class Location:
    name: Optional[str]  # None for CIF's nameless location
    initial: Optional[List[Expr]] = None  # None: not initial; []: always
    marked: Optional[List[Expr]] = None  # None: not marked; []: always
    edges: List[Edge] = field(default_factory=list)


@dataclass
class Efsm:
    name: str
    kind: str = "plant"  # "plant", "requirement" or "supervisor"
    locations: List[Location] = field(default_factory=list)
    variables: List[Variable] = field(default_factory=list)
    alphabet: set = field(default_factory=set)  # event names
    initial: List[Expr] = field(default_factory=list)  # automaton-level
    marked: List[Expr] = field(default_factory=list)  # automaton-level

    def expressions(self):
        yield from self.initial
        yield from self.marked
        for loc in self.locations:
            yield from loc.initial or ()
            yield from loc.marked or ()
            for edge in loc.edges:
                yield from edge.guard
                for _, value in edge.updates:
                    yield value


@dataclass
class EfsmSystem:
    events: Dict[str, bool]  # name -> controllable
    automata: List[Efsm]

    def automaton(self, name: str) -> Efsm:
        for a in self.automata:
            if a.name == name:
                return a
        raise KeyError(name)

    def groups(self, names: Optional[Sequence[str]] = None) -> List[List[str]]:
        """Automata linked through expressions, in declaration order."""
        names = [a.name for a in self.automata] if names is None else list(names)
        parent = {n: n for n in names}

        def find(n):
            while parent[n] != n:
                parent[n] = parent[parent[n]]
                n = parent[n]
            return n

        for n in names:
            for other in _references(self.automaton(n)):
                if other not in parent:
                    raise EfsmError(f"{n} reads {other}, which is not being unfolded")
                parent[find(other)] = find(n)
        out: Dict[str, List[str]] = {}
        for n in names:
            out.setdefault(find(n), []).append(n)
        return list(out.values())

    def unfold(self, flat: bool = False, kind: Optional[str] = None):
        """
        flat=False: {group name: Automaton}, one per group of linked automata
        (group name is the member names joined by '+').
        flat=True: one Automaton for the whole system.
        kind: only unfold automata of this kind ("plant", "requirement", ...).
        """
        names = [a.name for a in self.automata if kind is None or a.kind == kind]
        if flat:
            return self._unfold_group(names)
        result = {}
        for group in self.groups(names):
            kinds = {self.automaton(n).kind for n in group}
            if len(kinds) > 1:
                raise EfsmError(f"automata of different kinds are linked: {group}")
            result["+".join(group)] = self._unfold_group(group)
        return result

    # --- unfolding ------------------------------------------------------------

    def _unfold_group(self, names: List[str]) -> Automaton:
        auts = [self.automaton(n) for n in names]
        # ("loc", aut) -> i; ("locidx", aut, location) -> k; ("var", aut, var) -> (i, j)
        pos = {}
        for i, a in enumerate(auts):
            pos["loc", a.name] = i
            for k, loc in enumerate(a.locations):
                pos["locidx", a.name, loc.name] = k
            for j, v in enumerate(a.variables):
                pos["var", a.name, v.name] = (i, j)

        def comp(expr):
            return _compile(expr, pos)

        alphabet = sorted(set().union(*(a.alphabet for a in auts))) if auts else []
        events = {e: Event(e) for e in alphabet}
        g = Automaton(
            events=events.values(),
            Euc={events[e] for e in alphabet if not self.events.get(e, True)},
        )
        if not auts:
            return g

        # Per automaton: location name -> (index, compiled edges by event, marked fn)
        tables = []
        for a in auts:
            loc_index = {loc.name: k for k, loc in enumerate(a.locations)}
            by_event = []
            marked = []
            for loc in a.locations:
                edges = {}
                for edge in loc.edges:
                    guard = [comp(x) for x in edge.guard]
                    updates = [(_var_index(a, var), comp(x), var) for var, x in edge.updates]
                    target = loc_index[loc.name if edge.target is None else edge.target]
                    for e in edge.events:
                        edges.setdefault(e, []).append((guard, updates, target))
                by_event.append(edges)
                if loc.marked is None:
                    marked.append(None)
                else:
                    marked.append([comp(x) for x in loc.marked + a.marked])
            tables.append((by_event, marked))

        participants = {
            e: [i for i, a in enumerate(auts) if e in a.alphabet] for e in alphabet
        }

        def name(s):
            parts = [_state_name(a, s[i]) for i, a in enumerate(auts)]
            return parts[0] if len(parts) == 1 else tuple(parts)

        def is_marked(s):
            for i, (_, marked) in enumerate(tables):
                preds = marked[s[i][0]]
                if preds is None or not all(p(s) for p in preds):
                    return False
            return True

        index = {}
        queue = deque()

        def visit(s):
            if s not in index:
                index[s] = g.add_state(name(s), is_marked(s))
                queue.append(s)
            return index[s]

        for s in self._initial_states(auts, comp):
            g.init.add(visit(s))

        while queue:
            s = queue.popleft()
            source = index[s]
            for e in alphabet:
                options = []
                for i in participants[e]:
                    loc = s[i][0]
                    enabled = [
                        (i, upd, tgt)
                        for guard, upd, tgt in tables[i][0][loc].get(e, ())
                        if all(p(s) for p in guard)
                    ]
                    if not enabled:
                        break
                    options.append(enabled)
                else:
                    for combo in itertools.product(*options):
                        new = list(s)
                        for i, updates, target in combo:
                            values = list(s[i][1])
                            for j, fn, var in updates:
                                value = fn(s)
                                variable = auts[i].variables[j]
                                if not variable.contains(value):
                                    raise EfsmError(
                                        f"{auts[i].name}.{var} := {value!r} is outside its "
                                        f"range, on event {e} from state {name(s)!r}; "
                                        f"add a guard to that edge"
                                    )
                                values[j] = value
                            new[i] = (target, tuple(values))
                        g.add_transition(source, events[e], visit(tuple(new)))
        return g

    def _initial_states(self, auts, comp):
        candidates = []
        for a in auts:
            values = tuple(v.init for v in a.variables)
            locs = [k for k, loc in enumerate(a.locations) if loc.initial is not None]
            if not locs:
                raise EfsmError(f"{a.name} has no initial location")
            candidates.append([(k, values) for k in locs])
        checks = []
        for i, a in enumerate(auts):
            checks.append(
                (i, {k: [comp(x) for x in loc.initial + a.initial]
                     for k, loc in enumerate(a.locations) if loc.initial is not None})
            )
        for s in itertools.product(*candidates):
            if all(all(p(s) for p in preds[s[i][0]]) for i, preds in checks):
                yield s


# --- expressions --------------------------------------------------------------

_BINARY: Dict[str, Callable] = {
    "+": operator.add,
    "-": operator.sub,
    "*": operator.mul,
    "/": operator.truediv,
    "div": lambda a, b: int(a / b),
    "mod": lambda a, b: a - b * int(a / b),
    "=": operator.eq,
    "!=": operator.ne,
    "<": operator.lt,
    "<=": operator.le,
    ">": operator.gt,
    ">=": operator.ge,
}
_FUNCTIONS: Dict[str, Callable] = {"abs": abs, "min": min, "max": max}


def _compile(expr: Expr, pos) -> Callable:
    tag = expr[0]
    if tag == "lit":
        value = expr[1]
        return lambda s: value
    if tag == "var":
        try:
            i, j = pos["var", expr[1], expr[2]]
        except KeyError:
            raise EfsmError(f"{expr[1]}.{expr[2]} is not part of this unfolding")
        return lambda s: s[i][1][j]
    if tag == "loc":
        _, aut, loc = expr
        try:
            i, k = pos["loc", aut], pos["locidx", aut, loc]
        except KeyError:
            raise EfsmError(f"{aut}.{loc} is not part of this unfolding")
        return lambda s: s[i][0] == k
    if tag == "un":
        op, arg = expr[1], _compile(expr[2], pos)
        if op == "not":
            return lambda s: not arg(s)
        if op == "-":
            return lambda s: -arg(s)
        return arg
    if tag == "bin":
        op, a, b = expr[1], _compile(expr[2], pos), _compile(expr[3], pos)
        if op == "and":
            return lambda s: a(s) and b(s)
        if op == "or":
            return lambda s: a(s) or b(s)
        if op == "=>":
            return lambda s: (not a(s)) or b(s)
        if op == "<=>":
            return lambda s: bool(a(s)) == bool(b(s))
        fn = _BINARY[op]
        return lambda s: fn(a(s), b(s))
    if tag == "if":
        branches = [(_compile(c, pos), _compile(v, pos)) for c, v in expr[1]]
        other = _compile(expr[2], pos)

        def choose(s):
            for c, v in branches:
                if c(s):
                    return v(s)
            return other(s)

        return choose
    if tag == "call":
        fn = _FUNCTIONS[expr[1]]
        args = [_compile(x, pos) for x in expr[2]]
        return lambda s: fn(*(x(s) for x in args))
    raise EfsmError(f"unknown expression {expr!r}")


def evaluate_constant(expr: Expr):
    """Value of an expression that reads no location or variable."""
    if _expr_refs(expr):
        raise EfsmError(f"not a constant expression: {expr!r}")
    return _compile(expr, {})(())


def _expr_refs(expr: Expr) -> set:
    tag = expr[0]
    if tag in ("var", "loc"):
        return {expr[1]}
    if tag == "lit":
        return set()
    if tag == "un":
        return _expr_refs(expr[2])
    if tag == "bin":
        return _expr_refs(expr[2]) | _expr_refs(expr[3])
    if tag == "if":
        out = _expr_refs(expr[2])
        for c, v in expr[1]:
            out |= _expr_refs(c) | _expr_refs(v)
        return out
    if tag == "call":
        return set().union(*(_expr_refs(x) for x in expr[2]))
    raise EfsmError(f"unknown expression {expr!r}")


def _references(a: Efsm) -> set:
    out = set()
    for expr in a.expressions():
        out |= _expr_refs(expr)
    out.discard(a.name)
    return out


def _var_index(a: Efsm, var: str) -> int:
    for j, v in enumerate(a.variables):
        if v.name == var:
            return j
    raise EfsmError(f"{a.name} updates {var}, which is not one of its variables")


def _format(value) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    return str(value)


def _state_name(a: Efsm, local) -> str:
    k, values = local
    loc = a.locations[k].name
    if not a.variables:
        return loc
    vars_ = ", ".join(f"{v.name}={_format(x)}" for v, x in zip(a.variables, values))
    return vars_ if loc is None else f"{loc}({vars_})"
