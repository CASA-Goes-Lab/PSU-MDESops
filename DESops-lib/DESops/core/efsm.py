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
- decompose() splits the system further, into automata that interact only
  through shared events (see its docstring).
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

    def decompose(self, kind: Optional[str] = None) -> Dict[str, Automaton]:
        """
        Split the system into automata that interact only through shared
        events, so their parallel composition equals unfold(flat=True) (same
        generated and marked language). Per automaton A:

        - "A.guards": guard conjuncts of A that read only other automata move
          into a monitor, which tracks those automata (an unfolded copy that
          follows their events) and allows A's guarded events only where the
          conjuncts hold.
        - "A.x", "A.y,z": A's variables that are never read or updated
          together (in one conjunct, update, or initial/marked predicate)
          become separate automata synchronized on A's events. "A" keeps the
          locations and the variables tied to them; it is left out when it
          constrains nothing. An automaton with one part keeps its name.

        Conditions, else A is unfolded whole with every automaton it reads,
        as unfold() would (key "A+B..."): no conjunct or update mixes A's
        own state with another automaton's, no initial/marked predicate reads
        another automaton, and each event's other-automaton conjuncts are the
        same on all of A's edges for that event. A variable whose conjuncts or
        updates for some event differ between edges stays with the locations.
        kind: only automata of this kind, as in unfold().
        """
        names = [a.name for a in self.automata if kind is None or a.kind == kind]
        result: Dict[str, Automaton] = {}
        for n in names:
            a = self.automaton(n)
            split = _split(a)
            if split is None:
                group = self._closure([n], names)
                result["+".join(group)] = self._unfold_group(group)
                continue
            parts, guards = split
            for suffix, part in parts:
                key = n if len(parts) == 1 or suffix is None else f"{n}.{suffix}"
                result[key] = self._unfold_automata([part])
            if guards is not None:
                tracked = [self.automaton(m) for m in self._closure(_references(guards), names)]
                result[guards.name] = self._unfold_automata(
                    tracked + [guards], hidden={guards.name}
                )
        return result

    def _closure(self, start, names: Sequence[str]) -> List[str]:
        """start plus every automaton they read, transitively, in declaration order."""
        seen, todo = set(start), list(start)
        while todo:
            for other in _references(self.automaton(todo.pop())):
                if other not in names:
                    raise EfsmError(f"{other} is read but is not being unfolded")
                if other not in seen:
                    seen.add(other)
                    todo.append(other)
        return [n for n in names if n in seen]

    # --- unfolding ------------------------------------------------------------

    def _unfold_group(self, names: List[str]) -> Automaton:
        return self._unfold_automata([self.automaton(n) for n in names])

    def _unfold_automata(self, auts: List[Efsm], hidden=frozenset()) -> Automaton:
        """hidden: automata (stateless guard monitors) left out of state names."""
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
            parts = [_state_name(a, s[i]) for i, a in enumerate(auts) if a.name not in hidden]
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


def _expr_atoms(expr: Expr) -> set:
    """(automaton, variable name) for variables, (automaton, None) for locations."""
    tag = expr[0]
    if tag == "var":
        return {(expr[1], expr[2])}
    if tag == "loc":
        return {(expr[1], None)}
    if tag == "lit":
        return set()
    if tag == "un":
        return _expr_atoms(expr[2])
    if tag == "bin":
        return _expr_atoms(expr[2]) | _expr_atoms(expr[3])
    if tag == "if":
        out = _expr_atoms(expr[2])
        for c, v in expr[1]:
            out |= _expr_atoms(c) | _expr_atoms(v)
        return out
    if tag == "call":
        return set().union(*(_expr_atoms(x) for x in expr[2]))
    raise EfsmError(f"unknown expression {expr!r}")


_LOC = "@location"  # a's location, as a component next to its variables


def _split(a: Efsm):
    """
    Parts of a for EfsmSystem.decompose(): ([(suffix, Efsm)], guards Efsm or
    None), or None if a cannot be split from the automata it reads. Suffix
    None is the part holding the locations.
    """

    def own(expr):
        return {_LOC if v is None else v for aut, v in _expr_atoms(expr) if aut == a.name}

    def remote(expr):
        return {aut for aut, _ in _expr_atoms(expr) if aut != a.name}

    parent = {c: c for c in [_LOC] + [v.name for v in a.variables]}

    def find(c):
        while parent[c] != c:
            parent[c] = parent[parent[c]]
            c = parent[c]
        return c

    def union(components):
        components = list(components)
        for c in components[1:]:
            parent[find(c)] = find(components[0])

    several = len(a.locations) > 1
    loc_preds = [x for loc in a.locations for x in (loc.initial or []) + (loc.marked or [])]
    for x in a.initial + a.marked + loc_preds:
        if remote(x):
            return None
    for x in a.initial + a.marked:
        union(own(x))
    for x in loc_preds:
        # With several locations, a location's predicate depends on which one it is.
        union(own(x) | ({_LOC} if several else set()))

    edges = [edge for loc in a.locations for edge in loc.edges]
    remote_guards: Dict[str, Dict[tuple, list]] = {}
    for edge in edges:
        theirs = []
        for x in edge.guard:
            r, o = remote(x), own(x)
            if r and o:
                return None
            if r:
                theirs.append(x)
            else:
                union(o)
        for var, x in edge.updates:
            if remote(x):
                return None
            union({var} | own(x))
        for e in edge.events:
            remote_guards.setdefault(e, {})[tuple(sorted(map(repr, theirs)))] = theirs
    if any(len(options) > 1 for options in remote_guards.values()):
        return None

    def in_part(x, root):
        o = own(x)
        if not o:
            return root == find(_LOC)
        return find(next(iter(o))) == root

    def local(edge, root):
        guard = [x for x in edge.guard if not remote(x) and in_part(x, root)]
        updates = [(v, x) for v, x in edge.updates if find(v) == root]
        return guard, updates

    # A variable group can leave the locations only if, for every event, all
    # edges with that event read and update it the same way.
    changed = True
    while changed:
        changed = False
        for root in {find(v.name) for v in a.variables} - {find(_LOC)}:
            seen: Dict[str, set] = {}
            for edge in edges:
                guard, updates = local(edge, root)
                for e in edge.events:
                    seen.setdefault(e, set()).add(repr((sorted(map(repr, guard)), updates)))
            if any(len(s) > 1 for s in seen.values()):
                union([_LOC, root])
                changed = True
                break

    loc_root = find(_LOC)
    roots = [loc_root]
    for v in a.variables:
        if find(v.name) not in roots:
            roots.append(find(v.name))

    parts = []
    covered = set()  # events constrained by a variable part or the guards
    for root in roots[1:]:
        variables = [v for v in a.variables if find(v.name) == root]
        by_event = {}
        for edge in edges:
            guard, updates = local(edge, root)
            if guard or updates:
                for e in edge.events:
                    by_event.setdefault(e, Edge((e,), guard, updates))
        covered |= set(by_event)
        # Location-level predicates reach here only with a single location
        # (with several, they are tied to the locations above).
        initial = a.initial + [x for loc in a.locations for x in loc.initial or []]
        marked = a.marked + [x for loc in a.locations for x in loc.marked or []]
        part = Efsm(
            a.name,
            a.kind,
            [Location(None, initial=[], marked=[], edges=list(by_event.values()))],
            variables,
            set(by_event),
            initial=[x for x in initial if in_part(x, root)],
            marked=[x for x in marked if in_part(x, root)],
        )
        parts.append((",".join(v.name for v in variables), part))

    guards = None
    theirs = {e: next(iter(options.values())) for e, options in remote_guards.items()}
    theirs = {e: g for e, g in theirs.items() if g}
    if theirs:
        guards = Efsm(
            f"{a.name}.guards",
            a.kind,
            [Location(None, initial=[], marked=[],
                      edges=[Edge((e,), list(g)) for e, g in theirs.items()])],
            alphabet=set(theirs),
        )
        covered |= set(theirs)

    def keep(preds):
        return None if preds is None else [x for x in preds if in_part(x, loc_root)]

    locations = [
        Location(
            loc.name,
            keep(loc.initial),
            keep(loc.marked),
            [Edge(edge.events, *local(edge, loc_root), edge.target) for edge in loc.edges],
        )
        for loc in a.locations
    ]
    main = Efsm(
        a.name,
        a.kind,
        locations,
        [v for v in a.variables if find(v.name) == loc_root],
        set(a.alphabet),
        initial=[x for x in a.initial if in_part(x, loc_root)],
        marked=[x for x in a.marked if in_part(x, loc_root)],
    )
    with_edges = {e for edge in a.locations[0].edges for e in edge.events} if a.locations else set()
    trivial = (
        len(locations) == 1
        and not main.variables
        and locations[0].initial == []
        and locations[0].marked == []
        and not main.initial
        and not main.marked
        and all(not edge.guard and not edge.updates for edge in locations[0].edges)
        and main.alphabet <= with_edges
        and main.alphabet <= covered
    )
    if not trivial:
        parts.insert(0, (None, main))
    return parts, guards


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
