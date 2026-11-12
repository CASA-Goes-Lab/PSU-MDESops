"""
EFSMs (extended finite-state machines): the syntax.

Mirrors certisc-proof/DESopsProof/Efsm.lean (spec: certisc-proof/spec/efsm.md §2), with names
instead of indices. The meaning (which states and transitions a system has) is defined in
Lean and computed by the verified Rust unfolder (later); this module only holds and checks the
model. Reference: the extended finite automata of Sköldstam, Åkesson & Fabian (CDC 2007).

    Expressions   Lit(3), Var("Room.T"), AtLoc("Load", "Low"), Un("not", x), Bin("add", x, y),
                  Ite(c, t, e). Integers; booleans are 0 / 1, and any nonzero value is true.
    Variable      name, range [lo, hi], initial value (bool: [0, 1]; enum: literal names).
    Edge          source --event / guard / updates--> target. `updates` maps a variable name to
                  its new value; a variable not in it is "not written" (Ξ), which is not the
                  same as writing `x := x` (spec Example 4).
    Efsm          locations, initial locations, alphabet, marked predicate, edges, kind
                  (plant / requirement).
    EfsmSystem    events (with Euc, Euo), the variables (shared by all EFSMs, as in the paper:
                  any EFSM may read or write any variable), the EFSMs.

EfsmSystem.check() checks the model is well formed as syntax (names resolve, ranges, alphabets).
Plain Python, trusted: the unfolder re-checks what it relies on.
"""

from dataclasses import dataclass, field
from typing import Dict, Iterable, List, Optional, Set, Tuple, Union

UNARY = ("not", "neg", "abs")
BINARY = ("and", "or", "imp", "iff", "eq", "ne", "lt", "le", "gt", "ge",
          "add", "sub", "mul", "div", "mod", "min", "max")


INT_MIN, INT_MAX = -2 ** 31, 2 ** 31 - 1
"""CIF's integers are 32-bit (Java int); Lean intMin / intMax. Every value an expression
computes must lie in [INT_MIN, INT_MAX] (else an overflow error), and so must every variable
range."""


class EfsmError(ValueError):
    """The EFSM model is not well formed."""


# --- expressions -------------------------------------------------------------------------

@dataclass(frozen=True)
class Lit:
    """An integer constant (true = 1, false = 0)."""
    value: int

    def __post_init__(self):
        if isinstance(self.value, bool):
            object.__setattr__(self, "value", int(self.value))
        if not isinstance(self.value, int):
            raise EfsmError(f"a literal must be an integer, not {self.value!r}")


@dataclass(frozen=True)
class Var:
    """The value of a system variable."""
    name: str


@dataclass(frozen=True)
class AtLoc:
    """1 if EFSM `automaton` is at `location`, else 0 (CIF's A.L)."""
    automaton: str
    location: str


@dataclass(frozen=True)
class Un:
    op: str
    arg: "Expr"

    def __post_init__(self):
        if self.op not in UNARY:
            raise EfsmError(f"unknown unary operator {self.op!r} (one of {UNARY})")


@dataclass(frozen=True)
class Bin:
    op: str
    left: "Expr"
    right: "Expr"

    def __post_init__(self):
        if self.op not in BINARY:
            raise EfsmError(f"unknown binary operator {self.op!r} (one of {BINARY})")


@dataclass(frozen=True)
class Ite:
    """if cond then then_ else other."""
    cond: "Expr"
    then_: "Expr"
    other: "Expr"


Expr = Union[Lit, Var, AtLoc, Un, Bin, Ite]
TRUE, FALSE = Lit(1), Lit(0)

_SYMBOL = {"and": "and", "or": "or", "imp": "=>", "iff": "<=>", "eq": "=", "ne": "!=",
           "lt": "<", "le": "<=", "gt": ">", "ge": ">=", "add": "+", "sub": "-", "mul": "*",
           "div": "div", "mod": "mod"}


def conj(xs: Iterable[Expr]) -> Expr:
    """x1 and x2 and ... (TRUE if empty)."""
    out = None
    for x in xs:
        out = x if out is None else Bin("and", out, x)
    return TRUE if out is None else out


def disj(xs: Iterable[Expr]) -> Expr:
    """x1 or x2 or ... (FALSE if empty)."""
    out = None
    for x in xs:
        out = x if out is None else Bin("or", out, x)
    return FALSE if out is None else out


def text(e: Expr) -> str:
    """The expression in CIF-like notation, fully parenthesized (for messages)."""
    if isinstance(e, Lit):
        return str(e.value)
    if isinstance(e, Var):
        return e.name
    if isinstance(e, AtLoc):
        return f"{e.automaton}.{e.location}"
    if isinstance(e, Un):
        return {"not": "not ", "neg": "-"}.get(e.op, e.op) + (
            f"({text(e.arg)})" if e.op == "abs" else text(e.arg))
    if isinstance(e, Bin):
        if e.op in ("min", "max"):
            return f"{e.op}({text(e.left)}, {text(e.right)})"
        return f"({text(e.left)} {_SYMBOL[e.op]} {text(e.right)})"
    if isinstance(e, Ite):
        return f"(if {text(e.cond)}: {text(e.then_)} else {text(e.other)} end)"
    raise EfsmError(f"not an expression: {e!r}")


def reads(e: Expr) -> Tuple[Set[str], Set[str]]:
    """(variables read, EFSMs whose location is tested) by e."""
    variables: Set[str] = set()
    automata: Set[str] = set()
    stack = [e]
    while stack:
        x = stack.pop()
        if isinstance(x, Var):
            variables.add(x.name)
        elif isinstance(x, AtLoc):
            automata.add(x.automaton)
        elif isinstance(x, Un):
            stack.append(x.arg)
        elif isinstance(x, Bin):
            stack += [x.left, x.right]
        elif isinstance(x, Ite):
            stack += [x.cond, x.then_, x.other]
        elif not isinstance(x, Lit):
            raise EfsmError(f"not an expression: {x!r}")
    return variables, automata


# --- variables, edges, EFSMs, systems -----------------------------------------------------

@dataclass
class Variable:
    """A system variable with range [lo, hi] and an initial value. kind "int", "bool" (range
    [0, 1]) or "enum" (value i is literals[i - lo]; lo = 0)."""
    name: str
    lo: int
    hi: int
    init: int
    kind: str = "int"
    literals: Tuple[str, ...] = ()

    def show(self, value: int) -> str:
        """value as written in the model: an int, false/true, or an enum literal."""
        if self.kind == "bool":
            return "true" if value else "false"
        if self.kind == "enum":
            return self.literals[value - self.lo]
        return str(value)


@dataclass
class Edge:
    """source --event / guard / updates--> target (target None: the source)."""
    source: str
    event: str
    guard: Tuple[Expr, ...] = ()
    updates: Dict[str, Expr] = field(default_factory=dict)
    target: Optional[str] = None

    def __post_init__(self):
        self.guard = tuple(self.guard)
        if self.target is None:
            self.target = self.source


@dataclass
class Efsm:
    """One EFSM. `marked` is a predicate over the state (spec G1); TRUE marks every state."""
    name: str
    locations: List[str]
    initial: Set[str]
    alphabet: Set[str]
    edges: List[Edge] = field(default_factory=list)
    marked: Expr = TRUE
    kind: str = "plant"


@dataclass
class EfsmSystem:
    """EFSMs sharing the variables, synchronizing on shared events (spec §3)."""
    events: List[str]
    variables: List[Variable]
    automata: List[Efsm]
    Euc: Set[str] = field(default_factory=set)
    Euo: Set[str] = field(default_factory=set)

    def variable(self, name: str) -> Variable:
        for v in self.variables:
            if v.name == name:
                return v
        raise KeyError(name)

    def automaton(self, name: str) -> Efsm:
        for a in self.automata:
            if a.name == name:
                return a
        raise KeyError(name)

    def writers(self, name: str) -> List[str]:
        """The EFSMs with an edge that writes variable `name`."""
        return [a.name for a in self.automata if any(name in e.updates for e in a.edges)]

    def check(self) -> "EfsmSystem":
        """Raise EfsmError unless the model is well formed as syntax; return self."""
        _unique("event", self.events)
        _unique("variable", [v.name for v in self.variables])
        _unique("EFSM", [a.name for a in self.automata])
        events = set(self.events)
        for which, s in (("uncontrollable", self.Euc), ("unobservable", self.Euo)):
            if not set(s) <= events:
                raise EfsmError(f"{which} events not declared: {sorted(set(s) - events)}")
        for v in self.variables:
            if not INT_MIN <= v.lo <= v.hi <= INT_MAX:
                raise EfsmError(f"variable {v.name}: range [{v.lo}, {v.hi}] is empty or not "
                                f"within the 32-bit integers [{INT_MIN}, {INT_MAX}]")
            if not v.lo <= v.init <= v.hi:
                raise EfsmError(f"variable {v.name}: initial value {v.init} is outside "
                                f"[{v.lo}, {v.hi}]")
        variables = {v.name for v in self.variables}
        locations = {a.name: set(a.locations) for a in self.automata}

        def expr_ok(e, where):
            vs, auts = reads(e)
            if vs - variables:
                raise EfsmError(f"{where}: unknown variable(s) {sorted(vs - variables)}")
            for x in _atlocs(e):
                if x.automaton not in locations:
                    raise EfsmError(f"{where}: unknown EFSM {x.automaton} in {text(x)}")
                if x.location not in locations[x.automaton]:
                    raise EfsmError(f"{where}: {x.automaton} has no location {x.location}")

        for a in self.automata:
            if a.kind not in ("plant", "requirement", "supervisor"):
                raise EfsmError(f"{a.name}: unknown kind {a.kind!r}")
            if not a.locations:
                raise EfsmError(f"{a.name} has no locations")
            _unique(f"{a.name}: location", a.locations)
            if not a.initial:
                raise EfsmError(f"{a.name} has no initial location")
            if not a.initial <= set(a.locations):
                raise EfsmError(f"{a.name}: unknown initial location(s) "
                                f"{sorted(a.initial - set(a.locations))}")
            if not a.alphabet <= events:
                raise EfsmError(f"{a.name}: alphabet events not declared: "
                                f"{sorted(a.alphabet - events)}")
            expr_ok(a.marked, f"{a.name}, marked")
            for e in a.edges:
                where = f"{a.name}, edge {e.source} --{e.event}--> {e.target}"
                if e.source not in locations[a.name] or e.target not in locations[a.name]:
                    raise EfsmError(f"{where}: unknown location")
                if e.event not in a.alphabet:
                    raise EfsmError(f"{where}: event not in the alphabet of {a.name}")
                if set(e.updates) - variables:
                    raise EfsmError(f"{where}: writes unknown variable(s) "
                                    f"{sorted(set(e.updates) - variables)}")
                for g in e.guard:
                    expr_ok(g, where)
                for x in e.updates.values():
                    expr_ok(x, where)
        return self


def _unique(what, names):
    seen = set()
    for n in names:
        if n in seen:
            raise EfsmError(f"{what} {n!r} declared twice")
        seen.add(n)


def _atlocs(e):
    stack, out = [e], []
    while stack:
        x = stack.pop()
        if isinstance(x, AtLoc):
            out.append(x)
        elif isinstance(x, Un):
            stack.append(x.arg)
        elif isinstance(x, Bin):
            stack += [x.left, x.right]
        elif isinstance(x, Ite):
            stack += [x.cond, x.then_, x.other]
    return out
