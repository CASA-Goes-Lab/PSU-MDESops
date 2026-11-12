"""
Read CIF 3 models (Eclipse ESCET) into an EFSM system (core_aut.efsm.EfsmSystem).

    model = read_cif("model.cif")       # a checked EfsmSystem
    model = parse_cif(text)             # the same, from a string

This is the only module that knows CIF: it translates CIF into the EFSM syntax of
certisc-proof/spec/efsm.md (§7.1). CIF models are a subset of EFSMs: each discrete variable is
written only by its own automaton, updates use the state before the step, an update out of
range is an error, as in the EFSM meaning. Trusted code (it decides what the text means).

Supported now (the rest raises UnsupportedCifError, never skipped):
    controllable a, b;  uncontrollable c;  event e;      (plain event: controllable)
    const int N = 2;  const bool B = true;  alg int x = <expr>;  enum Mode = Off, On;
    [plant|requirement|supervisor] [automaton] Name: ... end
    [plant|requirement|supervisor] [automaton] def Name(<params>): ... end; Name: Def(<args>);
        params: controllable|uncontrollable|event x, y; alg <type> z
    inside an automaton:
        disc int[lo..hi] x = v;  disc bool b;  disc Mode m = Off;   (const / alg too)
        alphabet a, b;  initial <pred>;  marked <pred>;
        location L;  location L: ...  location: ... (nameless, the only location)
            initial [<pred>];  marked [<pred>];
            edge e1, e2 [when <guards>] [do x := <expr>, ...] [goto L];
    expressions: true false 3 x A.x A.L (location test) not - + * div mod = != < <= > >=
        and or => <=> if c: v elif c: v else v end abs(x) min(x, y) max(x, y)

Translation choices (spec §7.1):
- variables are named "A.x"; bool is [0, 1]; an enum's literals are 0, 1, ...;
- a `disc` without a value starts at false, the first literal, or 0 (the lower bound if 0 is
  outside the range), as the legacy reader;
- initial locations: those with an `initial` clause whose predicates (and the automaton's
  `initial` predicates) hold for the initial variable values; they may not test locations yet;
- marked predicate of A: (A's `marked` predicates) and (some location L with a `marked`
  clause has A.L and its predicates); a location without `marked` is not marked;
- an edge with several events becomes one edge per event; without `goto` it stays;
- `/` (a real division in CIF), reals, unranged int: refused (not finite or not integer);
- integers are 32-bit as in CIF: a literal or an operator result outside [-2^31, 2^31 - 1] is an
  overflow error (in a constant: CifFormatError; in a guard or update: an error at unfolding);
- `div` / `mod` as CIF (spec Q6): `div` rounds toward zero, `mod` has the sign of the left
  operand (-7 div 4 = -1, -7 mod 4 = -3); by zero: an error.
"""

import re
from dataclasses import dataclass, field
from typing import Dict, List

from core_aut.efsm import (
    FALSE,
    INT_MAX,
    INT_MIN,
    TRUE,
    AtLoc,
    Bin,
    Edge,
    Efsm,
    EfsmSystem,
    Ite,
    Lit,
    Un,
    Var,
    Variable,
    conj,
    disj,
    text,
)

KINDS = ("plant", "requirement", "supervisor")
UNSUPPORTED = {
    "input", "invariant", "urgent", "group", "func", "import", "svgfile", "svgout",
    "svgin", "svgcopy", "svgmove", "print", "printfile", "cont", "der", "equation",
    "tau", "while", "switch", "namespace", "monitor", "type", "initial_value", "real",
    "needs", "disables", "string", "list", "tuple", "dist", "any",
}
_BIN = {"and": "and", "or": "or", "=>": "imp", "<=>": "iff", "=": "eq", "!=": "ne",
        "<": "lt", "<=": "le", ">": "gt", ">=": "ge", "+": "add", "-": "sub", "*": "mul",
        "div": "div", "mod": "mod"}


class CifFormatError(ValueError):
    """The text is not a CIF model this reader understands."""


class UnsupportedCifError(CifFormatError):
    """A CIF construct the reader does not translate (yet)."""


def read_cif(path) -> EfsmSystem:
    with open(path) as f:
        return parse_cif(f.read(), source=str(path))


def parse_cif(text_: str, source: str = "<cif>") -> EfsmSystem:
    spec = _Parser(_tokenize(text_, source), source).spec()
    return _Builder(spec, source).build().check()


# --- tokens -------------------------------------------------------------------------------

_TOKEN = re.compile(
    r"""
    (?P<ws>\s+) | (?P<comment>//[^\n]*|/\*.*?\*/)
    | (?P<num>\d+\.\d+(?:[eE][+-]?\d+)?|\d+)
    | (?P<id>[A-Za-z_][A-Za-z0-9_]*)
    | (?P<sym>:=|\.\.|<=>|=>|<=|>=|!=|[=<>+\-*/()\[\],;:.])
    """,
    re.VERBOSE | re.DOTALL,
)


@dataclass
class _Tok:
    kind: str  # "num", "id", "sym", "eof"
    text: str
    line: int


def _tokenize(src: str, source: str) -> List[_Tok]:
    out, i, line = [], 0, 1
    while i < len(src):
        m = _TOKEN.match(src, i)
        if not m:
            raise CifFormatError(f"{source} line {line}: unexpected {src[i]!r}")
        kind = m.lastgroup
        if kind not in ("ws", "comment"):
            out.append(_Tok(kind, m.group(), line))
        line += m.group().count("\n")
        i = m.end()
    out.append(_Tok("eof", "", line))
    return out


# --- parser: tokens -> declarations with unresolved names ----------------------------------
# Unresolved expressions: ("lit", int), ("name", [parts], line), ("un", op, x),
# ("bin", op, x, y), ("if", [(cond, value), ...], other), ("call", fn, [args]).


@dataclass
class _AutDecl:
    kind: str
    name: str
    body: list
    params: list = field(default_factory=list)
    line: int = 0


class _Parser:
    def __init__(self, toks: List[_Tok], source: str):
        self.toks, self.i, self.source = toks, 0, source

    @property
    def tok(self) -> _Tok:
        return self.toks[self.i]

    def fail(self, msg, tok=None):
        tok = tok or self.tok
        raise CifFormatError(f"{self.source} line {tok.line}: {msg}")

    def unsupported(self, what, tok=None):
        tok = tok or self.tok
        raise UnsupportedCifError(f"{self.source} line {tok.line}: '{what}' is not supported "
                                  "by certisc's CIF reader")

    def at(self, *texts) -> bool:
        return self.tok.kind in ("id", "sym") and self.tok.text in texts

    def take(self, *texts) -> _Tok:
        if not self.at(*texts):
            self.fail(f"expected {' or '.join(repr(t) for t in texts)}, got {self.tok.text!r}")
        tok = self.tok
        self.i += 1
        return tok

    def accept(self, *texts) -> bool:
        if self.at(*texts):
            self.i += 1
            return True
        return False

    def ident(self) -> str:
        if self.tok.kind != "id":
            self.fail(f"expected a name, got {self.tok.text!r}")
        if self.tok.text in UNSUPPORTED:
            self.unsupported(self.tok.text)
        name = self.tok.text
        self.i += 1
        return name

    def idlist(self) -> List[str]:
        names = [self.ident()]
        while self.accept(","):
            names.append(self.ident())
        return names

    def spec(self) -> dict:
        spec = {"events": {}, "consts": [], "algs": [], "enums": {}, "defs": {},
                "automata": []}
        while self.tok.kind != "eof":
            self.declaration(spec)
        return spec

    def declaration(self, spec):
        tok = self.tok
        if self.at("controllable", "uncontrollable", "event"):
            kind = self.take("controllable", "uncontrollable", "event").text
            for name in self.idlist():
                if name in spec["events"]:
                    self.fail(f"event {name} declared twice", tok)
                spec["events"][name] = kind
            self.take(";")
        elif self.at("const", "alg"):
            which = self.take("const", "alg").text
            spec[which + "s"].extend(self.typed_definitions())
        elif self.accept("enum"):
            name = self.ident()
            self.take("=")
            spec["enums"][name] = self.idlist()
            self.take(";")
        elif self.at(*KINDS, "automaton"):
            kind = self.tok.text if self.at(*KINDS) else "plant"
            self.accept(*KINDS)
            self.accept("automaton")
            if self.accept("def"):
                name = self.ident()
                self.take("(")
                params = self.params()
                self.take(")")
                self.take(":")
                spec["defs"][name] = _AutDecl(kind, name, self.body(), params, tok.line)
            else:
                name = self.ident()
                self.take(":")
                spec["automata"].append(_AutDecl(kind, name, self.body(), line=tok.line))
        elif tok.kind == "id" and self.toks[self.i + 1].text == ":":
            name = self.ident()
            self.take(":")
            definition = self.ident()
            self.take("(")
            args = [] if self.at(")") else self.exprs()
            self.take(")")
            self.take(";")
            spec["automata"].append(("instance", name, definition, args, tok.line))
        elif tok.kind == "id":
            self.unsupported(tok.text)
        else:
            self.fail(f"unexpected {tok.text!r}")

    def typed_definitions(self):
        """`<type> a = e, b = e;` -> [(name, type, expr)]"""
        type_ = self.type_()
        out = []
        while True:
            name = self.ident()
            self.take("=")
            out.append((name, type_, self.expr()))
            if not self.accept(","):
                break
        self.take(";")
        return out

    def type_(self):
        if self.accept("bool"):
            return ("bool",)
        if self.accept("int"):
            if self.accept("["):
                lo = self.expr()
                self.take("..")
                hi = self.expr()
                self.take("]")
                return ("int", lo, hi)
            return ("int",)
        return ("enum", self.ident())

    def params(self):
        params = []
        while not self.at(")"):
            if self.at("controllable", "uncontrollable", "event"):
                kind = self.take("controllable", "uncontrollable", "event").text
                params.extend(("event", n, kind) for n in self.idlist())
            elif self.accept("alg"):
                type_ = self.type_()
                params.extend(("alg", n, type_) for n in self.idlist())
            else:
                self.unsupported(self.tok.text)
            if not self.accept(";"):
                break
        return params

    def body(self):
        elements = []
        while not self.accept("end"):
            tok = self.tok
            if self.accept("disc"):
                type_ = self.type_()
                while True:
                    name = self.ident()
                    value = self.expr() if self.accept("=") else None
                    if self.at("in"):
                        self.unsupported("disc ... in")
                    elements.append(("disc", name, type_, value, tok.line))
                    if not self.accept(","):
                        break
                self.take(";")
            elif self.at("const", "alg"):
                which = self.take("const", "alg").text
                for d in self.typed_definitions():
                    elements.append((which,) + d)
            elif self.accept("alphabet"):
                elements.append(("alphabet", self.idlist() if not self.at(";") else [],
                                 tok.line))
                self.take(";")
            elif self.at("initial", "marked"):
                which = self.take("initial", "marked").text
                elements.append((which, self.exprs(), tok.line))
                self.take(";")
            elif self.accept("location"):
                elements.append(("location", self.location(tok)))
            elif tok.kind == "eof":
                self.fail("missing 'end'")
            elif tok.kind == "id":
                self.unsupported(tok.text)
            else:
                self.fail(f"unexpected {tok.text!r}")
        return elements

    def location(self, tok):
        name = None if self.at(":", ";") else self.ident()
        loc = {"name": name, "initial": None, "marked": None, "edges": [], "line": tok.line}
        if self.accept(";"):
            return loc
        self.take(":")
        while True:
            if self.at("initial", "marked"):
                which = self.take("initial", "marked").text
                loc[which] = [] if self.at(";") else self.exprs()
                self.take(";")
            elif self.accept("edge"):
                loc["edges"].append(self.edge())
                self.take(";")
            elif self.at("urgent", "invariant"):
                self.unsupported(self.tok.text)
            else:
                return loc

    def edge(self):
        line = self.tok.line
        events = self.idlist()
        guard, updates, target = [], [], None
        seen = set()
        while self.at("when", "do", "goto"):
            clause = self.take("when", "do", "goto").text
            if clause in seen:
                self.fail(f"'{clause}' given twice on one edge")
            seen.add(clause)
            if clause == "when":
                guard = self.exprs()
            elif clause == "do":
                updates = [self.update()]
                while self.accept(","):
                    updates.append(self.update())
            else:
                target = self.ident()
        return {"events": events, "guard": guard, "updates": updates, "target": target,
                "line": line}

    def update(self):
        if self.at("if"):
            self.unsupported("if inside 'do'")
        if self.at("("):
            self.unsupported("multi-assignment")
        var = self.ident()
        if self.at("."):
            self.fail("an automaton may only update its own variables")
        self.take(":=")
        return (var, self.expr())

    # expressions, by precedence: => <=>, or, and, comparisons, + -, * div mod, unary
    def exprs(self):
        out = [self.expr()]
        while self.accept(","):
            out.append(self.expr())
        return out

    def expr(self):
        left = self.disjunction()
        while self.at("=>", "<=>"):
            op = self.take("=>", "<=>").text
            left = ("bin", op, left, self.disjunction())
        return left

    def disjunction(self):
        left = self.conjunction()
        while self.accept("or"):
            left = ("bin", "or", left, self.conjunction())
        return left

    def conjunction(self):
        left = self.comparison()
        while self.accept("and"):
            left = ("bin", "and", left, self.comparison())
        return left

    def comparison(self):
        left = self.sum_()
        if self.at("=", "!=", "<", "<=", ">", ">="):
            op = self.take("=", "!=", "<", "<=", ">", ">=").text
            left = ("bin", op, left, self.sum_())
        return left

    def sum_(self):
        left = self.product()
        while self.at("+", "-"):
            op = self.take("+", "-").text
            left = ("bin", op, left, self.product())
        return left

    def product(self):
        left = self.unary()
        while self.at("*", "/", "div", "mod"):
            if self.at("/"):
                self.unsupported("/ (real division; use div)")
            op = self.take("*", "div", "mod").text
            left = ("bin", op, left, self.unary())
        return left

    def unary(self):
        if self.at("not", "-", "+"):
            op = self.take("not", "-", "+").text
            return ("un", op, self.unary())
        return self.primary()

    def primary(self):
        tok = self.tok
        if tok.kind == "num":
            if "." in tok.text:
                self.unsupported(f"real number {tok.text}")
            self.i += 1
            return ("lit", int(tok.text))
        if self.accept("true"):
            return ("lit", 1)
        if self.accept("false"):
            return ("lit", 0)
        if self.accept("("):
            e = self.expr()
            self.take(")")
            return e
        if self.accept("if"):
            branches = [(self.expr(), self._colon_expr())]
            while self.accept("elif"):
                branches.append((self.expr(), self._colon_expr()))
            self.take("else")
            other = self.expr()
            self.take("end")
            return ("if", branches, other)
        if self.at("abs", "min", "max"):
            fn = self.take("abs", "min", "max").text
            self.take("(")
            args = self.exprs()
            self.take(")")
            if len(args) != (1 if fn == "abs" else 2):
                self.fail(f"{fn} takes {1 if fn == 'abs' else 2} argument(s)", tok)
            return ("call", fn, args)
        if tok.kind == "id":
            parts = [self.ident()]
            while self.accept("."):
                parts.append(self.ident())
            if self.at("("):
                self.unsupported("function call " + ".".join(parts))
            return ("name", parts, tok.line)
        self.fail(f"unexpected {tok.text!r} in expression")

    def _colon_expr(self):
        self.take(":")
        return self.expr()


# --- builder: resolve names, build the EfsmSystem -----------------------------------------
# Scope entries: ("lit", Lit), ("var", full name), ("loc", automaton, location),
# ("alg", unresolved body, scope, name), ("expr", resolved Expr), ("event", name).


class _Scope:
    def __init__(self, parent=None):
        self.parent, self.names = parent, {}

    def lookup(self, name):
        scope = self
        while scope is not None:
            if name in scope.names:
                return scope.names[name]
            scope = scope.parent
        return None


class _Builder:
    def __init__(self, spec: dict, source: str):
        self.spec, self.source = spec, source
        self.automata: Dict[str, dict] = {}
        self.globals = _Scope()
        self.variables: List[Variable] = []

    def fail(self, msg, line=None):
        where = f" line {line}" if line else ""
        raise CifFormatError(f"{self.source}{where}: {msg}")

    def unsupported(self, msg, line=None):
        where = f" line {line}" if line else ""
        raise UnsupportedCifError(f"{self.source}{where}: {msg}")

    def build(self) -> EfsmSystem:
        spec = self.spec
        literal_of = {}
        for enum, literals in spec["enums"].items():
            for k, lit in enumerate(literals):
                if lit in literal_of and literal_of[lit] != k:
                    self.unsupported(f"enum literal {lit} has different positions in two enums")
                literal_of[lit] = k
                self.globals.names[lit] = ("lit", Lit(k))
        for name, type_, expr in spec["consts"]:
            self.globals.names[name] = ("lit", Lit(self.constant(expr, self.globals)))
        for name, _, expr in spec["algs"]:
            self.globals.names[name] = ("alg", expr, self.globals, name)

        decls = []
        for item in spec["automata"]:
            if isinstance(item, tuple):
                _, name, definition, args, line = item
                if definition not in spec["defs"]:
                    self.fail(f"{name}: no automaton definition {definition}", line)
                decl = spec["defs"][definition]
                decls.append((name, decl, self.bind(name, decl, args, line)))
            else:
                decls.append((item.name, item, {}))
        for name, decl, bindings in decls:
            if name in self.automata:
                self.fail(f"automaton {name} declared twice", decl.line)
            self.automata[name] = self.declare(name, decl, bindings)
        for name, decl, _ in decls:
            self.variables += self.discs(name, decl)
        automata = [self.fill(name, decl) for name, decl, _ in decls]

        events = list(spec["events"])
        euc = {n for n, kind in spec["events"].items() if kind == "uncontrollable"}
        return EfsmSystem(events, self.variables, automata, Euc=euc)

    def bind(self, name, decl, args, line):
        if len(args) != len(decl.params):
            self.fail(f"{name}: {decl.name} takes {len(decl.params)} arguments, "
                      f"got {len(args)}", line)
        bindings = {}
        for (what, pname, extra), arg in zip(decl.params, args):
            if what == "event":
                if arg[0] != "name" or len(arg[1]) != 1:
                    self.fail(f"{name}: argument for {pname} must be an event", line)
                event = arg[1][0]
                declared = self.spec["events"].get(event)
                if declared is None:
                    self.fail(f"{name}: {event} is not a declared event", line)
                if extra != "event" and declared != extra:
                    self.fail(f"{name}: parameter {pname} must be {extra}, but {event} is "
                              f"{declared}", line)
                bindings[pname] = ("event", event)
            else:
                bindings[pname] = ("expr", self.resolve(arg, self.globals))
        return bindings

    def declare(self, name, decl, bindings):
        """The automaton's scope: parameters, locations, discs, local const / alg."""
        scope = _Scope(self.globals)
        scope.names.update(bindings)
        locations = []
        for element in decl.body:
            if element[0] == "location":
                loc = element[1]
                lname = "" if loc["name"] is None else loc["name"]
                if loc["name"] is not None:
                    scope.names[lname] = ("loc", name, lname)
                locations.append(lname)
            elif element[0] == "disc":
                scope.names[element[1]] = ("var", f"{name}.{element[1]}")
            elif element[0] == "const":
                scope.names[element[1]] = ("lit", Lit(self.constant(element[3], scope)))
            elif element[0] == "alg":
                scope.names[element[1]] = ("alg", element[3], scope, element[1])
        if not locations:
            self.fail(f"{name} has no locations", decl.line)
        if "" in locations and len(locations) > 1:
            self.fail(f"{name}: a nameless location must be the only one", decl.line)
        return {"scope": scope, "locations": locations}

    def discs(self, name, decl):
        scope = self.automata[name]["scope"]
        out = []
        for element in decl.body:
            if element[0] != "disc":
                continue
            _, var, type_, value, line = element
            full = f"{name}.{var}"
            if type_[0] == "bool":
                lo, hi, kind, literals = 0, 1, "bool", ()
                init = 0 if value is None else self.constant(value, scope)
            elif type_[0] == "int":
                if len(type_) == 1:
                    self.unsupported(f"disc int {var} needs a range, int[lo..hi]", line)
                lo, hi = self.constant(type_[1], scope), self.constant(type_[2], scope)
                kind, literals = "int", ()
                init = (0 if lo <= 0 <= hi else lo) if value is None \
                    else self.constant(value, scope)
            else:
                literals = self.spec["enums"].get(type_[1])
                if literals is None:
                    self.fail(f"unknown type {type_[1]}", line)
                lo, hi, kind, literals = 0, len(literals) - 1, "enum", tuple(literals)
                init = 0 if value is None else self.constant(value, scope)
            if not lo <= init <= hi:
                self.fail(f"initial value of {full} is outside its type", line)
            out.append(Variable(full, lo, hi, init, kind, literals))
        return out

    def fill(self, name, decl) -> Efsm:
        entry = self.automata[name]
        scope, locations = entry["scope"], entry["locations"]
        alphabet, declared_alphabet = set(), None
        aut_initial, aut_marked = [], []
        initial, marked_terms, edges = set(), [], []
        locs = iter(locations)
        for element in decl.body:
            tag = element[0]
            if tag == "alphabet":
                declared_alphabet = {self.event(e, scope, element[2]) for e in element[1]}
            elif tag == "initial":
                aut_initial += [self.resolve(x, scope) for x in element[1]]
            elif tag == "marked":
                aut_marked += [self.resolve(x, scope) for x in element[1]]
        for element in decl.body:
            if element[0] != "location":
                continue
            loc, lname = element[1], next(locs)
            if loc["marked"] is not None:
                preds = [self.resolve(x, scope) for x in loc["marked"]]
                here = [] if len(locations) == 1 else [AtLoc(name, lname)]
                marked_terms.append(conj(here + preds))
            if loc["initial"] is not None:
                preds = [self.resolve(x, scope) for x in loc["initial"]] + aut_initial
                if all(self.initially(p, loc["line"]) for p in preds):
                    initial.add(lname)
            for e in loc["edges"]:
                target = lname if e["target"] is None else e["target"]
                if target not in locations:
                    self.fail(f"{name}: no location {target}", e["line"])
                guard = tuple(self.resolve(x, scope) for x in e["guard"])
                updates = {}
                for var, x in e["updates"]:
                    entry_ = scope.names.get(var)
                    if entry_ is None or entry_[0] != "var":
                        self.fail(f"{name}: {var} is not a variable of {name}", e["line"])
                    if entry_[1] in updates:
                        self.fail(f"{name}: {var} updated twice on one edge", e["line"])
                    updates[entry_[1]] = self.resolve(x, scope)
                for ev in e["events"]:
                    event = self.event(ev, scope, e["line"])
                    if declared_alphabet is not None and event not in declared_alphabet:
                        self.fail(f"{name}: edge event {event} is not in its alphabet",
                                  e["line"])
                    alphabet.add(event)
                    edges.append(Edge(lname, event, guard, dict(updates), target))
        if not initial:
            self.fail(f"{name} has no initial location", decl.line)
        if declared_alphabet is not None:
            alphabet = declared_alphabet
        marked = conj(aut_marked + [disj(marked_terms)]) if marked_terms else FALSE
        return Efsm(name, locations, initial, alphabet, edges, marked, decl.kind)

    def event(self, name, scope, line):
        bound = scope.lookup(name)
        if bound is not None and bound[0] == "event":
            return bound[1]
        if name not in self.spec["events"]:
            self.fail(f"{name} is not a declared event", line)
        return name

    def initially(self, pred, line) -> bool:
        """Whether an initial predicate holds for the initial variable values (spec Q5: one
        initial value per variable). Location tests are not supported here yet."""
        values = {v.name: v.init for v in self.variables}
        try:
            return _static(pred, values) != 0
        except _EvalError as err:
            self.fail(f"initial predicate {text(pred)}: {err}", line)
        except _NotStatic as err:
            self.unsupported(f"initial predicate {text(pred)} ({err})", line)

    def constant(self, expr, scope) -> int:
        resolved = self.resolve(expr, scope)
        try:
            return _static(resolved, {})
        except _EvalError as err:
            self.fail(f"{text(resolved)}: {err}")
        except _NotStatic as err:
            self.fail(f"{text(resolved)} is not a constant ({err})")

    def resolve(self, expr, scope, active=()):
        tag = expr[0]
        if tag == "lit":
            return Lit(expr[1])
        if tag == "name":
            return self.resolve_name(expr[1], expr[2], scope, active)
        if tag == "un":
            arg = self.resolve(expr[2], scope, active)
            return arg if expr[1] == "+" else Un("not" if expr[1] == "not" else "neg", arg)
        if tag == "bin":
            return Bin(_BIN[expr[1]], self.resolve(expr[2], scope, active),
                       self.resolve(expr[3], scope, active))
        if tag == "if":
            out = self.resolve(expr[2], scope, active)
            for cond, value in reversed(expr[1]):
                out = Ite(self.resolve(cond, scope, active), self.resolve(value, scope, active),
                          out)
            return out
        if tag == "call":
            args = [self.resolve(x, scope, active) for x in expr[2]]
            return Un("abs", args[0]) if expr[1] == "abs" else Bin(expr[1], args[0], args[1])
        raise AssertionError(expr)

    def resolve_name(self, parts, line, scope, active):
        if len(parts) == 2:
            aut = self.automata.get(parts[0])
            if aut is None:
                self.fail(f"unknown automaton {parts[0]}", line)
            target = aut["scope"].names.get(parts[1])
        elif len(parts) == 1:
            target = scope.lookup(parts[0])
        else:
            self.unsupported(f"'{'.'.join(parts)}' (groups are not supported yet)", line)
        if target is None:
            self.fail(f"unknown name {'.'.join(parts)}", line)
        kind = target[0]
        if kind == "lit":
            return target[1]
        if kind == "var":
            return Var(target[1])
        if kind == "loc":
            return AtLoc(target[1], target[2])
        if kind == "expr":
            return target[1]
        if kind == "alg":
            _, body, alg_scope, alg_name = target
            key = (id(alg_scope), alg_name)
            if key in active:
                self.fail(f"alg {alg_name} is defined in terms of itself", line)
            return self.resolve(body, alg_scope, active + (key,))
        self.fail(f"{'.'.join(parts)} cannot be used in an expression", line)


class _NotStatic(Exception):
    """The expression reads the state (a variable or a location), so it has no fixed value."""


class _EvalError(Exception):
    """An evaluation error, as in CIF: division by zero, or a 32-bit integer overflow."""


def _fit32(v: int, what) -> int:
    """v if it is a 32-bit integer, else CIF's overflow error (Lean fit32)."""
    if not INT_MIN <= v <= INT_MAX:
        raise _EvalError(f"integer overflow: {what() if callable(what) else what} = {v} is "
                         f"outside CIF's 32-bit integers [{INT_MIN}, {INT_MAX}]")
    return v


def _static(e, values) -> int:
    """Value of e from the given variable values, with the operators of the EFSM meaning
    (certisc-proof/DESopsProof/Efsm.lean, BinOp.apply). Used only for constants and initial
    predicates; the unfolder evaluates everything else. As Lean `Expr.eval`, every literal and
    operator result must be a 32-bit integer (`_fit32`)."""
    if isinstance(e, Lit):
        return _fit32(e.value, "literal")
    if isinstance(e, Var):
        if e.name not in values:
            raise _NotStatic(f"reads variable {e.name}")
        return values[e.name]
    if isinstance(e, AtLoc):
        raise _NotStatic(f"tests location {text(e)}")
    if isinstance(e, Ite):
        return _static(e.then_ if _static(e.cond, values) != 0 else e.other, values)
    if isinstance(e, Un):
        v = _static(e.arg, values)
        return _fit32({"not": int(v == 0), "neg": -v, "abs": abs(v)}[e.op], lambda: text(e))
    a, b = _static(e.left, values), _static(e.right, values)
    return _fit32(_binary(e.op, a, b), lambda: f"{a} {e.op} {b}")


def _binary(op, a, b) -> int:
    """The exact (unbounded) result of a binary operator, as Lean `BinOp.apply`."""
    if op in ("div", "mod"):
        # As CIF (ESCET CifMath: Java / and %; Lean Int.tdiv / Int.tmod), not Python's // and %,
        # which round down: -7 div 4 = -1 and -7 mod 4 = -3 (Python: -2 and 1).
        if b == 0:
            raise _EvalError(f"division by zero: {a} {op} 0")
        q = abs(a) // abs(b) * (1 if (a < 0) == (b < 0) else -1)
        return q if op == "div" else a - b * q
    return {
        "and": lambda: int(a != 0 and b != 0), "or": lambda: int(a != 0 or b != 0),
        "imp": lambda: int(a == 0 or b != 0), "iff": lambda: int((a != 0) == (b != 0)),
        "eq": lambda: int(a == b), "ne": lambda: int(a != b), "lt": lambda: int(a < b),
        "le": lambda: int(a <= b), "gt": lambda: int(a > b), "ge": lambda: int(a >= b),
        "add": lambda: a + b, "sub": lambda: a - b, "mul": lambda: a * b,
        "min": lambda: min(a, b), "max": lambda: max(a, b),
    }[op]()
