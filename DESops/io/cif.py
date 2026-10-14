"""
Read a subset of CIF 3 (Eclipse ESCET) into a DESops.core.efsm.EfsmSystem.

    system = read_cif("model.cif")
    parts = system.unfold()           # {name: Automaton}, linked automata merged
    plant = system.unfold(flat=True)  # one Automaton for the whole model

Supported:
    controllable a, b;  uncontrollable c;  event e;
    const int N = 2;  const real Q = 0.1;  const bool B = true;
    alg bool deficit = <expr>;           (top level or inside an automaton)
    enum Mode = Off, On;
    [plant|requirement|supervisor] [automaton] Name: ... end
    [plant|requirement|supervisor] [automaton] def Name(<params>): ... end
        params: controllable|uncontrollable|event x, y; alg <type> z
    Name: Def(<args>);                   (instantiation)
    inside an automaton:
        disc int[lo..hi] x = v;  disc bool b;  disc Mode m = Off;
        alphabet a, b;                   (events the automaton must take part in)
        initial <pred>;  marked <pred>;  (automaton-level predicates)
        location L;  location L: ...  location: ...   (nameless)
            initial [<pred>];  marked [<pred>];
            edge e1, e2 [when <guards>] [do x := <expr>, ...] [goto L];
    expressions: true false 1 0.5 x A.x A.L (location as bool) not - + - * /
        div mod = != < <= > >= and or => <=> if c: v elif c: v else v end
        abs(x) min(x, y) max(x, y)

Anything else (input variables, invariants, urgency, groups, functions,
if-updates, SVG, imports, ...) raises error.UnsupportedFeatureError rather
than being skipped.

Defaults and choices:
- A `disc` without initial value starts at false (bool), the first literal
  (enum), or 0 for int (the lower bound if 0 is outside the range).
- `disc int` needs a range; `disc real` is not supported (unfolding needs
  finite domains).
- Plain `event` declarations are treated as controllable. CIF has no
  observability, so every event is observable (Euo is empty).
"""

import re
from dataclasses import dataclass, field
from typing import Dict, List

from DESops import error
from DESops.core.efsm import (
    Edge,
    Efsm,
    EfsmSystem,
    Location,
    Variable,
    evaluate_constant,
)

KINDS = ("plant", "requirement", "supervisor")
UNSUPPORTED = {
    "input", "invariant", "urgent", "group", "func", "import", "svgfile", "svgout",
    "svgin", "svgcopy", "svgmove", "print", "printfile", "cont", "der", "equation",
    "tau", "while", "switch", "namespace", "monitor", "type", "initial_value",
}


def read_cif(path: str) -> EfsmSystem:
    with open(path, "r") as f:
        return parse_cif(f.read(), source=path)


def parse_cif(text: str, source: str = "<cif>") -> EfsmSystem:
    return _Builder(_Parser(_tokenize(text, source), source).spec(), source).build()


# --- tokens -------------------------------------------------------------------

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


def _tokenize(text: str, source: str) -> List[_Tok]:
    out, i, line = [], 0, 1
    while i < len(text):
        m = _TOKEN.match(text, i)
        if not m:
            raise error.FileFormatError(f"{source} line {line}: unexpected {text[i]!r}")
        kind = m.lastgroup
        if kind not in ("ws", "comment"):
            out.append(_Tok(kind, m.group(), line))
        line += m.group().count("\n")
        i = m.end()
    out.append(_Tok("eof", "", line))
    return out


# --- parser: tokens -> declarations with unresolved names ------------------------
# Unresolved expressions use ("name", [parts], line) for identifiers.


@dataclass
class _AutDecl:
    kind: str
    name: str
    body: list  # elements
    params: list = field(default_factory=list)  # for definitions
    line: int = 0


class _Parser:
    def __init__(self, toks: List[_Tok], source: str):
        self.toks, self.i, self.source = toks, 0, source

    # helpers
    @property
    def tok(self) -> _Tok:
        return self.toks[self.i]

    def fail(self, msg, tok=None):
        tok = tok or self.tok
        raise error.FileFormatError(f"{self.source} line {tok.line}: {msg}")

    def unsupported(self, what, tok=None):
        tok = tok or self.tok
        raise error.UnsupportedFeatureError(
            f"{self.source} line {tok.line}: '{what}' is not supported by DESops' CIF reader"
        )

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
        text = self.tok.text
        self.i += 1
        return text

    def idlist(self) -> List[str]:
        names = [self.ident()]
        while self.accept(","):
            names.append(self.ident())
        return names

    # top level
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
        if self.accept("real"):
            return ("real",)
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
                elements.append(("alphabet", self.idlist() if not self.at(";") else []))
                self.take(";")
            elif self.at("initial", "marked"):
                which = self.take("initial", "marked").text
                elements.append((which, self.exprs()))
                self.take(";")
            elif self.accept("location"):
                elements.append(("location",) + self.location(tok))
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
            return (loc,)
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
                return (loc,)

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
            self.unsupported("if-update")
        var = self.ident()
        if self.at("."):
            self.unsupported("updating another automaton's variable")
        self.take(":=")
        return (var, self.expr())

    # expressions
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
            op = self.take("*", "/", "div", "mod").text
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
            self.i += 1
            return ("lit", float(tok.text) if "." in tok.text else int(tok.text))
        if self.accept("true"):
            return ("lit", True)
        if self.accept("false"):
            return ("lit", False)
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


# --- builder: resolve names, build the EfsmSystem ---------------------------------


class _Scope:
    """Names visible at some point: name -> resolved expression or marker."""

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
        self.automata: Dict[str, dict] = {}  # name -> {"scope": _Scope, "efsm": Efsm}
        self.globals = _Scope()

    def fail(self, msg, line=None):
        where = f" line {line}" if line else ""
        raise error.FileFormatError(f"{self.source}{where}: {msg}")

    def build(self) -> EfsmSystem:
        spec = self.spec
        for enum, literals in spec["enums"].items():
            for lit in literals:
                self.globals.names[lit] = ("lit", lit)
        for name, _, expr in spec["consts"]:
            self.globals.names[name] = ("lit", self.constant(expr, self.globals))
        for name, _, expr in spec["algs"]:
            self.globals.names[name] = ("alg", expr, self.globals, name)

        # declare every automaton first, so expressions can refer to any of them
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
            self.fill(name, decl)

        events = {n: kind != "uncontrollable" for n, kind in spec["events"].items()}
        return EfsmSystem(events, [a["efsm"] for a in self.automata.values()])

    def bind(self, name, decl, args, line):
        if len(args) != len(decl.params):
            self.fail(
                f"{name}: {decl.name} takes {len(decl.params)} arguments, got {len(args)}",
                line,
            )
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
                    self.fail(
                        f"{name}: parameter {pname} must be {extra}, but {event} is {declared}",
                        line,
                    )
                bindings[pname] = ("event", event)
            else:
                bindings[pname] = ("expr", self.resolve(arg, self.globals))
        return bindings

    def declare(self, name, decl, bindings):
        scope = _Scope(self.globals)
        scope.names.update(bindings)
        efsm = Efsm(name, decl.kind)
        for element in decl.body:
            if element[0] == "location":
                loc = element[1]
                if loc["name"] is not None:
                    scope.names[loc["name"]] = ("loc", name, loc["name"])
                efsm.locations.append(Location(loc["name"]))
            elif element[0] == "disc":
                scope.names[element[1]] = ("var", name, element[1])
            elif element[0] == "const":
                scope.names[element[1]] = ("lit", self.constant(element[3], scope))
            elif element[0] == "alg":
                scope.names[element[1]] = ("alg", element[3], scope, element[1])
        if not efsm.locations:
            self.fail(f"{name} has no locations", decl.line)
        if any(loc.name is None for loc in efsm.locations) and len(efsm.locations) > 1:
            self.fail(f"{name}: a nameless location must be the only one", decl.line)
        return {"scope": scope, "efsm": efsm, "decl": decl}

    def fill(self, name, decl):
        entry = self.automata[name]
        scope, efsm = entry["scope"], entry["efsm"]
        locs = iter(efsm.locations)
        for element in decl.body:
            tag = element[0]
            if tag == "disc":
                efsm.variables.append(self.variable(element, scope))
            elif tag == "alphabet":
                efsm.alphabet |= {self.event(e, scope, decl.line) for e in element[1]}
            elif tag in ("initial", "marked"):
                getattr(efsm, tag).extend(self.resolve(x, scope) for x in element[1])
            elif tag == "location":
                loc, target = element[1], next(locs)
                for which in ("initial", "marked"):
                    if loc[which] is not None:
                        setattr(target, which, [self.resolve(x, scope) for x in loc[which]])
                names = {other.name for other in efsm.locations}
                for e in loc["edges"]:
                    if e["target"] is not None and e["target"] not in names:
                        self.fail(f"{name}: no location {e['target']}", e["line"])
                    events = tuple(self.event(x, scope, e["line"]) for x in e["events"])
                    efsm.alphabet |= set(events)
                    target.edges.append(Edge(
                        events,
                        [self.resolve(x, scope) for x in e["guard"]],
                        [(var, self.resolve(x, scope)) for var, x in e["updates"]],
                        e["target"],
                    ))
                    for var, _ in e["updates"]:
                        if scope.names.get(var, (None,))[0] != "var":
                            self.fail(f"{name}: {var} is not a variable of {name}", e["line"])

    def event(self, text, scope, line):
        bound = scope.lookup(text)
        if bound is not None and bound[0] == "event":
            return bound[1]
        if text not in self.spec["events"]:
            self.fail(f"{text} is not a declared event", line)
        return text

    def variable(self, element, scope):
        _, name, type_, value, line = element
        if type_[0] == "bool":
            init = False if value is None else self.constant(value, scope)
            return Variable(name, "bool", (), init)
        if type_[0] == "int":
            if len(type_) == 1:
                raise error.UnsupportedFeatureError(
                    f"{self.source} line {line}: disc int {name} needs a range, int[lo..hi]"
                )
            lo, hi = self.constant(type_[1], scope), self.constant(type_[2], scope)
            init = (0 if lo <= 0 <= hi else lo) if value is None else self.constant(value, scope)
            var = Variable(name, "int", (lo, hi), init)
        elif type_[0] == "enum":
            literals = self.spec["enums"].get(type_[1])
            if literals is None:
                self.fail(f"unknown type {type_[1]}", line)
            init = literals[0] if value is None else self.constant(value, scope)
            var = Variable(name, "enum", tuple(literals), init)
        else:
            raise error.UnsupportedFeatureError(
                f"{self.source} line {line}: disc {type_[0]} is not supported"
            )
        if not var.contains(var.init):
            self.fail(f"initial value {var.init!r} of {name} is outside its type", line)
        return var

    def constant(self, expr, scope):
        return evaluate_constant(self.resolve(expr, scope))

    def resolve(self, expr, scope, active=()):
        tag = expr[0]
        if tag == "name":
            return self.resolve_name(expr[1], expr[2], scope, active)
        if tag == "lit":
            return expr
        if tag == "un":
            return ("un", expr[1], self.resolve(expr[2], scope, active))
        if tag == "bin":
            return ("bin", expr[1], self.resolve(expr[2], scope, active),
                    self.resolve(expr[3], scope, active))
        if tag == "if":
            return ("if",
                    [(self.resolve(c, scope, active), self.resolve(v, scope, active))
                     for c, v in expr[1]],
                    self.resolve(expr[2], scope, active))
        if tag == "call":
            return ("call", expr[1], [self.resolve(x, scope, active) for x in expr[2]])
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
            raise error.UnsupportedFeatureError(
                f"{self.source} line {line}: '{'.'.join(parts)}' (groups are not supported)"
            )
        if target is None:
            self.fail(f"unknown name {'.'.join(parts)}", line)
        kind = target[0]
        if kind in ("lit", "var", "loc"):
            return target
        if kind == "expr":
            return target[1]
        if kind == "alg":
            _, body, alg_scope, alg_name = target
            key = (id(alg_scope), alg_name)
            if key in active:
                self.fail(f"alg {alg_name} is defined in terms of itself", line)
            return self.resolve(body, alg_scope, active + (key,))
        self.fail(f"{'.'.join(parts)} cannot be used in an expression", line)
