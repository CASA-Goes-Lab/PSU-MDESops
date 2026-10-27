"""
Trusted: turns a Nagini-verified module into the code that runs (certisc-proof/spec/wrapper.md).

Verification is done on the source as written. Before running, two kinds of statements are
removed, because they have no runtime meaning and some would fail at runtime (e.g. Old(...) is
None outside Nagini):
1. contract statements: Requires, Ensures, Invariant, Assert, Assume, Fold, Unfold, Decreases;
2. calls to lemmas. A lemma is a function whose body, once the contracts are removed, does
   nothing: it is empty, or holds only calls to lemmas (itself included: a recursive lemma, i.e.
   a proof by induction), assignments of simple values to locals, and `if` statements with
   simple conditions around such statements. Only calls that stand alone as statements are
   dropped, with simple arguments: names, constants, arithmetic, list reads (indices proved in
   range), len(...), and the contract functions ToSeq(...) / Old(...) (no-ops at runtime). So nothing
   with a side effect is dropped.
3. ToSeq(...) and Old(...) left in the code (as arguments of a real call, e.g. values passed
   only for the proof) become None, which is what they return at runtime, when their argument
   is simple. Same result, without the call.

Nothing else changes, so the stripped module computes exactly what the verified one does.
"""

import ast
import types
from pathlib import Path

CONTRACTS = {"Requires", "Ensures", "Invariant", "Assert", "Assume", "Fold", "Unfold", "Decreases"}
_SIMPLE = (ast.Name, ast.Constant, ast.BinOp, ast.UnaryOp, ast.BoolOp, ast.Compare,
           ast.Subscript, ast.operator, ast.unaryop, ast.boolop, ast.cmpop, ast.expr_context)
_VALUE_CONTRACTS = {"ToSeq", "Old", "len"}   # side-effect-free calls allowed in lemma arguments


def _simple(node) -> bool:
    """No side effect: names, constants, arithmetic, comparisons, list reads l[i] (in verified
    code Nagini proves every index in range), len(...), and ToSeq/Old calls."""
    for x in ast.walk(node):
        if isinstance(x, ast.Call):
            if not (isinstance(x.func, ast.Name) and x.func.id in _VALUE_CONTRACTS):
                return False
        elif not isinstance(x, _SIMPLE):
            return False
    return True


def _is_lemma_call(stmt, names) -> bool:
    call = stmt.value if isinstance(stmt, ast.Expr) else None
    return (isinstance(call, ast.Call) and isinstance(call.func, ast.Name)
            and call.func.id in names and not call.keywords
            and all(_simple(a) for a in call.args))


class _DropStatements(ast.NodeTransformer):
    """Remove statement-level calls to the given names; keep every block non-empty."""

    def __init__(self, names, simple_args_only):
        self.names = names
        self.simple_args_only = simple_args_only

    def visit_Expr(self, node):
        call = node.value
        if isinstance(call, ast.Call) and isinstance(call.func, ast.Name) \
                and call.func.id in self.names:
            if not self.simple_args_only or _is_lemma_call(node, self.names):
                return None
        return node

    def generic_visit(self, node):
        super().generic_visit(node)
        body = getattr(node, "body", None)
        if isinstance(body, list) and not body:
            body.append(ast.Pass())
        return node


def _does_nothing(stmts, names) -> bool:
    """Every statement is a docstring, pass, a lemma call, an assignment of a simple value to a
    local name (dead: a lemma returns nothing), or an if (simple condition) whose branches do
    nothing."""
    for s in stmts:
        if isinstance(s, ast.Pass) or (isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant)):
            continue
        if _is_lemma_call(s, names):
            continue
        if isinstance(s, ast.Assign) and len(s.targets) == 1 and isinstance(s.targets[0], ast.Name) \
                and _simple(s.value):
            continue
        if isinstance(s, ast.If) and _simple(s.test) and _does_nothing(s.body, names) \
                and _does_nothing(s.orelse, names):
            continue
        return False
    return True


def _lemmas(tree):
    """Top-level functions that do nothing (after stripping the contracts). Computed as a
    greatest fixed point, so a lemma may call itself or other lemmas."""
    funcs = {f.name: f for f in tree.body if isinstance(f, ast.FunctionDef)}
    names = set(funcs)
    while True:
        keep = {n for n in names if _does_nothing(funcs[n].body, names)}
        if keep == names:
            return names
        names = keep


class _NoneForValueContracts(ast.NodeTransformer):
    """ToSeq(x) / Old(x) with a simple argument -> None (their runtime value)."""

    def visit_Call(self, node):
        self.generic_visit(node)
        if isinstance(node.func, ast.Name) and node.func.id in ("ToSeq", "Old") \
                and not node.keywords and all(_simple(a) for a in node.args):
            return ast.copy_location(ast.Constant(None), node)
        return node


def strip_source(source: str) -> ast.Module:
    tree = _DropStatements(CONTRACTS, simple_args_only=False).visit(ast.parse(source))
    tree = _DropStatements(_lemmas(tree), simple_args_only=True).visit(tree)
    tree = _NoneForValueContracts().visit(tree)
    return ast.fix_missing_locations(tree)


def load_stripped(path: Path, name: str) -> types.ModuleType:
    """The module at `path`, stripped, as a new module object called `name`."""
    import core_aut.verified_core  # noqa: F401  (contract stand-ins for the remaining imports)
    module = types.ModuleType(name)
    module.__file__ = str(path)
    exec(compile(strip_source(Path(path).read_text()), str(path), "exec"), module.__dict__)
    return module
