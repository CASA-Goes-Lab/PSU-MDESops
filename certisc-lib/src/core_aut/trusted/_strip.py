"""
Trusted: turns a Nagini-verified module into the code that runs (certisc-proof/spec/wrapper.md).

Verification is done on the source as written. Before running, two kinds of statements are
removed, because they have no runtime meaning and some would fail at runtime (e.g. Old(...) is
None outside Nagini):
1. contract statements: Requires, Ensures, Invariant, Assert, Assume, Fold, Unfold, Decreases;
2. calls to lemmas: functions whose body is empty once the contracts are removed. Only calls
   that stand alone as statements, with arguments that are names, constants or arithmetic, so
   nothing with a side effect is dropped.

Nothing else changes, so the stripped module computes exactly what the verified one does.
"""

import ast
import types
from pathlib import Path

CONTRACTS = {"Requires", "Ensures", "Invariant", "Assert", "Assume", "Fold", "Unfold", "Decreases"}
_SIMPLE = (ast.Name, ast.Constant, ast.BinOp, ast.UnaryOp)


class _DropStatements(ast.NodeTransformer):
    """Remove statement-level calls to the given names; keep every block non-empty."""

    def __init__(self, names, simple_args_only):
        self.names = names
        self.simple_args_only = simple_args_only

    def visit_Expr(self, node):
        call = node.value
        if isinstance(call, ast.Call) and isinstance(call.func, ast.Name) \
                and call.func.id in self.names:
            if not self.simple_args_only or all(
                    isinstance(a, _SIMPLE) and not any(isinstance(x, ast.Call) for x in ast.walk(a))
                    for a in call.args):
                return None
        return node

    def generic_visit(self, node):
        super().generic_visit(node)
        body = getattr(node, "body", None)
        if isinstance(body, list) and not body:
            body.append(ast.Pass())
        return node


def _lemmas(tree):
    """Top-level functions whose body is only a docstring and/or pass (after stripping)."""
    names = set()
    for f in tree.body:
        if isinstance(f, ast.FunctionDef):
            body = [s for s in f.body
                    if not (isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant))]
            if all(isinstance(s, ast.Pass) for s in body):
                names.add(f.name)
    return names


def strip_source(source: str) -> ast.Module:
    tree = _DropStatements(CONTRACTS, simple_args_only=False).visit(ast.parse(source))
    tree = _DropStatements(_lemmas(tree), simple_args_only=True).visit(tree)
    return ast.fix_missing_locations(tree)


def load_stripped(path: Path, name: str) -> types.ModuleType:
    """The module at `path`, stripped, as a new module object called `name`."""
    import core_aut.verified_core  # noqa: F401  (contract stand-ins for the remaining imports)
    module = types.ModuleType(name)
    module.__file__ = str(path)
    exec(compile(strip_source(Path(path).read_text()), str(path), "exec"), module.__dict__)
    return module
