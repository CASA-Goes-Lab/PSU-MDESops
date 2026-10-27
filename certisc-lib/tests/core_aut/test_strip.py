"""
The contract stripper (core_aut/trusted/_strip.py): what counts as a lemma, and which calls are
removed.
"""

import ast

from core_aut.trusted._strip import strip_source

SOURCE = '''
def lem(a, i):
    Requires(i >= 0)
    Ensures(True)
    if i > 0:
        lem(a, i - 1)


def lem2(a, x):
    lo = a[x]
    Assert(lo >= 0)


def work(a, out):
    out.append(1)


def run(a, out, n):
    lem(ToSeq(a), n)
    lem2(a, a[0] + 1)
    lem(a, len(a))
    work(a, out)
    lem(a, f(n))
'''


def _calls(tree):
    return [c.func.id for c in ast.walk(tree)
            if isinstance(c, ast.Call) and isinstance(c.func, ast.Name)]


def test_recursive_lemma_and_simple_arguments_are_removed():
    tree = strip_source(SOURCE)
    run = next(f for f in tree.body if isinstance(f, ast.FunctionDef) and f.name == "run")
    calls = _calls(run)
    # lemma calls with simple arguments (names, list reads, arithmetic, len, ToSeq) are gone
    assert calls.count("lem") == 1 and "lem2" not in calls
    # a real call stays, and so does a lemma call whose argument calls another function
    assert "work" in calls and "f" in calls
    # contracts are gone everywhere
    assert not {"Requires", "Ensures", "Assert"} & set(_calls(tree))
