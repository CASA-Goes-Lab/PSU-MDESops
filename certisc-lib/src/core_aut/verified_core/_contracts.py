"""
Lets the verified modules run without Nagini installed.

The verified modules import their contract functions exactly as Nagini expects:

    from nagini_contracts.contracts import *

When Nagini is installed (the `verify` extra), that is the real module, whose functions are
no-ops at runtime except `Ensures`, which this file replaces with a no-op (see below). When it is
not installed, this file registers a stand-in module under the same name, with the same names, all
no-ops. Either way the verified code runs unchanged; only `nagini` (the verifier) needs the real
package.
"""

import sys
import types


def _noop(*args, **kwargs):
    return None


try:
    import nagini_contracts.contracts as _real
except ImportError:
    _real = None

if _real is not None:
    # The real `Ensures` is declared only with @typing.overload and has no implementation, so
    # calling it at runtime raises NotImplementedError (Python 3.13, Nagini 1.3.1). Nagini reads
    # the source and never calls it; replace it with a no-op so the verified code can run.
    _real.Ensures = _noop
else:
    _NAMES = [
        "Requires", "Ensures", "Invariant", "Assert", "Assume", "Old", "Result", "Implies",
        "Forall", "Forall2", "Forall3", "Exists", "Acc", "Rd", "list_pred", "set_pred", "ToSeq",
        "dict_pred", "Decreases", "Unfolding", "Fold", "Unfold",
    ]
    _contracts = types.ModuleType("nagini_contracts.contracts")
    for _name in _NAMES:
        setattr(_contracts, _name, _noop)
    _contracts.Pure = lambda func: func
    _contracts.Predicate = lambda func: func

    # Nagini's value types (PSeq, PSet, PMultiset). They appear in type annotations, which
    # Python evaluates when a function is defined (e.g. `o: PSeq[int]`), and as calls inside
    # contracts (e.g. `PSeq(x)`), so each needs to be subscriptable and callable.
    class _ValueType:
        def __class_getitem__(cls, item):
            return cls

        def __init__(self, *args):
            pass

    _TYPES = ["PSeq", "PSet", "PMultiset"]
    for _name in _TYPES:
        setattr(_contracts, _name, type(_name, (_ValueType,), {}))
    _contracts.__all__ = _NAMES + ["Pure", "Predicate"] + _TYPES

    # Termination obligations (check.py: Requires/Invariant(MustTerminate(...))).
    _obligations = types.ModuleType("nagini_contracts.obligations")
    setattr(_obligations, "MustTerminate", _noop)
    setattr(_obligations, "__all__", ["MustTerminate"])

    _package = types.ModuleType("nagini_contracts")
    _package.contracts = _contracts
    setattr(_package, "obligations", _obligations)
    sys.modules["nagini_contracts"] = _package
    sys.modules["nagini_contracts.contracts"] = _contracts
    sys.modules["nagini_contracts.obligations"] = _obligations
