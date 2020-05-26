class InvalidGraphTypeError(Exception):
    pass


class DependencyNotInstalledError(Exception):
    pass


class MissingAttributeError(Exception):
    pass


class NoPathError(Exception):
    pass


class IncompleteHeuristicFnError(Exception):
    # Called in:
    # StochasticCostAttack/value_iter_strategy.py
    # Used when a initial value function is provided that is incomplete,
    # i.e. the given function's length does not match the number of vertices
    # in the MDP construction.
    pass


class SolverNotFoundError(Exception):
    pass


class IncongruencyError(Exception):
    pass


class ConversionError(Exception):
    pass
