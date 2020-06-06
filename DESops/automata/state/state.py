import sys
from collections.abc import Iterable


class State:
    def __init__(self, name):
        self.attr = set()

        if isinstance(name, str) or isinstance(name, int):
            self.name = name
        elif isinstance(name, Iterable):
            # TODO: check that it's an iterable of states?
            self.name = name.copy()
        else:
            sys.exit("ERROR:\nState name must be str")

    def __repr__(self):
        return "(State: {0})".format(self.name)

    def __str__(self):
        return self.name

    def __eq__(self, other):
        return self.name == other.name

    def __hash__(self):
        return hash(self.name)


class StateEstimate(State):
    def __init__(self, name):
        super(StateEstimate, self).__init__(init)
        pass

    def add_state(self, state):
        self.attr
