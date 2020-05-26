import sys


class Event:
    def __init__(self, label):
        self.attr = set()
        if isinstance(label, str):
            self.label = label
        else:
            sys.exit("ERROR:\nEvent label must be str")

    def name(self):
        return self.label

    def __repr__(self):
        return self.label

    def __eq__(self, other):
        if isinstance(other, Event):
            return self.label == other.label
        else:
            return False

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash(self.__repr__())
