import sys


class Event:
    def __init__(self, label, **kwargs):
        self.attr = set()
        # if not isinstance(label, str):
        #    sys.exit("ERROR:\nEvent label must be str")

        if not kwargs:
            self.__dict__ = dict()
            self.__dict__["label"] = label
        else:
            self.__dict__ = kwargs
            self.__dict__["label"] = label

    def name(self):
        return self.label

    def __repr__(self):
        # Should print like: "{label}[, {key} : {val}, ...]"
        base_repr = str(self.__dict__["label"])
        extension = ", ".join(
            "{} : {}".format(k, v)
            for k, v in self.__dict__.items()
            if v and k != "label"
        )

        if extension:
            return base_repr + ", " + extension
        return base_repr

    def __eq__(self, other):
        if isinstance(other, Event):
            return self.label == other.label and self.__dict__ == other.__dict__
        else:
            return False

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash(frozenset(self.__dict__.items()))
