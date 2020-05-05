class Event:
    """
    Class to handle modified events with 'inserted' and 'deleted' member variables
    This is really only relevant for SDA_work at the moment, but most functions should
    work if Event objects are used in place of other label types (e.g strings).

    TODO: investigate if replacing event labels with Event objects uniformly is
    worthwhile (more memory intensive, but potentially easier code to work with?)
    """

    """
    def __init__(self, label, inserted=False, deleted=False):

        Initialize as:
        >>> e.Event('a', inserted=True)

        Can alternatively use the classmethods inserted() or deleted()

        self.inserted = inserted
        self.deleted = deleted
        self.label = label

    def __eq__(self, other):
        return isinstance(other, Event) and self.label == other.label and self.inserted == other.inserted and self.deleted == other.deleted
    def __ne__(self, other):
        return not self.__eq__(other)
    def __hash__(self):
        return hash((self.label, self.inserted, self.deleted))
    """

    def __init__(self, label):
        self.label = label

    def name(self):
        return self.label
