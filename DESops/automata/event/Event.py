class Event:
    def __init__(self, label):
        self.attr = set()
        self.label = label

    def name(self):
        return self.label


