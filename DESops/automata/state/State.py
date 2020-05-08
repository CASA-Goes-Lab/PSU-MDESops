class State:
    def __init__(self, name):
        self.attr = set()
        self.name = name

class StateEstimate(State):
    def __init__(self, name):
        super(StateEstimate, self).__init__(init)
        pass

    def add_state(self, state):
        self.attr