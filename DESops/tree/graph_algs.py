class SCCHelper:

    def __init__(self, nfa):
        self.nfa = nfa
        self.time = 0
        self.stack = []
        self.nfa.vs["visitTime"] = -1
        self.nfa.vs["lowTime"] = -1
        self.nfa.vs["inStack"] = False
        self.sccList = []

    def computeSCC(self):
        """
        Compute the strongly connected components of the ATA viewed as a directed graph.
        Result guaranteed to be in reverse topological order.
        """
        for q in self.nfa.vs:
            if q["visitTime"] < 0:
                self.computePointedSCC(q)
        return self.sccList

    def computePointedSCC(self, q):
        q["visitTime"] = self.time
        q["lowTime"] = self.time
        self.time += 1
        self.stack.append(q)
        q["inStack"] = True

        for s in q.neighbors(mode="out"):
            if s["visitTime"] < 0:
                self.computePointedSCC(s)
                q["lowTime"] = min(q["lowTime"], s["lowTime"])
            elif s["inStack"]:
                q["lowTime"] = min(q["lowTime"], s["visitTime"])

        if q["lowTime"] == q["visitTime"]:
            s = None
            scc = set()
            while q != s:
                s = self.stack.pop()
                s["inStack"] = False
                scc.add(s["name"])
            self.sccList.append(scc)


