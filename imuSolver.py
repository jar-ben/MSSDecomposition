import sys
#sys.path.insert(0, "/home/xbendik/bin/pysat")
from pysat.formula import CNF
from pysat.solvers import Solver, Minisat22

#TODO: employ model rotation in getIMU (rotate critical clauses to speed up the IMU extraction)
class IMUSolver:
    def __init__(self, C, B):
        self.C = C
        self.B = B
        self.s = Solver(name = "g4")
        self.maxVariable = 0
        for cl in C + B:
            self.maxVariable = max(self.maxVariable, max([abs(l) for l in cl]))
        self.activators = [x + self.maxVariable + 1 for x in range(len(C))]
        self.activatorsMap = {a: a - (self.maxVariable + 1) for a in self.activators}
        #add hard clauses
        for cl in B:
            self.s.add_clause(cl)
        #add soft clauses
        for i in range(len(C)):
            self.s.add_clause(C[i] + [-self.activators[i]])

    def emptyImu(self):
        return self.getImu(emptinessCheck = True)

    def getImu(self, emptinessCheck = False):
        K = []
        C = [i for i in range(len(self.C))]
        while len(C) > 0:
            f = C.pop()
            assumptions = [self.activators[i] for i in range(len(self.C)) if i != f]
            if self.s.solve(assumptions):
                if emptinessCheck:
                    return False #non-empty IMU
                K.append(f)
            else:
                C = list(set(C).intersection([self.activatorsMap[c] for c in self.s.get_core()]))
        if emptinessCheck:
            return True #empty IMU
        return K

IMUSolver([[1], [-1], [2], [-1, -2]], []).emptyImu()
