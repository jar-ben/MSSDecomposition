import sys
from math import log
import subprocess as sp
import random
import time
from statistics import median
from random import randint
import argparse
import os
from functools import partial
import signal
sys.path.insert(0, "/home/xbendik/bin/pysat")
from pysat.formula import CNF
from pysat.solvers import Solver, Minisat22


def receiveSignal(tempFiles, signalNumber, frame):
    print(tempFiles, signalNumber, frame)
    print('Received signal:', signalNumber)
    print('Cleaning tmp files')
    for f in tempFiles:
        if os.path.exists(f):
            print("removing", f, "...", end="")
            os.remove(f)
            print("removed")
    sys.exit()

def maxVar(C):
    m = 0
    for cl in C:
        for l in cl:
            m = max(m,abs(l))
    return m

def renderWcnf(Hard, Soft):
    nvariables = maxVar(Hard + Soft)
    clauses = len(Hard) + len(Soft)
    hardWeight = len(Soft) + 1
    softWeight = 1

    result = "p wcnf {} {} {}\n".format(nvariables, clauses, hardWeight)
    for cl in Hard:
        result += str(hardWeight) + " " + " ".join([str(l) for l in cl]) + " 0\n"
    for cl in Soft:
        result += str(softWeight) + " " + " ".join([str(l) for l in cl]) + " 0\n"

    return result


def run(cmd, timeout, ttl = 3):
    proc = sp.Popen([cmd], stdout=sp.PIPE, stderr=sp.PIPE, shell=True)
    try:
        (out, err) = proc.communicate(timeout = int(timeout * 1.1) + 1)
        out = out.decode("utf-8")
    except sp.TimeoutExpired:
        proc.kill()
        try:
            (out, err) = proc.communicate()
            out = out.decode("utf-8")
        except ValueError:
            if ttl > 0:
                return run(cmd, timeout, ttl - 1)
            out = ""
    return out

def randomBool():
    return bool(random.getrandbits(1))

def exportCNF(clauses, filename):
    with open(filename, "w") as f:
        maxVar = max([max(abs(l) for l in cl) for cl in clauses])
        f.write("p cnf {} {}\n".format(maxVar, len(clauses)))
        for cl in clauses:
            f.write(" ".join([str(l) for l in cl]) + " 0\n")

#parse .gcnf instance,
#returns a pair C,B where B contains the base (hard) clauses and C the other clauses
def parse(filename):
    C = []
    B = []
    with open(filename, "r") as f:
        lines = f.readlines()
        if filename[-5:] == ".gcnf":
            for line in lines[1:]:
                if line[0] in ["p","c"]: continue
                line = line.split(" ")
                cl = [int(i) for i in line[1:-1]]
                if len(cl) > 0:
                    if line[0] == "{0}":
                        B.append(cl)
                    else:
                        C.append(cl)
        else:
            for line in lines[1:]:
                if line[0] in ["p","c"]: continue
                line = line.split(" ")
                cl = [int(i) for i in line[:-1]]
                if len(cl) > 0:
                    C.append(cl)
    return C,B

def offset(a, off):
    if a > 0:
        return a + off
    return a - off

def offsetClause(cl, off):
    return [offset(l, off) for l in cl]    

class MSSDecomposer:
    def __init__(self, filename = None, C = None):
        self.filename = filename
        if filename:
            self.C, self.B = parse(filename)
        else:
            self.C, self.B = C, []

        #self.imuTrim()
        self.dimension = len(self.C)
        self.maxVar = 2*self.dimension + 2*maxVar(self.C + self.B)
        self.rid = randint(1,10000000)
        flatten = []
        for cl in (self.B + self.C):
            flatten += cl
        self.lits = set([l for l in flatten])
        self.hitmapC = {}
        self.hitmapB = {}
        for l in self.lits:
            self.hitmapC[l] = []
            self.hitmapC[-l] = []
            self.hitmapB[l] = []
            self.hitmapB[-l] = []
        for i in range(len(self.C)):
            for l in self.C[i]:
                assert l in self.lits
                self.hitmapC[l].append(i + 1) #+1 offset
        for i in range(len(self.B)):
            for l in self.B[i]:
                assert l in self.lits
                self.hitmapB[l].append(i) #note that here we store 0-based index as opposed to hitmapC


        #selection variables for individual wrappers. True means selected
        self.w2 = True
        self.w3 = True
        self.w4 = True
        self.w5 = True

        self.SSFile = "/var/tmp/SS_{}.cnf".format(self.rid)
        self.SSIndFile = self.SSFile[:-4] + "_ind.cnf"
        self.LSSFile = "/var/tmp/LSS_{}.cnf".format(self.rid)
        self.LSSIndFile = self.LSSFile[:-4] + "_ind.cnf"
        self.tmpFiles = [self.SSFile, self.SSIndFile, self.LSSFile, self.LSSIndFile]

        #VARIABLES INFO
        #N: 1 -- dimension
        #N1: dimension + 1 -- 2*dimension
        #N2: 2*dimension + 1 -- 3*dimension
        #C1: 3*dimension + 1 -- 4*dimension
        #C2: 4*dimension + 1 -- 5*dimension
        #N': 5*dimension + 1 -- 6*dimension
        #F's variables: 6*dimension + 1 -- 6*dimension + Vars(F)
        self.acts = {}
        self.acts["N"] = [i + 1 for i in range(len(self.C))]
        self.acts["N1"] = [i + 1 + len(self.C) for i in range(len(self.C))]
        self.acts["N2"] = [i + 1 + 2*len(self.C) for i in range(len(self.C))]
        self.acts["C1"] = [i + 1 + 3*len(self.C) for i in range(len(self.C))]
        self.acts["C2"] = [i + 1 + 4*len(self.C) for i in range(len(self.C))]
        self.acts["M"] = [i + 1 + 5*len(self.C) for i in range(len(self.C))]
        self.nvarsOffset = 6*self.dimension
        self.mvarsOffset = 6*self.dimension + maxVar(self.C) 
        self.vars = {}
        self.vars["Nvars"] = [v + self.nvarsOffset for v in variables(self.C)]       
        self.vars["Mvars"] = [v + self.mvarsOffset for v in variables(self.C)]       
        
        self.minAct = self.vars["Mvars"][-1] + 1
    

    def isMSS(self, N):
        s = Solver(name = "g4")
        Ncls = []
        for i in range(len(self.C)):
            if i not in N:
                Ncls.append(self.C[i])

        for i in N:
            s = Solver(name = "g4")
            for cl in Ncls:
                s.add_clause(cl)
            s.add_clause(self.C[i])
            if s.solve(): return False
        return True

    def disjointMUSes(self):
        assert len(self.B) == 0
        filename = "./tmp/disjoint_" + str(randint(1,10000000)) + ".cnf"
        exportCNF(self.C, filename)
        cmd = "timeout 300 ./unimus_disjoint -a marco {}".format(filename)
        #print(cmd)
        out = run(cmd, 60)
        if not "disjoint pair" in out:
            return [],[]
        reading = False
        m1 = []
        m2 = []
        for line in out.splitlines():
            if reading and len(m1) == 0:
                m1 = [int(i) for i in line.rstrip().split()]
            elif reading and len(m2) == 0:
                m2 = [int(i) for i in line.rstrip().split()]
                break
            elif reading:
                assert False
            if line.rstrip() == "disjoint pair":
                reading = True
        return m1, m2

    def imuTrim(self):
        assert self.B == []
        imu = self.getImu()
        self.imuSize = len(imu)

        autarky = [i for i in range(len(self.C))]
        C = [self.C[c] for c in sorted(set(autarky) - set(imu))]
        B = [self.C[c] for c in imu]
        self.C, self.B = C, B

    def getImu(self):
        cmd = "timeout 3600 python3 gimu.py {}".format(self.filename)
        out = run(cmd, 3600)
        if "imu size" in out:
            for line in out.splitlines():
                line = line.rstrip()
                if line[:2] == "v ":
                    return [int(c) - 1 for c in line.split()[1:]]
        return []

    #VARIABLES INFO
    #N: 1 -- dimension
    #N1: dimension + 1 -- 2*dimension
    #N2: 2*dimension + 1 -- 3*dimension
    #C1: 3*dimension + 1 -- 4*dimension
    #C2: 4*dimension + 1 -- 5*dimension
    #N': 5*dimension + 1 -- 6*dimension
    #F's variables: 6*dimension + 1 -- 7*dimension + Vars(F)
    #(N')'s variables: 7*dimension + 1 -- 8*dimension + Vars(F) (used to reason about supersets of N)
    def SS(self):
        #encode that N is an element of an MSS wrapper
        clauses = self.W1()
        if self.w4:
            clauses += self.W4()
        if self.w5:
            act = max(self.minAct, maxVar(clauses))
            clauses += self.W5(act)

        #encode that N is an MSS via qbf encoding, i.e., every M > N is unsat
        #first we encode that M > N
        act = max(self.minAct, maxVar(clauses)) + 1
        for i in range(len(self.C)):
            clauses.append([-self.acts["N"][i], self.acts["M"][i]]) # N[i] -> M[i]
            clauses.append([-(act + i), -self.acts["N"][i]]) #the following three encode the proper superset 
            clauses.append([-(act + i), self.acts["M"][i]])
            clauses.append([self.acts["N"][i], -self.acts["M"][i], act + i])
        clauses.append([act + i for i in range(len(self.C))])
        #second, we encode that N' is unsat
        cls = []
        i = 0
        for cl in self.C:
            renumCl = offsetClause(cl, self.mvarsOffset)
            renumCl.append(self.acts["M"][i])
            cls.append(renumCl)
            i += 1
        for cl in self.B:
            cls.append(offsetClause(cl, self.mvarsOffset))
        act = max(self.minAct, maxVar(clauses))
        clauses += CNF(from_clauses=cls).negate(act).clauses
          

        #both N1 and N2 are non-empty
        clauses.append(self.acts["N1"])
        clauses.append(self.acts["N2"])

        #N = N1 cup N2
        for i in range(len(self.C)):
            clauses.append([-self.acts["N"][i], self.acts["N1"][i], self.acts["N2"][i]]) # N[i] -> N1[i] | N2[i]
            clauses.append(-self.acts["N1"][i], self.acts["N"][i]) #N1[i] -> N[i]
            clauses.append(-self.acts["N2"][i], self.acts["N"][i]) #N2[i] -> N2[i]

        #C1 cap C2 = {}
        for i in range(len(self.C)):
            clauses.append([-self.acts["C1"][i], -self.acts["C2"][i]])

        #C1 supsetneq N1
        act = max(self.minAct, maxVar(clauses)) + 1
        for i in range(len(self.C)):
            clauses.append([-self.acts["N1"][i], self.acts["C1"][i]]) # N1[i] -> C1[i]
            clauses.append([-(act + i), -self.acts["N1"][i]]) #the following three encode the proper superset 
            clauses.append([-(act + i), self.acts["C1"][i]])
            clauses.append([self.acts["N1"][i], -self.acts["C1"][i], act + i])
        clauses.append([act + i for i in range(len(self.C))])
            
        #C2 supsetneq N2
        act = max(self.minAct, maxVar(clauses)) + 1
        for i in range(len(self.C)):
            clauses.append([-self.acts["N2"][i], self.acts["C2"][i]]) # N2[i] -> C2[i]
            clauses.append([-(act + i), -self.acts["N2"][i]]) #the following three encode the proper superset 
            clauses.append([-(act + i), self.acts["C2"][i]])
            clauses.append([self.acts["N2"][i], -self.acts["C2"][i], act + i])
        clauses.append([act + i for i in range(len(self.C))])

        #Disconnected
        for i in range(len(self.C)):
            cl = self.C[i - 1]
            for l in cl:
                for j in self.hitmapC[l]:
                    clauses.append([-self.acts["C1"][i], -self.acts["C2"][i]]) #C1[i] -> not C2[j]
                    clauses.append([-self.acts["C2"][i], -self.acts["C1"][i]]) #C2[i] -> not C1[j]

        #Minimal
        for i in range(len(self.C)):
            cl = [self.acts["C1"][i], self.acts["C2"][i]]
            for l in self.C[i - 1]:
                for j in self.hitmapC[-l]:
                    cl.append(self.acts["C1"][J])
            clauses.append(cl[:])
            cl = [self.acts["C1"][i], self.acts["C2"][i]]
            for l in self.C[i - 1]:
                for j in self.hitmapC[-l]:
                    cl.append(self.acts["C2"][j])
            clauses.append(cl[:])

        #disjoint MUSes M1 M2 as subsets of C1 and C2 (to ensure their unsatisfiability)
        m1, m2 = self.disjointMUSes()
        for i in m1:
            clauses.append([self.acts["C1"][i]])
        for i in m2:
            clauses.append([self.acts["C2"][i]])

        return clauses

    def W1(self):
        clauses = []
        i = 0
        for cl in self.C:
            renumCl = offsetClause(cl, self.nvarsOffset)
            renumCl.append(self.acts["N"][i])
            clauses.append(renumCl)
            i += 1
        for cl in self.B:
            clauses.append(offsetClause(cl, self.nvarsOffset))
        return clauses

    def W4(self):
        clauses = []
        #max model
        i = 0
        for cl in self.C:
            renumCl = []
            for l in cl:
                if l > 0:
                    clauses.append([-self.acts["N"][i], -(l + self.nvarsOffset)])
                else:
                    clauses.append([-self.acts["N"][i], -(l - self.nvarsOffset)])
            i += 1
        return clauses

    def W5(self, act):
        clauses = []
        for i in range(len(self.C)):
            for l in self.C[i]:
                cl = [-i]
                acts = []
                for d in self.hitmapC[-l]:
                    act += 1
                    acts.append(act)
                    cube = [-d] + [-offset(k, self.nvarsOffset) for k in self.C[d - 1] if k != -l] #C[d] is activated and l is the only literal of C[d] satisfied by the model
                    #eq encodes that act is equivalent to the cube
                    eq = [[act] + [-x for x in cube]] # one way implication
                    for c in cube: #the other way implication
                        eq += [[-act, c]]
                    clauses += eq
                for d in self.hitmapB[-l]:
                    act += 1
                    acts.append(act)
                    cube = [-offset(k, self.nvarsOffset) for k in self.B[d] if k != -l] #B[d] is activated and l is the only literal of B[d] satisfied by the model
                    #eq encodes that act is equivalent to the cube
                    eq = [[act] + [-x for x in cube]] # one way implication
                    for c in cube: #the other way implication
                        eq += [[-act, c]]
                    clauses += eq
                cl = [-self.acts["N"][i]] + acts #either C[i] is activated or the literal -l is enforced by one of the activated clauses
                clauses.append(cl)
            #break  
        return clauses
    
    def run(self):
        return self.run_qbf() if self.qbf else self.run_basic()

    #VARIABLES INFO
    #N: 1 -- dimension
    #N1: dimension + 1 -- 2*dimension
    #N2: 2*dimension + 1 -- 3*dimension
    #C1: 3*dimension + 1 -- 4*dimension
    #C2: 4*dimension + 1 -- 5*dimension
    #N': 5*dimension + 1 -- 6*dimension
    #F's variables: 6*dimension + 1 -- 7*dimension + Vars(F)
    #(N')'s variables: 7*dimension + 1 -- 8*dimension + Vars(F) (used to reason about supersets of N)
    def run_qbf(self):
        SSClauses = self.SS()
        result = "p cnf {} {}\n".format(maxVar(SSClauses), len(SSClauses))
        a = []
        e = []
        result += "e " + " ".join([str(i) for i in activators + primeActivatorsFlatten + primeVars + unexCurrents]) + " 0 \n"
        result += "a " + " ".join([str(i) for i in Vars + currents]) + " 0 \n"
    for cl in main:
        result += " ".join([str(l) for l in cl]) + " 0\n"

    def run_basic(self):
        SSClauses = self.SS()
        s = Solver(name = "g4")
        for cl in SSClauses:
            s.add_clause(cl)
        divisions = []
        #for _ in range(len(self.C)):
        for iter in range(1000):
            print(iter)
            if not s.solve(): break
            model = s.get_model()
            C1 = [i - 3*len(self.C) for i in range(3*len(self.C), 4*len(self.C)) if model[i] > 0]
            C2 = [i - 4*len(self.C) for i in range(4*len(self.C), 5*len(self.C)) if model[i] > 0]
            #print("C:", len(self.C), "C1:", len(C1), "C2:", len(C2))
            block = [-model[i] for i in range(3*len(self.C), 5*len(self.C))]
            s.add_clause(block[:])
            divisions.append([C1, C2])

            s1 = Solver(name = "g4")
            for i in C1:
                s1.add_clause(self.C[i])
            s2 = Solver(name = "g4")
            for i in C2:
                s2.add_clause(self.C[i])

            N = [i for i in range(len(self.C)) if model[i] > 0]
            if self.isMSS(N):
                print("\n\n----AAA---\n\n")
                return divisions[-1:]
        print("\n\n---BBB---\n\n")
        return divisions

import sys
if __name__ == "__main__":
    parser = argparse.ArgumentParser("MSS decomposer")
    parser.add_argument("--verbose", "-v", action="count", help = "Use the flag to increase the verbosity of the outputs. The flag can be used repeatedly.")
    parser.add_argument("input_file", help = "A path to the input file. Either a .cnf or a .gcnf instance. See ./examples/")
    parser.add_argument("--w2", action='store_true', help = "Use the wrapper W2, i.e., autarky (multiple wrappers can be used simultaneously)")
    parser.add_argument("--w3", action='store_true', help = "Use the wrapper W3 (multiple wrappers can be used simultaneously)")
    parser.add_argument("--w4", action='store_true', help = "Use the wrapper W4 (multiple wrappers can be used simultaneously)")
    parser.add_argument("--w5", action='store_true', help = "Use the wrapper W5 (multiple wrappers can be used simultaneously)")
    parser.add_argument("--imu", action='store_true', help = "Use IMU.")
    parser.add_argument("--qbf", action='store_true', help = "Ensure that N is an MSS via QBF solver.", default=False)
    args = parser.parse_args()

    decomposer = MSSDecomposer(args.input_file)
    signal.signal(signal.SIGHUP, partial(receiveSignal, decomposer.tmpFiles))
    signal.signal(signal.SIGINT, partial(receiveSignal, decomposer.tmpFiles))
    signal.signal(signal.SIGTERM, partial(receiveSignal, decomposer.tmpFiles))

    decomposer.w2 = args.w2
    decomposer.w4 = args.w4
    decomposer.w5 = args.w5
    decomposer.qbf = args.qbf

    decomposer.run()
