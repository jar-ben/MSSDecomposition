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
    def __init__(self, filename):
        self.filename = filename
        self.C, self.B = parse(filename)

        self.imuTrim()
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
    #F's variables: 5*dimension + 1 -- 5*dimension + Vars(F)
    def SS(self):
        #encode that N is an "MSS" (or its under-approximation)
        clauses = self.W1()
        if self.w4:
            clauses += self.W4()
        if self.w5:
            act = max(self.maxVar, maxVar(clauses))
            clauses += self.W5(act)

        #N = N1 cup N2
        for i in range(len(self.C)):
            clauses.append([-i, i + self.dimension, i + 2*self.dimension]) # N[i] -> N1[i] | N2[i]
            clauses.append([-(i + self.dimension), i]) # N1[i] -> N[i]
            clauses.append([-(i + 2*self.dimension), i]) # N2[i] -> N[i]

        #N1 cap N2 = {}
        for i in range(len(self.C)):
            clauses.append([i + self.dimension, i + 2*self.dimension])
            clauses.append([-(i + self.dimension), -(i + 2*self.dimension)])

        #C1 > N1
        act = max(self.maxVar, maxVar(clauses)) + 1
        for i in range(len(self.C)):
            clauses.append([-(i + self.dimension), i + 3*self.dimension]) # N1[i] -> C1[i]
            clauses.append([-(act + i), -(i + self.dimension)]) #the following three encode that C1 is a proper superset of N1 (using act as tseitin variable)
            clauses.append([-(act + i), i + 3*self.dimension])
            clauses.append([i + self.dimension, -(i + 3*self.dimension), act + i])
        clauses.append([act + i for i in range(len(self.C))])
            
        #C2 > N2
        act = max(self.maxVar, maxVar(clauses)) + 1
        for i in range(len(self.C)):
            clauses.append([-(i + 2*self.dimension), i + 4*self.dimension]) # N2[i] -> C2[i]
            clauses.append([-(act + i), -(i + 2*self.dimension)]) #the following three encode that C1 is a proper superset of N1 (using act as tseitin variable)
            clauses.append([-(act + i), i + 4*self.dimension])
            clauses.append([i + 2*self.dimension, -(i + 4*self.dimension), act + i])
        clauses.append([act + i for i in range(len(self.C))])

        #Disconnected


        #Minimal

        return clauses

    def W1(self):
        clauses = []
        i = 1
        for cl in self.C:
            renumCl = offsetClause(cl, 5*self.dimension)
            renumCl.append(i)
            clauses.append(renumCl)
            i += 1
        for cl in self.B:
            clauses.append(offsetClause(cl, 5*self.dimension))
        return clauses

    def W4(self):
        clauses = []
        #max model
        i = 1
        for cl in self.C:
            renumCl = []
            for l in cl:
                if l > 0:
                    clauses.append([-i, -(l + 5*self.dimension)])
                else:
                    clauses.append([-i, -(l - 5*self.dimension)])
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
                    cube = [-d] + [-offset(k, 5*self.dimension) for k in self.C[d - 1] if k != -l] #C[d] is activated and l is the only literal of C[d] satisfied by the model
                    #eq encodes that act is equivalent to the cube
                    eq = [[act] + [-x for x in cube]] # one way implication
                    for c in cube: #the other way implication
                        eq += [[-act, c]]
                    clauses += eq
                for d in self.hitmapB[-l]:
                    act += 1
                    acts.append(act)
                    cube = [-offset(k, 5*self.dimension) for k in self.B[d] if k != -l] #B[d] is activated and l is the only literal of B[d] satisfied by the model
                    #eq encodes that act is equivalent to the cube
                    eq = [[act] + [-x for x in cube]] # one way implication
                    for c in cube: #the other way implication
                        eq += [[-act, c]]
                    clauses += eq
                cl = [-(i + 1)] + acts #either C[i] is activated or the literal -l is enforced by one of the activated clauses
                clauses.append(cl)
            #break  
        return clauses
    
    def run(self):
        SSClauses = self.SS()
        SSFile = self.SSFile
        exportCNF(SSClauses, SSFile)
        #TODO: use pysat here to solve the formula        
        os.remove(SSFile)

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
    args = parser.parse_args()

    decomposer = MSSDecomposer(args.input_file)
    signal.signal(signal.SIGHUP, partial(receiveSignal, decomposer.tmpFiles))
    signal.signal(signal.SIGINT, partial(receiveSignal, decomposer.tmpFiles))
    signal.signal(signal.SIGTERM, partial(receiveSignal, decomposer.tmpFiles))

    decomposer.w2 = args.w2
    decomposer.w4 = args.w4
    decomposer.w5 = args.w5

    decomposer.run()
