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
from decomposeIter import Decomposer
from contractor import Contractor
from pysat.card import *
import glob
import itertools

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

def exportCNF(clauses, filename, ind=[], varFile=None):
    #print("running export for ", filename)
    with open(filename, "w") as f:
        if len(ind) > 0:
            f.write("c ind " + " ".join([str(i) for i in ind]) + " 0\n")
        maxVar = max([max(abs(l) for l in cl) for cl in clauses])
        f.write("p cnf {} {}\n".format(maxVar, len(clauses)))
        for cl in clauses:
            f.write(" ".join([str(l) for l in cl]) + " 0\n")

    if varFile:
        #print(varFile)
        with open(varFile, "w") as f:
            f.write(",".join ([str(v) for v in ind]))

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

def getAutarky(C):
    filename = "./tmp/autarky{}.cnf".format(randint(1,10000000))
    exportCNF(C, filename)
    cmd = "timeout 3600 python3 autarky.py {}".format(filename)
    #print(cmd)
    out = run(cmd, 3600)
    os.remove(filename)
    if "autarky vars" in out:
        for line in out.splitlines():
            line = line.rstrip()
            if line[:2] == "v ":
                return [int(c) - 1 for c in line.split()[1:]]
    else: return [i for i in range(len(C))]

def rime(C):
    filename = "./tmp/rime{}.cnf".format(randint(1,10000000))
    exportCNF(C, filename)
    cmd = "./rime -v 1 {}".format(filename)
    print(len(C), cmd)
    out = run(cmd, 3600)
    os.remove(filename)
    assert "Number of MSSes" in out
    out = out.splitlines()
    assert "Number of MSSes" in out[-1]
    mssesCount = int(out[-1].rstrip().split()[-1])

    mcses = []
    for line in out:
        if line[:4] == "MCS ":
            line = line.rstrip().split(" ")[1:]
            mcs = [int(c) for c in line if int(c) < len(C)] #0-based indexing
            mcses.append(mcs)
    assert mssesCount == len(mcses)
    return mcses

def checkSAT(C, excluded):
    s = Solver(name = "g4")
    for i in range(len(C)):
        if not i in excluded:
            s.add_clause(C[i])
    return s.solve()

def printMCSes(mcses):
    return
    for mcs in mcses:
        print("MCS~", mcs)

def mcsls(C, hard, excluded):
    if checkSAT(C, excluded):
        return [[]]

    H = []
    S = []
    mapa = []
    for i in range(len(C)):
        if i in excluded: continue
        elif i in hard:
            H.append(C[i])
        else:
            mapa.append(i)
            S.append(C[i])

    if len(S) == 0:
        return []

    filename = "./tmp/mcsls{}.wcnf".format(randint(1,10000000))
    open(filename, "w").write(renderWcnf(H,S))
    cmd = "timeout {} ./mcsls -num 10000 {}".format(3600, filename)
    print(cmd)
    out = run(cmd, 3600)
    os.remove(filename)
    mcses = []
    for line in out.splitlines():
        if line[:7] == "c MCS: ":
            mcs = [int(c) for c in line[7:].rstrip().split(" ")] #0 based indexing
            mcses.append([mapa[i - (1 + len(H))] for i in mcs])

    return mcses

def projection(source, target):
    return [i for i in source if i in target]



#return MSSes that are not subsets of artMSSes
def validCombinations2(C, hard, excluded, artMCSes, art, componentsMCSes, components, softs, wholeSofts):    
    s = Solver(name = "g4")
    for mcs in artMCSes:
        s.add_clause([i + 1 for i in mcs]) #standard MSS map blocking clause

    def isValid(mcs):
        assumptions = [i + 1 if i not in mcs else -(i + 1) for i in range(len(C)) if i not in excluded]
        return s.solve(assumptions)

    combinedMSSes = []
    for item in itertools.product(*componentsMCSes):
        mcs = []
        for comp in item:
            mcs += comp
        if isValid(mcs):
            combinedMSSes.append(mcs + [art])
    return combinedMSSes

        
def validCombinations(C, hard, excluded, arts, componentsMCSes, components, softs, wholeSofts):
    s = Solver(name = "g4")
    maxVariable = 0
    for clause in C:
        maxVariable = max(maxVariable, max([abs(l) for l in clause]))
    activators = [x + maxVariable + 1 for x in range(len(C))]
    activatorsArts = [activators[-1] + 1 + x for x in range(len(arts))]
    for i in range(len(C)):
        if i in hard:
            s.add_clause(C[i])
        elif i in arts:
            pos = 0
            for j in arts:
                if j == i:
                    break
                pos += 1
            s.add_clause(C[i] + [activatorsArts[pos]])
        else:
            s.add_clause(C[i] + [activators[i]])
    s.add_clause([-a for a in activatorsArts]) #at least one of arts is satisfied

    temp = list(itertools.product(*componentsMCSes))
    allCombinations = []
    for item in temp:
        mcs = []
        for comp in item:
            mcs += comp
        allCombinations.append(list(set(mcs)))

    #print("all combs:", len(allCombinations))
    combinedMSSes = []
    iteration = 0
    for mcs in allCombinations:
        assumptions = [-activators[i] for i in range(len(C)) if i not in (mcs + excluded)]
        if not s.solve(assumptions):
            combinedMSSes.append(mcs + arts) #arts are not part of the MSSes, hence, we need to add it to the MCSes
        iteration += 1

    return combinedMSSes


def processComponent(C, hard, excluded, ttl = 1, mainInstance = True):
    if ttl == 0: 
        mcses = mcsls(C, hard, excluded)
        if mainInstance:
            printMCSes(mcses)
        return mcses

    cont = Contractor(C, [])
    partitioning = cont.partition()
    if not partitioning:
        return mcsls(C, hard, excluded)
    part1, part2, border = list(partitioning[0]), list(partitioning[1]), list(partitioning[2])

    p1sat = checkSAT([C[i] for i in part1], [])
    p2sat = checkSAT([C[i] for i in part2], [])
    print("p1sat p2sat", p1sat, p2sat)


    components = [part1, part2]
    #Get MSSes in the individual components
    componentsMCSes = []
    Cid = 0
    softs = []
    wholeSofts = []
    for component in components:
        Cid += 1
        soft = component
        excludedRec = [i for i in range(len(C)) if i not in soft]
        softs.append(soft[:])
        componentsMCSes.append(processComponent(C, hard, excludedRec, ttl = min(0, ttl - 1), mainInstance = False))
        print("components MSSes", len(componentsMCSes[-1]))

    #assertion
    softsUnion = []
    for s in softs + wholeSofts:
        softsUnion += s

    combinedMSSes = validCombinations(C, hard, excluded, border, componentsMCSes, components, softs, wholeSofts)
    print("combinedMSSes", len(combinedMSSes))


    if mainInstance:
        printMCSes(combinedMSSes)

    artMSSes = []
    return artMSSes + combinedMSSes


def processFile(filename):
    Call, Ball = parse(filename)
    Call = [Call[i] for i in getAutarky(Call)] #autarky trim
    assert len(Ball) == 0 #currently, we do not support .gcnf instances
    decomposer = Decomposer(Call, Ball)
    components = decomposer.sccs()
    print("components:", len(components))
    print("components sizes: ", " ".join([str(len(c[0])) for c in components]))

    #print("Number of components after the decomposition:", len(components))
    nontrivialComponents = 0
    counts = []
    iteration = 1
    for component in components:
        Cids,_ = component
        C = [Call[i] for i in Cids]

        if len(C) == 1: continue #there is only one clause in that component, i.e., the clause is an MSS
        s = Solver(name = "g4")
        for cl in C:
            s.add_clause(cl)
        if s.solve(): continue #the whole component is satisfiable
        print("component size:", len(C))
        C = [C[i] for i in getAutarky(C)] #autarky trim
        print("autarky size:", len(C))
        nontrivialComponents += 1
        if iteration == 1 or True:
            #exportCNF(C, "C.cnf")
            count = len(processComponent(C, [], [], 200))
        else:
            count = len(processComponent(C, [], [], 0))
        counts.append(count)
        #print("+++count", count, iteration)
        iteration += 1

    msses = 1
    for count in counts:
        msses *= count
    print(filename, "nontrivial Components:", nontrivialComponents, "msses:", msses, "counts:", counts)
    return msses

def tests():
    files = {
            "./tests/m1_marco_input_57_100_42_refined.cnf": 40320, #5 sec
            "./tests/m2_marco_input_132_200_9_refined.cnf": 109944, #2 sec
            "./tests/m2_marco_input_159_200_51_refined.cnf": 32256, #1 sec
            "./tests/m1_marco_input_199_200_80_refined.cnf": 2304, #0.4 sec
            }
    for test in files:
        startTime = time.time()
        assert files[test] == processFile(test)
        print("duration", time.time() - startTime)

#files = glob.glob("/home/xbendik/benchmarks/randBenchsSmallRefined/*.cnf")
#print("files:", len(files))
#for f in files:
#    processFile(f)

#processFile("/home/xbendik/benchmarks/randBenchsLargeRefined/m6_marco_input_578_600_75_refined.cnf")

#tests()

import sys
if __name__ == "__main__":
    parser = argparse.ArgumentParser("MSS counter")
    parser.add_argument("input_file", help = "A path to the input file. Either a .cnf or a .gcnf instance. See ./examples/")
    args = parser.parse_args()

    if args.input_file == "tests":
        tests()
    else:
        processFile(args.input_file)
