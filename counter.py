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
from decompose import Decomposer
from pysat.card import *
import glob
import itertools

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
    print(cmd)
    out = run(cmd, 3600)
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

    filename = "./tmp/mcsls{}.wcnf".format(randint(1,10000000))
    open(filename, "w").write(renderWcnf(H,S))
    cmd = "timeout {} ./mcsls {}".format(3600, filename)
    print(cmd)
    out = run(cmd, 3600)
    mcses = []
    for line in out.splitlines():
        if line[:7] == "c MCS: ":
            mcs = [int(c) for c in line[7:].rstrip().split(" ")] #0 based indexing
            mcses.append([mapa[i - (1 + len(H))] for i in mcs])

    return mcses

#return MSSes that are not subsets of artMSSes
def validCombinations2(C, hard, excluded, artMCSes, art, componentsMCSes, components, softs):
    s = Solver(name = "g4")
    cls = []
    for mcs in artMCSes:
        s.add_clause([-(x + 1) for x in mcs])
        cls.append([-(x + 1) for x in mcs])
        assert set(mcs) - set(hard) == set(mcs)
    witnessed = []
    nonWitnessed = []

    for cid in range(len(componentsMCSes)):
        component = componentsMCSes[cid]
        soft = softs[cid]
        coSoft = [i for i in range(len(C)) if i not in soft]
        w, n = [], []
        for mcs in component:
            if s.solve([i + 1 for i in (mcs + coSoft)]): 
                w.append(mcs) #the correcponding MSS is not a subset of any of artMSSes, i.e, a unexplored MSS seed
            else:
                n.append(mcs)
            if len(cls) < 5:
                print("PPP", cls, [i + 1 for i in mcs])
        witnessed.append(w)
        nonWitnessed.append(n)
        print("NW", len(n), len(w))
    assert len(componentsMCSes) == len(witnessed) == len(nonWitnessed)


    combinedMSSes = []
    for i in range(len(componentsMCSes)):
        validCombinationsList = [witnessed[i]]
        validCombinationsList += [nonWitnessed[j] for j in range(i)]
        validCombinationsList += [componentsMCSes[j] for j in range(i + 1, len(componentsMCSes))]
        combinedMSSes += [list(item) for item in itertools.product(*validCombinationsList)]
    return combinedMSSes
        

def validCombinations(C, hard, excluded, artMSSes, art, componentsMCSes, components, softs):
    s = Solver(name = "g4")
    maxVariable = 0
    for clause in C:
        maxVariable = max(maxVariable, max([abs(l) for l in clause]))
    activators = [x + maxVariable + 1 for x in range(len(C))]
    for i in range(len(C)):
        if i in hard:
            s.add_clause(C[i])
        elif i == art:
            s.add_clause(C[i])
        else:
            s.add_clause(C[i] + [activators[i]])

    temp = list(itertools.product(*componentsMCSes))
    allCombinations = []
    for item in temp:
        mcs = []
        for comp in item:
            mcs += comp
        allCombinations.append(list(set(mcs)))

    combinedMSSes = []
    for mcs in allCombinations:
        assumptions = [-activators[i] for i in range(len(C)) if i not in (mcs + excluded)]
        if not s.solve(assumptions):
            combinedMSSes.append(mcs + [art]) #art is not part of the MSSes, hence, we need to add it to the MCSes
    print("BBB", len(combinedMSSes), len(validCombinations2(C, hard, excluded, artMSSes, art, componentsMCSes, components, softs)))
    #return validCombinations2(C, hard, excluded, artMSSes, art, componentsMCSes, components)
    return combinedMSSes

def processComponent(C, hard, excluded, ttl = 1):
    print("hard: {}, excluded: {}, ttl: {}".format(len(hard), len(excluded), ttl))
    if ttl == 0: return mcsls(C, hard, excluded)

    decomposer = Decomposer(C, [])
    arts = [art for art in list(decomposer.articulationPoints()) if art not in hard]
    print("arts:", len(arts))
    if len(arts) == 0: #there is no articulation point, hence, we end the recursion
        return mcsls(C, hard, excluded)

    #pick and use one articulation point
    found = False
    for art in arts:
        components = Decomposer(C, []).sccs(excluded + [art])
        if len(components) > 1:
            found = True
            break
    if not found:
        print("single component")
        return mcsls(C, hard, excluded)

    #Get MSSes when art is presented
    artMSSes = processComponent(C, hard + [art], excluded, ttl - 1)
    print("QQQ", len(artMSSes), ttl)
    print("ttl: {}, art: {}, artMSSes: {}".format(ttl, art, len(artMSSes)))
    
    #Get MSSes in the individual components
    componentsMCSes = []
    Cid = 0
    softs = []
    for component in components:
        Cid += 1
        soft,_ = component
        excludedRec = list(set(excluded + [i for i in range(len(C)) if i not in soft] + [art]))

        #check for satisfiability
        if checkSAT(C, excludedRec):
            pass
            #componentsMCSes.append([[]]) #the whole component is satisfiable, i.e., [] is the only MCS
        else:
            softs.append(soft)
            print("soft", soft)
            print("excluded", excludedRec)
            componentsMCSes.append(processComponent(C, hard, excludedRec, min(40, ttl - 1)))
            print("components MSSes:", len(componentsMCSes[-1]), "components:", len(componentsMCSes))


    combinedMSSes = validCombinations(C, hard, excluded, artMSSes, art, componentsMCSes, components, softs)
    print(len(artMSSes), len(combinedMSSes), len(artMSSes + combinedMSSes))

    if len(artMSSes + combinedMSSes) < 50:
        print("malina")
        allMCSes = mcsls(C, hard, excluded)
        print("art: {}\n artMSSes: {}\ncombinedMSSes: {}\n mcsls: {}\ncomponentsMCSes: {}".format(art,artMSSes, combinedMSSes, allMCSes, componentsMCSes))
        assert len(allMCSes) == len(artMSSes + combinedMSSes)
        

    return artMSSes + combinedMSSes


def processFile(filename):
    Call, Ball = parse(filename)
    assert len(Ball) == 0 #currently, we do not support .gcnf instances
    decomposer = Decomposer(Call, Ball)
    components = decomposer.sccs()
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
            exportCNF(C, "C.cnf")
            count = len(processComponent(C, [], [], 150))
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
            "/home/xbendik/benchmarks/randBenchsSmallRefined/m1_marco_input_57_100_42_refined.cnf": 40320, #5 sec
            "/home/xbendik/benchmarks/randBenchsSmallRefined/m2_marco_input_132_200_9_refined.cnf": 109944, #2 sec
            "/home/xbendik/benchmarks/randBenchsSmallRefined/m2_marco_input_159_200_51_refined.cnf": 32256, #1 sec
            "/home/xbendik/benchmarks/randBenchsSmallRefined/m1_marco_input_199_200_80_refined.cnf": 2304, #0.4 sec
            "/home/xbendik/benchmarks/randBenchsSmallRefined/m3_marco_input_384_400_2_refined.cnf": 414720 #0.6 sec
            }
    for test in files:
        assert files[test] == processFile(test)

#files = glob.glob("/home/xbendik/benchmarks/randBenchsSmallRefined/*.cnf")
#print("files:", len(files))
#for f in files:
#    processFile(f)

#processFile("/home/xbendik/benchmarks/randBenchsLargeRefined/m6_marco_input_578_600_75_refined.cnf")

tests()

#processFile("/home/xbendik/rime/examples/C210_FW_UT_8630_uniques.cnf")
#processFile("/home/xbendik/benchmarks/randBenchsSmallRefined/m3_marco_input_384_400_2_refined.cnf")
#processFile("/home/xbendik/benchmarks/randBenchsSmallRefined/m4_marco_input_386_400_32_refined.cnf")
#processFile("/home/xbendik/rime/examples/bf1355-228.cnf")
