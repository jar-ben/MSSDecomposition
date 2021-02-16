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

def filterPivots(C, mcses, pivots):
    filtered = []
    maxVariable = 0
    clauses = C + pivots
    for clause in clauses:
        maxVariable = max(maxVariable, max([abs(l) for l in clause]))

    activators = [x + maxVariable + 1 for x in range(len(clauses))]
    s = Solver(name = "g4")
    for i in range(len(clauses)):
        s.add_clause(clauses[i] + [activators[i]])

    #at least one pivot hold
    s.add_clause([-activators[i] for i in range(len(C), len(activators))])

    for mcs in mcses:
        assumptions = [-activators[i] for i in range(len(C)) if i not in mcs]
        if not s.solve(assumptions):
            filtered.append(mcs)

    if len(pivots) > 0:
        print("       filtered:", filtered, "all", mcses)

    return filtered

def rime(C, pivots):
    filename = "rime{}.cnf".format(randint(1,10000000))
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
    return len(filterPivots(C, mcses, pivots))

def mcslsMCSes(soft, hard, pivots):
    filename = "mcsls{}.wcnf".format(randint(1,10000000))
    open(filename, "w").write(renderWcnf(hard, soft))
    cmd = "timeout {} ./mcsls {}".format(3600, filename)
    print(cmd)
    out = run(cmd, 3600)
    mcses = []
    for line in out.splitlines():
        if line[:7] == "c MCS: ":
            mcs = [int(c) - (len(hard) + 1) for c in line[7:].rstrip().split(" ")] #0 based indexing
            mcses.append(mcs)
    return len(filterPivots(soft + hard, mcses, pivots))


def processComponent(C, pivots = [], ttl = 1):
    if ttl == 0: return rime(C, pivots) #end of recursion

    decomposer = Decomposer(C, [])
    arts = list(decomposer.articulationPoints())
    if len(arts) == 0: #there is no articulation point, hence, we end the recursion
        return rime(C, pivots)

    #pick and use one articulation point
    art = arts[0] #we should sample instead of picking the first one
    Ccopy = C[:art] + C[art + 1:]
    print("C len: {}, Ccopy: {}".format(len(C), len(Ccopy)))
    print("C MSSes:{}, Ccopy MSSes:{}".format(rime(C, []), rime(Ccopy, [])))

    components = Decomposer(Ccopy, []).sccs()
    #TODO: the number of components should be always bigger than 1
    # assert len(components) > 1

    if len(components) == 1:
        return rime(C, pivots) #the decomposition did not work
    
    counts = []

    hardArtCount = mcslsMCSes(Ccopy, [C[art]], pivots)#the number of MSSes that include the art clause
    print("Ccopy + hard art MSSes:", hardArtCount)
    pivots.append(C[art])

    #the counts for the components without the art clause
    for component in components:
        C,B = component
        #if len(C) == 1: continue #there is only one clause in that component, i.e., the clause is an MSS
        #s = Solver(name = "g4")
        #for cl in C:
        #    s.add_clause(cl)
        #if s.solve(): continue #the whole component is satisfiable

        print("inner C:", len(C))
        count = processComponent(C, pivots, ttl - 1)
        print("inner count:", count)
        #count = rime(C, pivots + [C[art]])
        counts.append(count)

    msses = 1
    for count in counts:
        msses *= count
    msses += hardArtCount
    print(counts, msses)
    return msses


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
        C,B = component

        if len(C) == 1: continue #there is only one clause in that component, i.e., the clause is an MSS
        s = Solver(name = "g4")
        for cl in C:
            s.add_clause(cl)
        if s.solve(): continue #the whole component is satisfiable

        nontrivialComponents += 1
        if iteration == 5:
            count = processComponent(C, [], 1)
        else:
            count = processComponent(C, [], 0)
        counts.append(count)
        #print("+++count", count, iteration)
        iteration += 1

    msses = 1
    for count in counts:
        msses *= count
    print(filename, "nontrivial Components:", nontrivialComponents, "msses:", msses, "counts:", counts)


#files = glob.glob("/home/xbendik/benchmarks/randBenchsSmallRefined/*.cnf")
#print("files:", len(files))
#for f in files:
#    processFile(f)

processFile("/home/xbendik/benchmarks/randBenchsSmallRefined/m3_marco_input_384_400_2_refined.cnf")
#processFile("/home/xbendik/benchmarks/randBenchsSmallRefined/m4_marco_input_386_400_32_refined.cnf")
#processFile("/home/xbendik/rime/examples/C210_FW_UT_8630_uniques.cnf")
#processFile("/home/xbendik/rime/examples/bf1355-228.cnf")
