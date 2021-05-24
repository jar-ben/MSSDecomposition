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
from pysat.card import *
import glob
import itertools

#sys.path.insert(0, "/home/xbendik/bin/pysat")
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

def variables(C):
    v = set()
    for cl in C:
        for l in cl:
            v.add(abs(l))
    return v

def maxVar(C):
    return max(variables(C))

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

def getAutarky2(C, excluded):
    mapa = []
    D = []
    for i in range(len(C)):
        if i not in excluded:
            mapa.append(i)
            D.append(C[i])

    filename = "./tmp/autarky{}.cnf".format(randint(1,10000000))
    exportCNF(D, filename)
    cmd = "timeout 3600 python3 autarky.py {}".format(filename)
    #print(cmd)
    out = run(cmd, 3600)
    os.remove(filename)
    if "autarky vars" in out:
        for line in out.splitlines():
            line = line.rstrip()
            if line[:2] == "v ":
                return [mapa[int(c) - 1] for c in line.split()[1:]]
    else: return [mapa[i] for i in range(len(D))]

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

def rime(C, hard = [], excluded = [], limit = 0, auxiliaryHard = []):
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

    for h in auxiliaryHard:
        H.append(h)

    if len(S) == 0:
        return []

    filename = "./tmp/rime{}.wcnf".format(randint(1,10000000))
    open(filename, "w").write(renderWcnf(H,S))
    cmd = "./tools/rime -v 1 {}".format(filename)
    #print(cmd)
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
            mcs = [int(c) for c in line if int(c) <= len(C)] #0-based indexing
            mcses.append([mapa[i - len(H)] for i in mcs])
            #mcses.append(mcs)
    assert mssesCount == len(mcses)
    return mcses

def checkSAT(C, excluded = []):
    s = Solver(name = "g4")
    for i in range(len(C)):
        if not i in excluded:
            s.add_clause(C[i])
    return s.solve()

def isMCS(C, N):
    D = [C[i] for i in range(len(C)) if i not in N]
    if not checkSAT(D):
        print("not even a CS")
        return False

    for n in N:
        D = [C[i] for i in range(len(C)) if i not in N]
        D.append(C[n])
        if checkSAT(D): 
            print("adding {}, {} makes it sat".format(n, C[n]))
            return False
    return True


def printMCSes(mcses):
    return
    for mcs in mcses:
        print("MCS~", mcs)

def mcsls(C, hard, excluded, limit = 0, auxiliaryHard = []):
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

    for h in auxiliaryHard:
        H.append(h)

    if len(S) == 0:
        return []

    filename = "./tmp/mcsls{}.wcnf".format(randint(1,10000000))
    open(filename, "w").write(renderWcnf(H,S))
    cmd = "timeout {} ./tools/mcsls -num {} {}".format(3600, limit, filename)
    #print(cmd)
    out = run(cmd, 3600)
    os.remove(filename)
    mcses = []
    for line in out.splitlines():
        if line[:7] == "c MCS: ":
            mcs = [int(c) for c in line[7:].rstrip().split(" ")] #1 based indexing
            mcses.append([mapa[i - (1 + len(H))] for i in mcs])

    return mcses

def projection(source, target):
    return [i for i in source if i in target]


def computeCadet(filename, activators):
    cmd = "./tools/cadet --minimize {}".format(filename)
    proc = sp.Popen([cmd], stdout=sp.PIPE, shell=True)
    (out, err) = proc.communicate()
    out = out.decode("utf-8")
    assert "SAT" in out
    if not "UNSAT" in out:
        print("UNSATISFIABLE") #this means that there is no unexplored MUS in the cell
    else:
        Cids = {}
        for i in range(len(activators)):
            Cids[activators[i]] = i + 1
        reading = False
        for line in out.splitlines():
            if reading:
                assert line[0] == "V"
                MUS = [Cids[int(l)] for l in line.split(" ")[1:] if int(l) in Cids]
            if "UNSAT" in line:
                reading = True
        print("SOLUTION")
        print(" ".join([str(n) for n in MUS]) + " 0")

def simplify2(filename, result):
    cmd = "./tools/qratpre+ --no-ble --no-qratu --no-qrate --print-formula {} > {}".format(filename, result)
    #cmd = "./tools/qratpre+ --print-formula {} > {}".format(filename, result)
    proc = sp.Popen([cmd], stdout=sp.PIPE, shell=True)
    (out, err) = proc.communicate()
    out = out.decode("utf-8")
    print("simplified")
