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
from MSSdecompose import MSSDecomposer
from pysat.card import *
import glob
import itertools
sys.path.insert(0, "/home/xbendik/bin/pysat")
from pysat.formula import CNF
from pysat.solvers import Solver, Minisat22
from misc import *

class Counter:
    def __init__(self, filename):
        self.filename = filename
        self.Call, _ = parse(filename) #included from misc.py
        self.Call = [self.Call[i] for i in getAutarky(self.Call)] #autarky trim, included from misc.py
        self.MCSEnumerator = "mcsls"
        self.ttl = 200
        self.debug = False
        self.explicitMCSes = 0
        self.verbosity = 1

    def run(self):
        decomposer = Decomposer(self.Call, [])
        components = decomposer.sccs()
        print("components:", len(components))
        print("components sizes: ", " ".join([str(len(c[0])) for c in components]))

        nontrivialComponents = 0
        counts = []
        componentsMCSes = []
        for component in components:
            Cids,_ = component
            C = [self.Call[i] for i in Cids]

            if len(C) == 1: continue #there is only one clause in that component, i.e., the clause is an MSS
            s = Solver(name = "g4")
            for cl in C:
                s.add_clause(cl)
            if s.solve(): continue #the whole component is satisfiable
            print("component size:", len(C))
            A = getAutarky(C)
            C = [C[i] for i in A] #autarky trim
            print("autarky size:", len(C))
            nontrivialComponents += 1
            MCSes = self.processComponent(C, [], [], self.ttl)
            MCSesOrg = []
            for m in MCSes:
                MCSesOrg.append([Cids[A[i]] for i in m])

            componentsMCSes.append(MCSesOrg)
            counts.append(len(componentsMCSes[-1]))


        msses = 1
        for count in counts:
            msses *= count
        print(self.filename, "nontrivial Components:", nontrivialComponents, "msses:", msses, "counts:", counts, "explicit:", self.explicitMCSes)


        if self.verbosity >= 2:
            with open("mcses.txt", "w") as f:
                for item in itertools.product(*componentsMCSes):
                    mcs = []
                    for m in item:
                        mcs += m
                    print("MCS {}".format(" ".join([str(i) for i in mcs])))

        return msses

    def getMCSes(self, C, hard, excluded, atLeastOne, limit = 50000):
        assert len(hard) == 0
        H = []
        S = []

        auxiliaryHards = []
        for s in atLeastOne:
            cl = []
            for i in s:
                if i not in excluded:
                    cl += C[i]
            if len(cl) == 0:
                return []
            auxiliaryHards.append(cl)

        mcses = []
        if self.MCSEnumerator == "mcsls":
            mcses = mcsls(C, H, excluded, limit, auxiliaryHards)
        elif self.MCSEnumerator == "rime":
            mcses = rime(C, H, excluded, limit, auxiliaryHards)

        if self.debug:
            #assertion
            for mcs in mcses:
                assert checkSAT([C[i] for i in range(len(C)) if i not in (mcs + excluded)])
            #assertion
            for mcs in mcses:
                for b in atLeastOne:
                    assert len([i for i in b if i not in (mcs + excluded)]) > 0

        if len(mcses) == limit:
            print("MCS COUNT LIMIT REACHED")
        self.explicitMCSes += len(mcses)
        return mcses

    def verifyDecomposition(self, C, components):
        c1, c2 = components[:2]
        print(c1, c2)
        for cid in c1:
            for l in C[cid]:
                for cid2 in c2:
                    assert not -l in C[cid2]

    #checkpoint
    #return MSSes that are not subsets of artMSSes
    def validCombinations2(self, C, excluded, artMCSes, B, componentsMCSes):
        s = Solver(name = "g4")
        for mcs in artMCSes:
            s.add_clause([i + 1 for i in mcs]) #standard MSS map blocking clause
            if self.debug: assert checkSAT([C[i] for i in range(len(C)) if i not in (mcs + excluded)])

        def isValid(mcs):
            assumptions = [i + 1 if i not in (mcs + B) else -(i + 1) for i in range(len(C)) if i not in excluded]
            return s.solve(assumptions)

        combinedMSSes = []
        for item in itertools.product(*componentsMCSes):
            mcs = []
            for comp in item:
                mcs += comp
            if self.debug: assert checkSAT([C[i] for i in range(len(C)) if i not in (mcs + B + excluded)])
            if isValid(mcs):
                combinedMSSes.append(mcs + B)
        return combinedMSSes

    def validCombinations(self, C, excluded, artMSSes, B, componentsMCSes):
        s = Solver(name = "g4")
        maxVariable = 0
        for clause in C:
            maxVariable = max(maxVariable, max([abs(l) for l in clause]))
        activators = [x + maxVariable + 1 for x in range(len(C))]
        for i in range(len(C)):
            s.add_clause(C[i] + [activators[i]])

        s.add_clause([-activators[i] for i in B])

        temp = list(itertools.product(*componentsMCSes))
        allCombinations = []
        for item in temp:
            mcs = []
            for comp in item:
                mcs += comp
            allCombinations.append(list(set(mcs)))

        #print("all combs:", len(allCombinations))
        combinedMSSes = []
        for mcs in allCombinations:
            assumptions = [-activators[i] for i in range(len(C)) if i not in (mcs + excluded + B)]
            if not s.solve(assumptions):
                combinedMSSes.append(mcs + B) #B is not part of the MSSes, hence, we need to add it to the MCSes

        return combinedMSSes

    def decomposeViaMSSes(self, C, atLeastOne, excluded):
        mapa = []
        mapaRe = {}
        for i in range(len(C)):
            if i not in excluded:
                mapaRe[i] = len(mapa)
                mapa.append(i)

        atLeast = []
        for a in atLeastOne:
            a = [i for i in a if i not in excluded]
            atLeast.append([mapaRe[i] for i in a])
        decomposer = MSSDecomposer(C = [C[i] for i in range(len(C)) if i not in excluded], mapa = atLeast)
        decomposer.maxsat = True
        C1, C2, B = decomposer.run()
        if C1 == None:
            return C1, C2, B
        print("\n\n ", len(C1), len(C2), "\n\n")
        return [mapa[c] for c in C1], [mapa[c] for c in C2], [mapa[c] for c in B]

    def decompose(self, C, atLeastOne, excluded):
        return self.decomposeViaMSSes(C, atLeastOne, excluded)

    def processComponent(self, C, atLeastOne, excluded, ttl = 1, mainInstance = True):
        #autarky trim
        aut = getAutarky2(C, excluded)
        excluded = [i for i in range(len(C)) if i not in aut]

        for a in atLeastOne:
            if len([i for i in a if i not in excluded]) == 0:
                return []
        print("ttl", ttl)
        if ttl == 0 or len(C) - len(excluded) < 10:
            mcses = self.getMCSes(C, [], excluded, atLeastOne)
            if mainInstance: printMCSes(mcses)
            return mcses

        C1, C2, B = self.decompose(C, atLeastOne, excluded)
        if C1 == None:
            print("C1 is None")
            mcses = self.getMCSes(C, [], excluded, atLeastOne)
            if mainInstance: printMCSes(mcses)
            return mcses

        if self.debug:
            U = [i for i in range(len(C)) if (i in (C1 + C2 + B) and i not in excluded)]
            U2 = [i for i in range(len(C)) if i not in excluded]
            assert set(U) == set(U2)

        #Get MSSes when art is presented
        artMSSes = self.processComponent(C, atLeastOne + [B], excluded, min(ttl - 1, 0))
        print("artMSSes:", len(artMSSes))

        #Get MSSes in the individual components
        componentsMCSes = []
        excludedC1 = [i for i in range(len(C)) if i not in C1]
        if not checkSAT(C, excludedC1):
            componentsMCSes.append(self.processComponent(C, atLeastOne, excludedC1, ttl = min(0, ttl - 1), mainInstance = False))
            print("C1 MSSes:", len(componentsMCSes[-1]))
        excludedC2 = [i for i in range(len(C)) if i not in C2]
        if not checkSAT(C, excludedC2):
            componentsMCSes.append(self.processComponent(C, atLeastOne, excludedC2, ttl = min(0, ttl - 1), mainInstance = False))
            print("C2 MSSes:", len(componentsMCSes[-1]))


        #combinedMSSes = self.validCombinations2(C, excluded, artMSSes, B, componentsMCSes)
        #print("artMSSes: {}, combinedMSS: {}, total: {}".format(len(artMSSes), len(combinedMSSes), len(artMSSes + combinedMSSes)))
        combinedMSSes = self.validCombinations(C, excluded, artMSSes, B, componentsMCSes)
        print("-- artMSSes: {}, combinedMSS: {}, total: {}".format(len(artMSSes), len(combinedMSSes), len(artMSSes + combinedMSSes)))
        if mainInstance: printMCSes(combinedMSSes)

        if self.debug:
            print("checking {} MCSes".format(len(combinedMSSes)))
            mapaRe = {}
            D = []
            for i in range(len(C)):
                if i not in excluded:
                    mapaRe[i] = len(D)
                    D.append(C[i])
            for mcs in combinedMSSes:
                assert isMCS(D, [mapaRe[i] for i in mcs])        

        if len(combinedMSSes) > 0:
            print("\n\n\n \t\t combined: {}\n\n\n".format(len(combinedMSSes)))


        return artMSSes + combinedMSSes

def tests(args):
    files = {
            "./tests/m1_marco_input_57_100_42_refined.cnf": 40320, #5 sec
            "./tests/m2_marco_input_132_200_9_refined.cnf": 109944, #2 sec
            "./tests/m2_marco_input_159_200_51_refined.cnf": 32256, #1 sec
            "./tests/m1_marco_input_199_200_80_refined.cnf": 2304, #0.4 sec
            }
    for test in files:
        counter = Counter(test)
        counter.MCSEnumerator = "rime"
        counter.ttl = args.ttl
        startTime = time.time()
        assert files[test] == counter.run()
        print("duration", time.time() - startTime)

if __name__ == "__main__":
    parser = argparse.ArgumentParser("MSS counter")
    parser.add_argument("input_file", help = "A path to the input file. Either a .cnf or a .gcnf instance. See ./examples/")
    #parser.add_argument("--MCSEnumerator", help = "MCSEnumeration subroutine. Available options: [mcsls,rime]", default = "mcsls")
    parser.add_argument("--ttl", help = "Maximum recursion depth", type = int, default = 200)
    parser.add_argument("--verbosity", help = "Verbosity level. Set it to 2 to print indices of MCSes.", type = int, default = 1)
    parser.add_argument("--debug", action = 'store_true')
    args = parser.parse_args()

    if args.input_file == "tests":
        tests(args)
    else:
        counter = Counter(args.input_file)
        #counter.MCSEnumerator = args.MCSEnumerator
        counter.MCSEnumerator = "rime" #we do not distribute mcsls
        counter.ttl = args.ttl
        counter.debug = args.debug
        counter.verbosity = args.verbosity
        counter.run()
