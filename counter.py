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

    def run(self):
        decomposer = Decomposer(self.Call, [])
        components = decomposer.sccs()
        print("components:", len(components))
        print("components sizes: ", " ".join([str(len(c[0])) for c in components]))

        nontrivialComponents = 0
        counts = []
        for component in components:
            Cids,_ = component
            C = [self.Call[i] for i in Cids]

            if len(C) == 1: continue #there is only one clause in that component, i.e., the clause is an MSS
            s = Solver(name = "g4")
            for cl in C:
                s.add_clause(cl)
            if s.solve(): continue #the whole component is satisfiable
            print("component size:", len(C))
            C = [C[i] for i in getAutarky(C)] #autarky trim
            print("autarky size:", len(C))
            nontrivialComponents += 1
            count = len(self.processComponent(C, [], [], [], self.ttl))
            counts.append(count)

        msses = 1
        for count in counts:
            msses *= count
        print(self.filename, "nontrivial Components:", nontrivialComponents, "msses:", msses, "counts:", counts)
        return msses

    def getMCSes(self, C, hard, excluded, atLeastOne, limit = 0):
        H = hard[:]
        S = []
        for s in atLeastOne:
            if len(s) == 1:
                H += s
            else:
                S.append(s)

        auxiliaryHards = []
        for s in S:
            cl = []
            for i in s:
                cl += C[i]
            auxiliaryHards.append(cl)

        if self.MCSEnumerator == "mcsls":
            return mcsls(C, H, excluded, limit, auxiliaryHards)
        elif self.MCSEnumerator == "rime":
            return rime(C, H, excluded, limit, auxiliaryHards)
        assert False #self.MCSEnumerator should be either rime or mcsls

    def verifyDecomposition(self, C, components):
        c1, c2 = components[:2]
        print(c1, c2)
        for cid in c1:
            for l in C[cid]:
                for cid2 in c2:
                    assert not -l in C[cid2]

    #checkpoint
    #return MSSes that are not subsets of artMSSes
    def validCombinations2(self, C, excluded, artMCSes, cut, componentsMCSes, components):
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
            assert checkSAT([C[i] for i in range(len(C)) if i not in (mcs + cut)], excluded)
            if isValid(mcs):
                combinedMSSes.append(mcs + cut)
        return combinedMSSes

    def validCombinations(self, C, excluded, artMSSes, art, componentsMCSes, components, hard = []):
        s = Solver(name = "g4")
        maxVariable = 0
        for clause in C:
            maxVariable = max(maxVariable, max([abs(l) for l in clause]))
        activators = [x + maxVariable + 1 for x in range(len(C))]
        for i in range(len(C)):
            if i in hard:
                s.add_clause(C[i])
            elif i in art:
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

        #print("all combs:", len(allCombinations))
        combinedMSSes = []
        for mcs in allCombinations:
            assumptions = [-activators[i] for i in range(len(C)) if i not in (mcs + excluded)]
            if not s.solve(assumptions):
                combinedMSSes.append(mcs + art) #art is not part of the MSSes, hence, we need to add it to the MCSes

        return combinedMSSes

    def pickArt(self, arts, C, excluded):
        options = []
        for art in arts:
            options.append((art, Decomposer(C, []).sccs(excluded + [art])))
        #sort primary by the number of components (given by the art) and secondary by the median size of the components
        #primarily at least two components, and secondary sorty by the median siez of the components
        sortedOptions = sorted(options, key = lambda components: min(20000,(10000 * len(components[1]))) + median([len(i[0]) for i in components[1]]), reverse = True)
        return sortedOptions[0]

    def reduceCut(self, C, Cs, Cclauses, Bclauses):
        B = []
        for bid in Bclauses:
            connected = []
            for i in range(len(Cs)):
                isConnected = False
                for cid in Cs[i]:
                    for l in C[cid]:
                        if -l in C[bid]:
                            isConnected = True
                            break
                    if isConnected: break
                if isConnected: connected.append(i)
            B.append(connected[:]) #ids components, not ids of clauses
            assert len(B[-1]) > 0

        #TODO: find at least two b1 b2 such that B[b1][0] cap B[b2][0] == {} and then form C1 and C2 as:
        #C1 = B[b1][0] + [b1], C2 = B[b2][0] + [b2]
        C1, C2 = None, None
        for i in range(len(B)):
            for j in range(i+1, len(B)):
                if set(B[i]).isdisjoint(B[j]):
                    C1, C2 = i, j
                    print("\n\n\n----extension!\n\n\n")
                    break
            if C1 != None: break
        if C1 == None: return None, None, None
        Bassignment = [-1 for _ in B]
        Bassignment[C1], Bassignment[C2] = 1, 2
        C1groups, C2groups = B[C1], B[C2]
        assert min(len(C1groups), len(C2groups)) > 0

        for i in range(len(B)):
            if i in [C1, C2]: continue
            if set(B[i]).isdisjoint(C1groups) and not set(B[i]).isdisjoint(C2groups):
                Bassignment[i] = 2
                C2groups += B[i]
            if set(B[i]).isdisjoint(C2groups) and not set(B[i]).isdisjoint(C1groups):
                Bassignment[i] = 1
                C1groups += B[i]
        return C1groups, C2groups, [B[i] for i in range(len(B)) if Bassignment == -1]

    def decomposeViaCut(self, C, hard, atLeastOne, excluded):
        decomposition = None         
        for mcs in self.getMCSes(C, hard, excluded, atLeastOne, limit = 500):
            mssC = [C[i] for i in range(len(C)) if i not in mcs]
            decomposer = Decomposer(mssC, [])
            components = decomposer.sccs()
            print("---Cs:", len(components), "B:", len(C) - len(mssC), len(hard))
            if len(components) > 1:
                decomposition = components
                Cs = [component[0] for component in decomposition]
                Cclauses = [cid for component in Cs for cid in component]
                Bclauses = [cid for cid in range(len(C)) if (cid not in Cclauses and cid not in excluded and cid not in hard)]
                C1groups, C2groups, B = self.reduceCut(C, Cs, Cclauses, Bclauses)
                print("after reduce cut")
                #break
        if not decomposition: return None, None #failed to decompose

    def decomposeViaMSSes(self, C, hard, excluded):
        mapa = []
        for i in range(len(C)):
            if i not in excluded:
                mapa.append(i)
        decomposer = MSSDecomposer(C = [C[i] for i in range(len(C)) if i not in excluded])
        decompositions = decomposer.run()
        if len(decompositions) == 0: return None, None
        decomposition = decompositions[0] #for now, we just pick one of the identified decompositions
        decomposition[0] = [mapa[cid] for cid in decomposition[0]]
        decomposition[1] = [mapa[cid] for cid in decomposition[1]]

        components = [[decomposition[0], []], [decomposition[1], []]]
        cut = [i for i in range(len(C)) if i not in (decomposition[0] + decomposition[1] + excluded)] #the "cut" clauses
        if len(cut) == 0: return None, None
        print(len(cut))
        self.verifyDecomposition(C, [decomposition[0], decomposition[1]])
        print("verified")
        return components, cut

    def decomposeViaArticulationPoint(self, C, hard, excluded):
        decomposer = Decomposer(C, [])
        arts = [art for art in decomposer.articulationPointsIter() if art not in hard]
        if len(arts) == 0: return None, None #failed to decompose
        art, components = self.pickArt(arts, C, excluded)
        if len(components) == 1: return None, None #failed to decompose
        return components, [[art]]

    def decompose(self, C, hard, atLeastOne, excluded):
        if self.decompositionTechnique == "mss":
            return self.decomposeViaMSSes(C, hard, excluded)
        #if self.decompositionTechnique = "cut":
        #    return self.decomposeViaCut(C, hard, atLeastOne, excluded)
        return self.decomposeViaArticulationPoint(C, hard + atLeastOne, excluded)

    def processComponent(self, C, hard, atLeastOne, excluded, ttl = 1, mainInstance = True):
        if ttl == 0:
            mcses = self.getMCSes(C, hard, excluded, atLeastOne)
            if mainInstance: printMCSes(mcses)
            return mcses

        components, cut = self.decompose(C, hard, excluded, atLeastOne)
        if not components:
            mcses = self.getMCSes(C, hard, excluded, atLeastOne)
            if mainInstance: printMCSes(mcses)
            return mcses

        #Get MSSes when art is presented
        artMSSes = self.processComponent(C, hard, atLeastOne + [cut], excluded, min(ttl - 1, 1))

        #Get MSSes in the individual components
        componentsMCSes = []
        Cid = 0
        for component in components:
            Cid += 1
            soft,_ = component
            excludedRec = [i for i in range(len(C)) if i not in soft]

            #only unsatisfiable components participate on the MCSes
            if not checkSAT(C, excludedRec):
                componentsMCSes.append(self.processComponent(C, hard, atLeastOne, excludedRec, ttl = min(0, ttl - 1), mainInstance = False))
        combinedMSSes = self.validCombinations(C, excluded, artMSSes, cut, componentsMCSes, components)
        print("artMSSes: {}, combinedMSS: {}, total: {}".format(len(artMSSes), len(combinedMSSes), len(artMSSes + combinedMSSes)))
        combinedMSSes = self.validCombinations2(C, excluded, artMSSes, cut, componentsMCSes, components)
        print("-- artMSSes: {}, combinedMSS: {}, total: {}".format(len(artMSSes), len(combinedMSSes), len(artMSSes + combinedMSSes)))
        if mainInstance: printMCSes(combinedMSSes)

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
        counter.MCSEnumerator = args.MCSEnumerator
        counter.decompositionTechnique = args.decomposer
        counter.ttl = args.ttl
        startTime = time.time()
        assert files[test] == counter.run()
        print("duration", time.time() - startTime)

if __name__ == "__main__":
    parser = argparse.ArgumentParser("MSS counter")
    parser.add_argument("input_file", help = "A path to the input file. Either a .cnf or a .gcnf instance. See ./examples/")
    parser.add_argument("--MCSEnumerator", help = "MCSEnumeration subroutine. Available options: [mcsls,rime]", default = "mcsls")
    parser.add_argument("--decomposer", help = "Decomposition technique. Available options: [ap,mss]", default = "ap")
    parser.add_argument("--ttl", help = "Maximum recursion depth", type = int, default = 200)
    args = parser.parse_args()

    if args.input_file == "tests":
        tests(args)
    else:
        counter = Counter(args.input_file)
        counter.MCSEnumerator = args.MCSEnumerator
        counter.decompositionTechnique = args.decomposer
        counter.ttl = args.ttl
        counter.run()
