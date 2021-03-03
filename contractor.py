from collections import defaultdict
from collections import deque
import random
from random import randint
import sys
import subprocess as sp
import networkx as nx
sys.setrecursionlimit(10000)


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

class Contractor:
    def __init__(self, C, B):
        self.C = C
        self.B = B
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

    def disjointMUSes(self):
        assert len(self.B) == 0
        filename = "./tmp/disjoint_" + str(randint(1,10000000)) + ".cnf"
        exportCNF(self.C, filename)
        cmd = "timeout 60 ./unimus_disjoint -a marco {}".format(filename)
        print(cmd)
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

    def contractEdge(self, edge):
        if "m1" in edge and "m2" in edge: return #these are the main vertices
        if "m1" == edge[1] or "m2" == edge[1]:
            edge = (edge[1], edge[0]) #the first vertex is kept, i.e., we always preserve the two main vertices

        # merge v2 into v1 and remove v2 from graph
        v1l = self.g[edge[0]]
        v1l.extend(self.g[edge[1]])
        del self.g[edge[1]]

        #replace all occurnces of v2 value with v1
        for k in self.g:
            self.g[k] = [edge[0] if x == edge[1] else x for x in self.g[k]]

        # Remove all edges of v1 to itself(loops)
        self.g[edge[0]] = [x for x in self.g[edge[0]] if x != edge[0]]

    # Gets a random edge available in the current graph
    def getRandomEdge(self):        
        v2 = list(set(self.g.keys()) - set(["m1", "m2"])) [random.randint(0,len(self.g)-1)]        
        v1 = self.g[v2] [random.randint(0,len(self.g[v2])-1)]
        return (v1,v2) 
    
    def buildNXGraph(self):
        m1, m2 = self.disjointMUSes()
        if min(len(m1), len(m2)) == 0:
            print("failed to find disjoint MUSes")
            return None
        print("m1 size: {}, m2 size: {}".format(len(m1), len(m2)))
        self.nxG = nx.DiGraph()
        for cl in m1:
            for l in self.C[cl]:
                for nei in self.hitmapC[-l]:
                    if nei - 1 in m1: continue
                    self.nxG.add_edge("m1", str(nei) + "in", capacity=2)
        for cl in m2:
            for l in self.C[cl]:
                for nei in self.hitmapC[-l]:
                    if nei - 1 in m2: continue
                    self.nxG.add_edge("m2", str(nei) + "in", capacity=2)
        for i in range(len(C)):
            if i in m1 + m2: continue
            edges = False
            for l in self.C[i]:
                for nei in self.hitmapC[-l]:                    
                    edges = True
                    if (nei - 1) in m1:
                        self.nxG.add_edge(str(i + 1) + "out", "m1", capacity=2)
                    elif (nei - 1) in m2:
                        self.nxG.add_edge(str(i + 1) + "out", "m2", capacity=2)
                    else:
                        self.nxG.add_edge(str(i + 1) + "out", str(nei) + "in", capacity=2)
            if edges:
                self.nxG.add_edge(str(i + i) + "in", str(i + 1) + "out", capacity=1)
        print("nodes: {}, edges: {}".format(len(self.nxG.nodes), len(self.nxG.edges)))
        return True

    def buildGraph(self):
        m1, m2 = self.disjointMUSes()
        if min(len(m1), len(m2)) == 0:
            print("failed to find disjoint MUSes")
            return None
        print("m1 size: {}, m2 size: {}".format(len(m1), len(m2)))
        self.g = {}
        self.g["m1"] = [] #M1 vertex
        self.g["m2"] = [] #M2 vertex
        for cl in m1:
            for l in self.C[cl]:
                for nei in self.hitmapC[-l]:
                    self.g["m1"].append(nei)
        for cl in m2:
            for l in self.C[cl]:
                for nei in self.hitmapC[-l]:
                    self.g["m2"].append(nei)
        for i in range(len(C)):
            if i in m1 + m2: continue
            self.g[i + 1] = []
            for l in self.C[i]:
                for nei in self.hitmapC[-l]:
                    if (nei - 1) in m1:
                        self.g[i + 1].append("m1")
                    elif (nei - 1) in m2:
                        self.g[i + 1].append("m2")
                    else:
                        self.g[i + 1].append(nei)
            if len(self.g[i + 1]) == 0:
                del self.g[i + 1]
        self.originalG = dict(self.g)
        return True

    def vertexCutMUS(self):
        self.buildGraph()
        minlist = []
        # Repeat 20 times to get a minimum
        for i in range(0,20):
            self.g = dict(self.originalG)
            # Keep contracting the graph until we have 2 vertices
            while(len(self.g) > 2):
                self.contractEdge(self.getRandomEdge())
                if len(self.g) % 10 == 0:
                    print(len(self.g))
            minlist.append(len(self.g[list(self.g.keys())[0]]))
            print(minlist)
        print("minimum out of 20 rounds:", min(minlist))

import sys
import argparse
if __name__ == "__main__":
    parser = argparse.ArgumentParser("MSS counter")
    parser.add_argument("input_file", help = "A path to the input file. Either a .cnf or a .gcnf instance. See ./examples/")
    args = parser.parse_args()

    C,B = parse(args.input_file)
    cont = Contractor(C,B)
    cont.buildNXGraph()
    print("initialized")
    cut_value, partition = nx.minimum_cut(cont.nxG, "m1", "m2")
    part1, part2 = partition
    print("cut value", cut_value)
    print("partition", len(part1), len(part2))

    #TODO: create lists of clauses based on the two components. Note that node m1 corresponds to self.m1 and node m2 corresponds to self.m2
    part1Clauses = []
    for v in part1:

    part2Clauses = []












