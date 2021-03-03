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
        cmd = "timeout 300 ./unimus_disjoint -a marco {}".format(filename)
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

    def maxNode(self):
        maximum = 0
        for node in self.nxG.nodes:
            if "in" in node:
                maximum = max(maximum, int(node[:-2]))
            if "out" in node:
                maximum = max(maximum, int(node[:-3]))
        return maximum

    def buildNXGraph(self):
        m1, m2 = self.disjointMUSes()
        self.m1, self.m2 = m1, m2
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
        for i in range(len(self.C)):
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
                self.nxG.add_edge(str(i + 1) + "in", str(i + 1) + "out", capacity=1)
        print("nodes: {}, edges: {}".format(len(self.nxG.nodes), len(self.nxG.edges)))
        return True

    def partition(self):
        cont.buildNXGraph()
        if min(len(self.m1), len(self.m2)) == 0:
            return None #failed to find disjoing MUSes
        print("initialized")
        cut_value, partition = nx.minimum_cut(self.nxG, "m1", "m2")
        part1, part2 = partition
        print("cut value", cut_value)
        print("partition", len(part1), len(part2))

        #TODO: create lists of clauses based on the two components. Note that node m1 corresponds to self.m1 and node m2 corresponds to self.m2
        part1Clauses = set(self.m1)
        part1Border = set()
        for v in part1:
            if "out" in v:
                assert v[:-3] + "in" in part1
                part1Clauses.add(int(v[:-3]) - 1) #fixing +1 offset
            if "in" in v and not v[:-2] + "out" in part1:
                part1Border.add(int(v[:-2]) - 1) #fixing +1 offset

        part2Clauses = set(self.m2)
        part2Border = set()
        for v in part2:
            if "in" in v:
                part2Clauses.add(int(v[:-2]) - 1) #fixing +1 offset
                assert v[:-2] + "out" in part2
            if "out" in v and not v[:-3] + "in" in part2:
                part2Border.add(int(v[:-3]) - 1) #fixing +1 offset

        assert len(part1Border) == len(part2Border) == cut_value
        border = part1Border
        missing = set([i for i in range(len(C))]) - (part1Clauses.union(part2Clauses,border)) #these are not connected to the flip graph and hence can be added to either component
        for m in missing:
            part1Clauses.add(m)

        assert len(C) == len(part1Clauses) + len(part2Clauses) + len(border)
        return part1Clauses, part2Clauses, border

import sys
import argparse
if __name__ == "__main__":
    parser = argparse.ArgumentParser("MSS counter")
    parser.add_argument("input_file", help = "A path to the input file. Either a .cnf or a .gcnf instance. See ./examples/")
    args = parser.parse_args()
    C,B = parse(args.input_file)
    cont = Contractor(C,B)
    part = cont.partition()
