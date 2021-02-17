from collections import defaultdict
import sys
sys.setrecursionlimit(10000)

class Decomposer:
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

    def sccDFS(self, visitedC, visitedB, Ci, Bi, component, depth = 0):
        assert min(Ci, Bi) < 0 and max(Ci, Bi) >= 0
        if Ci >= 0 and not visitedC[Ci]:
            visitedC[Ci] = True
            self.sccC[Ci] = component
            for l in self.C[Ci]:
                for d in self.hitmapC[-l]: #clauses that contain the negated literal (offset +1!)
                    if not visitedC[d - 1]:
                        self.sccDFS(visitedC, visitedB, d - 1, -1, component, depth + 1)
                for d in self.hitmapB[-l]: #clauses that contain the negated literal (offset +1!)
                    if not visitedB[d - 1]:
                        self.sccDFS(visitedC, visitedB, -1, d - 1, component)
        if Bi >= 0 and not visitedB[Bi]:
            visitedB[Bi] = True
            self.sccB[Bi] = component
            for l in self.B[Bi]:
                for d in self.hitmapC[-l]: #clauses that contain the negated literal (offset +1!)
                    self.sccDFS(visitedC, visitedB, d - 1, -1, component)
                for d in self.hitmapB[-l]: #clauses that contain the negated literal (no offset here!)
                    self.sccDFS(visitedC, visitedB, -1, d, component)

    def sccs(self, art = []):
        visitedC = [False for _ in range(len(self.C))]
        visitedB = [False for _ in range(len(self.B))]
        self.sccC = [-1 for _ in range(len(self.C))]
        self.sccB = [-1 for _ in range(len(self.B))]

        for i in art:
            visitedC[i] = True

        component = 0
        for i in range(len(self.C)):
            if visitedC[i]: continue
            component += 1
            self.sccDFS(visitedC, visitedB, i, -1, component)
        for i in range(len(self.B)):
            if visitedB[i]: continue
            component += 1
            self.sccDFS(visitedC, visitedB, -1, i, component)
        components = [[[],[]] for _ in range(component)]
        for i in range(len(self.C)):
            if i in art: continue
            components[self.sccC[i] - 1][0].append(i)
        for i in range(len(self.B)):
            components[self.sccB[i] - 1][1].append(i)
       
        return components       

    #implemented based on https://leetcode.com/problems/critical-connections-in-a-network/discuss/504797/Python-Find-bridgesarticulation-points-with-detailed-explanation
    def articulationPoints(self):
        assert len(self.B) == 0

        visited = set()
        art = set()
        parents = {}
        low = {}

        def dfs(nid, Ci, parent):
            visited.add(Ci)
            parents[Ci] = parent
            edges = 0
            low[Ci] = nid

            for l in self.C[Ci]:
                for nei in self.hitmapC[-l]: #clauses that contain the negated literal (offset +1!)
                    nei -= 1 #fix the +1 offset
                    if nei == parent:
                        continue
                    if nei not in visited:
                        edges += 1
                        dfs(nid + 1, nei, Ci)
                    low[Ci] = min(low[Ci], low[nei])

                    if nid <= low[nei]:
                        if parents[Ci] != -1:
                            art.add(Ci)

            if parents[Ci] == -1 and edges >= 2:
                art.add(Ci)

        dfs(0,0,-1)
        return art
