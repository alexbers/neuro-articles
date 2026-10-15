#!/usr/bin/env python3
"""Independent verifier: build an SL(2,p) (or metacyclic) voltage lift explicitly and compute
degree regularity, simplicity and exact girth by BFS from every vertex (numpy-free, plain python).
usage: verify_lift.py S p resultfile     (resultfile = output of bta2: lines 'edge u v volt k : a b c d')
"""
import sys
from collections import deque

def parse(fn):
    edges = []
    for line in open(fn):
        if line.startswith('edge'):
            left, right = line.split(':')
            t = left.split()
            u, v = int(t[1]), int(t[2])
            mat = tuple(int(x) for x in right.split())
            edges.append((u, v, mat))
    return edges

def main():
    kind, p, fn = sys.argv[1], int(sys.argv[2]), sys.argv[3]
    edges = parse(fn)
    b = 1 + max(max(u, v) for u, v, _ in edges)
    def mul(x, y):
        a, bb, c, d = x; e, f, g, h = y
        return ((a*e + bb*g) % p, (a*f + bb*h) % p, (c*e + d*g) % p, (c*f + d*h) % p)
    def inv(x):
        a, bb, c, d = x
        return (d % p, (-bb) % p, (-c) % p, a % p)
    def det(x):
        return (x[0]*x[3] - x[1]*x[2]) % p
    for _, _, m in edges:
        assert det(m) == 1
    els = [(a, bb, c, d) for a in range(p) for bb in range(p) for c in range(p) for d in range(p)
           if (a*d - bb*c) % p == 1]
    idx = {}
    verts = [(u, m) for u in range(b) for m in els]
    for i, x in enumerate(verts):
        idx[x] = i
    N = len(verts)
    # darts: for each edge (u,v,A): (u,M) -> (v, M A) and (v,M) -> (u, M A^-1)
    darts = {u: [] for u in range(b)}
    for (u, v, A) in edges:
        darts[u].append((v, A))
        darts[v].append((u, inv(A)))
    adj = [None] * N
    for i, (u, m) in enumerate(verts):
        adj[i] = [idx[(w, mul(m, A))] for (w, A) in darts[u]]
    # simple & regular & symmetric
    degs = set(len(a) for a in adj)
    simple = all(len(set(a)) == len(a) and i not in a for i, a in enumerate(adj))
    sym = all(i in adj[j] for i, a in enumerate(adj) for j in a)
    print('N =', N, 'degrees', degs, 'simple', simple, 'symmetric', sym)
    # girth via BFS from every vertex (stop at depth 6)
    girth = 10**9
    for s in range(N):
        dist = {s: 0}; par = {s: -1}
        dq = deque([s])
        while dq:
            x = dq.popleft()
            if 2 * dist[x] + 1 >= girth:
                break
            for y in adj[x]:
                if y == par[x]:
                    continue
                if y in dist:
                    girth = min(girth, dist[x] + dist[y] + 1)
                else:
                    dist[y] = dist[x] + 1; par[y] = x; dq.append(y)
    print('girth =', girth)

if __name__ == '__main__':
    main()
