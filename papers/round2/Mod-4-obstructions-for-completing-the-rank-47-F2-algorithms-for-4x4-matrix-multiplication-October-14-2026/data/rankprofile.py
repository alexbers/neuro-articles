"""Invariants of an F2 scheme of <4,4,4> under the symmetry group of T (sandwiching, transposition, cyclic
mode permutation): per-mode distribution of the F2-ranks of the 4x4 factor matrices, and the number of
available flips (pairs of terms sharing a factor).  usage: python rankprofile.py scheme.txt ..."""
import sys
from collections import Counter
import numpy as np
from fmm import load_txt

def rk(v):
    M = (np.array(v).reshape(4, 4) % 2).copy(); r = 0
    for c in range(4):
        piv = [i for i in range(r, 4) if M[i, c]]
        if not piv: continue
        M[[r, piv[0]]] = M[[piv[0], r]]
        for i in range(4):
            if i != r and M[i, c]: M[i] ^= M[r]
        r += 1
    return r

for f in sys.argv[1:]:
    n, m, p, U, V, W = load_txt(f)
    trip = [(rk(a), rk(b), rk(c)) for a, b, c in zip(U, V, W)]
    dist = [tuple(Counter(t[i] for t in trip).get(k, 0) for k in (1, 2, 3, 4)) for i in range(3)]
    flips = 0
    for mode, F in enumerate((U, V, W)):
        cnt = Counter(tuple(int(x) % 2 for x in row) for row in F)
        flips += sum(c * (c - 1) // 2 for c in cnt.values())
    print(f, 'rank', len(U), 'per-mode rank distributions (1,2,3,4):', dist,
          'sorted:', sorted(dist), 'flip pairs:', flips)
