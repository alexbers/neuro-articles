# Second, independent exact checker: int64 Gram blocks (exact while |entries| < 2^28 and dim 20),
# then exact Python-integer comparison 4<x,y>^2 <= |x|^2 |y|^2 for every pair with <x,y> > 0.
import numpy as np, sys
rows = [list(map(int, l.split())) for l in open(sys.argv[1]) if l.strip()]
X = np.array(rows, dtype=np.int64)
assert np.abs(X).max() < 2 ** 28
n = len(X)
N2 = [int(x) for x in (X * X).sum(1)]
assert min(N2) > 0
bad = 0; checked = 0; touching = 0
for s in range(0, n, 1024):
    G = X[s:s + 1024] @ X.T                     # exact int64
    for a in range(G.shape[0]):
        i = s + a
        row = G[a]
        js = np.nonzero(row[i + 1:] > 0)[0] + i + 1
        for j in js:
            d = int(row[j]); checked += 1
            lhs = 4 * d * d; rhs = N2[i] * N2[j]
            if lhs > rhs: bad += 1
            elif lhs == rhs: touching += 1
print(f'points {n}, positive-inner-product pairs checked exactly: {checked}, violations: {bad}, touching pairs: {touching}')
print('distinct rows:', len(set(map(tuple, rows))) == n)
