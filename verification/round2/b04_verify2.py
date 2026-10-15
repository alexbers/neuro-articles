# Coordinator's independent check (fixed): exact integer test 4<x,y>^2 <= |x|^2|y|^2 for every pair with <x,y> > 0,
# done in Python big ints for all pairs whose float cosine is within 1e-6 of 1/2 or above; float for the rest.
import sys, numpy as np
X = np.loadtxt(sys.argv[1], dtype=np.int64)
n = X.shape[0]
Xl = [list(map(int, r)) for r in X.tolist()]
Nint = [sum(v*v for v in r) for r in Xl]
Nf = np.array(Nint, dtype=np.float64)
assert len({tuple(r) for r in Xl}) == n and all(Nint), "duplicate or zero vector"
# hyperplane: find integer normal via null space of X (rank 19)
_, s, vt = np.linalg.svd(X.astype(float), full_matrices=False)
print("vectors", n, "singular values (last 2):", s[-2:])
cand = 0; bad = 0; maxcos = -2.0
B = 1000
for i in range(0, n, B):
    G = X[i:i+B] @ X.T                                  # exact: |G| <= 20*(6.1e7)^2 < 9.2e18
    c = G.astype(np.float64) / np.sqrt(Nf[i:i+B][:, None] * Nf[None, :])
    for k in range(G.shape[0]): c[k, i+k] = -2.0
    maxcos = max(maxcos, float(c.max()))
    ks, js = np.nonzero(c > 0.5 - 1e-6)
    for k, j in zip(ks.tolist(), js.tolist()):
        if j <= i + k: continue                         # each unordered pair once
        cand += 1
        g = int(G[k, j])
        if g > 0 and 4*g*g > Nint[i+k]*Nint[j]: bad += 1
print("pairs needing exact check:", cand, "| exact violations:", bad, "| max float cos:", maxcos)
