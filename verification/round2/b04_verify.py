# Coordinator's independent check of the tau_19 >= 12277 certificate (exact integer arithmetic):
# vectors in Z^20, all in one hyperplane (rank <= 19), distinct, nonzero, pairwise angle >= 60 deg:
# for every pair, <x,y> <= 0 or 4<x,y>^2 <= |x|^2 |y|^2.
import sys, numpy as np
X = np.loadtxt(sys.argv[1], dtype=np.int64)
n, d = X.shape
print("vectors", n, "dim", d, "max|coord|", int(np.abs(X).max()))
assert len({tuple(r) for r in X.tolist()}) == n, "duplicates"
assert np.all(np.any(X != 0, axis=1)), "zero vector"
rk = np.linalg.matrix_rank(X.astype(float))
print("rank of span:", rk, "| row sums distinct values:", sorted(set(X.sum(axis=1).tolist()))[:5])
N = (X * X).sum(axis=1)
bad = 0; worst = -1.0
B = 1500
for i in range(0, n, B):
    G = X[i:i+B] @ X.T                       # exact int64 (entries small)
    Ni = N[i:i+B][:, None]
    lhs = 4 * G.astype(object) * G.astype(object) if G.max() > 2**30 else 4 * G * G
    rhs = Ni * N[None, :]
    viol = (G > 0) & (lhs > rhs)
    for k in range(G.shape[0]):                # exclude the diagonal
        if i + k < n: viol[k, i + k] = False
    bad += int(viol.sum())
    c = G / np.sqrt(Ni * N[None, :])
    for k in range(G.shape[0]): c[k, i + k] = -1
    worst = max(worst, float(c.max()))
print("violating pairs:", bad, "| max cos over distinct pairs:", worst)
