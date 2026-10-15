# Independent exact all-pairs verifier for a list of integer rays in Z^n.
# A pair x != y is compatible iff <x,y> <= 0 or 4<x,y>^2 <= |x|^2 |y|^2.
# Float64 screening; every pair whose float cosine is within 1e-6 of 1/2 (or above) is re-checked
# with Python integers.  Also checks: no zero vector, no two rays in the same direction.
import numpy as np, sys, time

def load(path):
    rows = []
    for line in open(path):
        line = line.strip()
        if not line or line.startswith('#'): continue
        rows.append([int(t) for t in line.split()])
    return rows

def verify(rows, block=2048):
    n = len(rows); dim = len(rows[0])
    assert all(len(r) == dim for r in rows)
    X = np.array(rows, dtype=np.float64)
    nr2 = [sum(a * a for a in r) for r in rows]
    assert min(nr2) > 0
    U = X / np.sqrt(np.array(nr2, dtype=np.float64))[:, None]
    exact_checks = 0; worst = -2.0; worst_pair = None
    for s in range(0, n, block):
        C = U[s:s + block] @ U.T
        for k in range(C.shape[0]):
            C[k, s + k] = -2.0
        C[:, :0] = -2
        # only pairs j > i
        idx_i, idx_j = np.nonzero(C > 0.5 - 1e-6)
        for a, j in zip(idx_i, idx_j):
            i = s + a
            if j <= i: continue
            exact_checks += 1
            d = sum(p * q for p, q in zip(rows[i], rows[j]))
            if d > 0 and 4 * d * d > nr2[i] * nr2[j]:
                raise AssertionError(f'violation {i} {j}')
            if 4 * d * d == nr2[i] * nr2[j] and d > 0 and nr2[i] == nr2[j] and rows[i] == rows[j]:
                raise AssertionError('duplicate')
        m = np.triu(C, 1).max() if C.size else -2
        if m > worst: worst = m
    return n, exact_checks, worst

if __name__ == '__main__':
    rows = load(sys.argv[1]); t = time.time()
    n, ex, w = verify(rows)
    print(f'points {n}  exact re-checks {ex}  max float cosine {w:.12f}  ALL PAIRS PASS  ({time.time()-t:.0f}s)')
