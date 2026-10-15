"""Utilities for matrix multiplication schemes <n,m,p>.

Convention (Perminov style): A is n x m, B is m x p, C = A B is n x p.
A scheme of rank r is given by lists U (r x nm), V (r x mp), W (r x np) such that
   C[i,k] = sum_r W[r][i*p+k] * (sum_ij U[r][i*m+j] A[i,j]) * (sum V[r][j*p+k] B[j,k])
equivalently the Brent equations
   sum_r U[r][a] V[r][b] W[r][c] = T[a,b,c],
   T[(i,j),(j',k),(i',k')] = [j==j'][i==i'][k==k'].
"""
import json, re, itertools
from fractions import Fraction
import numpy as np


def mm_tensor(n, m, p):
    T = np.zeros((n * m, m * p, n * p), dtype=np.int64)
    for i in range(n):
        for j in range(m):
            for k in range(p):
                T[i * m + j, j * p + k, i * p + k] = 1
    return T


def scheme_tensor(U, V, W):
    """exact (object/Fraction or int) tensor sum_r U_r x V_r x W_r"""
    U = np.array(U, dtype=object); V = np.array(V, dtype=object); W = np.array(W, dtype=object)
    r = U.shape[0]
    T = np.zeros((U.shape[1], V.shape[1], W.shape[1]), dtype=object)
    for t in range(r):
        T = T + np.multiply.outer(np.multiply.outer(U[t], V[t]), W[t])
    return T


def verify(n, m, p, U, V, W):
    T = scheme_tensor(U, V, W)
    D = T - mm_tensor(n, m, p).astype(object)
    return all(x == 0 for x in D.flat)


def verify_mod(n, m, p, U, V, W, q):
    U = np.array(U, dtype=np.int64) % q; V = np.array(V, dtype=np.int64) % q; W = np.array(W, dtype=np.int64) % q
    T = np.einsum('ra,rb,rc->abc', U, V, W) % q
    return np.array_equal(T, mm_tensor(n, m, p) % q)


def wT_to_w(w, n, p):
    # Perminov / catalogue store C-coefficients as p x n (C transposed), row-major
    return [w[k * n + i] for i in range(n) for k in range(p)]


def w_to_wT(w, n, p):
    return [w[i * p + k] for k in range(p) for i in range(n)]


def load_perminov_json(path):
    d = json.load(open(path))
    n, m, p = d['n']
    def conv(x):
        if isinstance(x, str):
            return Fraction(x)
        return Fraction(x)
    U = [[conv(x) for x in row] for row in d['u']]
    V = [[conv(x) for x in row] for row in d['v']]
    W = [[conv(x) for x in row] for row in d['w']]
    W = [wT_to_w(w, n, p) for w in W]
    return n, m, p, U, V, W


def load_txt(path):
    """Perminov txt single scheme format: 'n m p r' then U, V, W lines (flattened per term)."""
    toks = open(path).read().split()
    n, m, p, r = map(int, toks[:4])
    vals = list(map(int, toks[4:]))
    a, b, c = n * m, m * p, n * p
    U = [vals[t * a:(t + 1) * a] for t in range(r)]
    off = r * a
    V = [vals[off + t * b: off + (t + 1) * b] for t in range(r)]
    off += r * b
    W = [vals[off + t * c: off + (t + 1) * c] for t in range(r)]
    W = [wT_to_w(w, n, p) for w in W]
    return n, m, p, U, V, W


def save_txt(path, n, m, p, U, V, W):
    with open(path, 'w') as f:
        f.write(f"{n} {m} {p} {len(U)}\n")
        WT = [w_to_wT(w, n, p) for w in W]
        for M in (U, V, WT):
            f.write(' '.join(str(int(x)) for row in M for x in row) + '\n')


_num = r'-?\d+(?:/\d+)?'

def _parse_matrix(s):
    m = re.match(r'Matrix\((\d+),\s*(\d+),\s*\[(.*)\]\)$', s.strip(), re.S)
    rows, cols = int(m.group(1)), int(m.group(2))
    body = m.group(3)
    rws = re.findall(r'\[([^\[\]]*)\]', body)
    M = [[Fraction(x.strip()) for x in rw.split(',')] for rw in rws]
    assert len(M) == rows and all(len(r) == cols for r in M)
    return M


def load_maple_triads(path):
    """FMM catalogue maple tensor file -> list of (X, Y, Z) matrices (Fractions)."""
    s = open(path).read()
    triads = re.findall(r'Triad\(\[(Matrix\(.*?\]\]\)),\s*(Matrix\(.*?\]\]\)),\s*(Matrix\(.*?\]\]\))\]\)', s, re.S)
    out = []
    for t in triads:
        out.append(tuple(_parse_matrix(x) for x in t))
    return out


def triads_to_scheme(triads, n, m, p):
    """Try to find the convention mapping catalogue triads to (U,V,W). Returns scheme or None."""
    # candidates: X is n x m (coeff of A), Y is m x p (coeff of B), Z is p x n (coeff of C^T) or n x p
    cands = []
    for transX in (False, True):
        for transY in (False, True):
            for transZ in (False, True):
                U = []; V = []; W = []
                ok = True
                for X, Y, Z in triads:
                    Xm = np.array(X, dtype=object); Ym = np.array(Y, dtype=object); Zm = np.array(Z, dtype=object)
                    if transX: Xm = Xm.T
                    if transY: Ym = Ym.T
                    if transZ: Zm = Zm.T
                    if Xm.shape != (n, m) or Ym.shape != (m, p) or Zm.shape != (n, p):
                        ok = False; break
                    U.append(list(Xm.flatten())); V.append(list(Ym.flatten())); W.append(list(Zm.flatten()))
                if ok and verify(n, m, p, U, V, W):
                    return U, V, W, (transX, transY, transZ)
    return None


def denominators(M):
    ds = set()
    for row in M:
        for x in row:
            ds.add(Fraction(x).denominator)
    return ds


if __name__ == '__main__':
    import sys
    pass
