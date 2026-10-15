# Independent verification: parse a propus family, build the 4v x 4v propus matrix, check H = H^T and H H^T = 4v I.
import sys, numpy as np
def parse(fn, idx=0):
    sols = []; cur = {}
    for line in open(fn):
        if line.startswith("SOLUTION"):
            cur = {"hdr": line.strip()}; sols.append(cur)
        elif ":" in line:
            k, vals = line.split(":", 1); cur[k.strip()] = [int(t) for t in vals.split()]
    return sols[idx]
def verify(v, X1, X2, X4):
    seq = lambda X: np.array([-1 if i in set(X) else 1 for i in range(v)])
    a, b, d = seq(X1), seq(X2), seq(X4)
    assert all(a[i] == a[(-i) % v] for i in range(v)), "X1 not symmetric"
    paf = lambda x, s: int(np.dot(x, np.roll(x, -s)))
    for s in range(1, v):
        assert paf(a, s) + 2 * paf(b, s) + paf(d, s) == 0, ("PAF fails at", s)
    I = np.arange(v)
    circ = lambda x: x[(I[None, :] - I[:, None]) % v]          # A(i,k) = x(k-i)
    AR = lambda x: x[(-I[:, None] - I[None, :]) % v]            # (AR)(i,k) = x(-i-k)
    RA = lambda x: x[(I[:, None] + I[None, :]) % v]             # (RA)(i,k) = x(i+k)
    H = np.block([[-circ(a), AR(b), AR(b), AR(d)],
                  [AR(b), RA(d), circ(a), -RA(b)],
                  [AR(b), circ(a), -RA(d), RA(b)],
                  [AR(d), -RA(b), RA(b), circ(a)]])
    assert set(np.unique(H)) <= {-1, 1}
    assert (H == H.T).all(), "not symmetric"
    G = H.astype(np.int64) @ H.T.astype(np.int64)
    assert (G == 4 * v * np.eye(4 * v, dtype=np.int64)).all(), "not Hadamard"
    return H
if __name__ == "__main__":
    fn = sys.argv[1]; idx = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    s = parse(fn, idx); v = int(s["hdr"].split("v=")[1].split()[0])
    X1, X2, X4 = s["X1(sym)"], s["X2=X3"], s["X4"]
    print("v =", v, "|X1|,|X2|,|X4| =", len(X1), len(X2), len(X4), "lambda =", len(X1) + 2 * len(X2) + len(X4) - v)
    H = verify(v, X1, X2, X4)
    print("VERIFIED: symmetric Hadamard matrix of order", 4 * v)
    if len(sys.argv) > 3:
        np.savetxt(sys.argv[3], H, fmt="%d", delimiter=" ")
