# Independent check (coordinator): balancedness, ANF degree via Moebius transform,
# autocorrelation via Walsh-Hadamard (r = WHT(W^2)/N), nonlinearity.
import sys, hashlib, numpy as np
s = open(sys.argv[1]).read().strip()
n = 13; N = 1 << n
T = int(s, 16); assert T >> N == 0
f = np.array([(T >> x) & 1 for x in range(N)], dtype=np.int64)
print("sha256(hex) =", hashlib.sha256(s.encode()).hexdigest()[:16], " weight =", int(f.sum()))
# ANF (Moebius transform over GF(2))
a = f.copy()
h = 1
while h < N:
    for i in range(0, N, 2*h):
        a[i+h:i+2*h] ^= a[i:i+h]
    h *= 2
deg = max(bin(u).count("1") for u in range(N) if a[u])
print("algebraic degree =", deg, " #monomials =", int(a.sum()))
def wht(v):
    v = v.astype(np.int64).copy(); h = 1
    while h < N:
        v = v.reshape(-1, 2*h)
        x, y = v[:, :h].copy(), v[:, h:].copy()
        v[:, :h], v[:, h:] = x + y, x - y
        v = v.reshape(-1); h *= 2
    return v
W = wht(1 - 2*f)
r = wht(W*W) // N
assert r[0] == N
print("Delta =", int(np.abs(r[1:]).max()), " nonlinearity =", (N - int(np.abs(W).max()))//2)
# naive spot check of r(d) for 50 random d
rng = np.random.default_rng(1); F = 1 - 2*f; idx = np.arange(N)
for d in rng.integers(1, N, 50):
    assert int((F * F[idx ^ d]).sum()) == r[d]
print("naive spot-check of 50 shifts: OK")
