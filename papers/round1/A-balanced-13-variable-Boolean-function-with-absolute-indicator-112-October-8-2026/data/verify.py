"""Independent check of the A12 certificate (pure numpy, naive O(4^n) autocorrelation)."""
import sys, numpy as np
hexstr = open(sys.argv[1]).read().strip()
n = 13; N = 1 << n
T = int(hexstr, 16)
f = np.array([(T >> x) & 1 for x in range(N)], dtype=np.int64)
assert T >> N == 0
F = 1 - 2 * f
xs = np.arange(N)
print("weight =", int(f.sum()))
# naive autocorrelation r(d) = sum_x F(x) F(x xor d)
r = np.array([int((F * F[xs ^ d]).sum()) for d in range(N)])
print("r(0) =", r[0], " absolute indicator Delta = max_{d!=0}|r(d)| =", int(np.abs(r[1:]).max()))
vals, cnts = np.unique(np.abs(r[1:]), return_counts=True)
print("distribution of |r(d)|, d != 0:", dict(zip(vals.tolist(), cnts.tolist())))
# Walsh spectrum (naive via FWHT) and nonlinearity
W = F.copy()
h = 1
while h < N:
    W = W.reshape(-1, 2, h); a = W[:, 0, :].copy(); b = W[:, 1, :].copy(); W[:, 0, :] = a + b; W[:, 1, :] = a - b; W = W.reshape(-1); h *= 2
print("max|W| =", int(np.abs(W).max()), " nonlinearity =", (N - int(np.abs(W).max())) // 2)
# ANF and degree
A = f.copy(); h = 1
while h < N:
    A = A.reshape(-1, 2, h); A[:, 1, :] ^= A[:, 0, :]; A = A.reshape(-1); h *= 2
deg = max(bin(int(u)).count('1') for u in np.nonzero(A)[0])
print("algebraic degree =", deg, " ANF coeff of x0x1x2 (u=7):", int(A[7]))
# invariance under the affine group of coordinate permutations i -> a*i+b mod 13
def permute(p):
    img = np.zeros(N, dtype=np.int64)
    for i in range(n): img |= ((xs >> i) & 1) << p[i]
    return img
ok = all(np.array_equal(f[permute([(a * i + b) % n for i in range(n)])], f) for a in range(1, 13) for b in range(13))
print("invariant under x_i -> x_{a i + b mod 13} for all a != 0, b:", ok)
