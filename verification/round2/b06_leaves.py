# Coordinator's check of B06 using only the leaf ENDPOINTS from the agent; the polynomial P is rebuilt
# independently from gamma (own Laguerre recurrence), and every leaf transform T is computed by own code.
import sys
from fractions import Fraction as Fr
gam = [int(l) for l in open(sys.argv[1]) if l.strip()]
D = 2 * (len(gam) - 1)
L = [[1], [1, -2]]
for n in range(1, D):
    a, b = L[n], L[n - 1]; c = [0] * (n + 2)
    for k, x in enumerate(a): c[k] += (4*n + 1) * x; c[k + 1] -= 2 * x
    for k, x in enumerate(b): c[k] -= 2*n*(2*n - 1) * x
    L.append(c)
P = [0] * (D + 1)
for j, g in enumerate(gam):
    for k, x in enumerate(L[2*j]): P[k] += g * x
print("P(0) < 0:", P[0] < 0, "| leading > 0:", P[-1] > 0)
leaves = [tuple(map(int, l.split())) for l in open(sys.argv[2]) if l.strip()]
def mul_lin(p, a0, a1):                     # p(z) * (a0 + a1 z)
    r = [0] * (len(p) + 1)
    for k, x in enumerate(p): r[k] += a0 * x; r[k + 1] += a1 * x
    return r
ok = True
iv = []
for (u0, u1, v0, v1) in leaves:
    # T(z) = sum_i P_i (u0+u1 z)^i (v0+v1 z)^(D-i), homogeneous Horner
    H = [P[D]]; Bp = [1]
    for k in range(D - 1, -1, -1):
        H = mul_lin(H, u0, u1)
        Bp = mul_lin(Bp, v0, v1)            # Bp = (v0+v1 z)^(D-k)
        H = [h + (P[k] * Bp[t] if t < len(Bp) else 0) for t, h in enumerate(H + [0] * (len(Bp) - len(H)))] if len(Bp) > len(H) else [h + (P[k] * Bp[t] if t < len(Bp) else 0) for t, h in enumerate(H)]
    good = all(x >= 0 for x in H) and H[0] > 0
    ok &= good
    lo = Fr(u0, v0); hi = Fr(u1, v1) if v1 else None
    iv.append((lo, hi, good))
iv.sort(key=lambda t: t[0])
cover = iv[0][0] == Fr(48, 25) and iv[-1][1] is None and all(iv[i][1] == iv[i + 1][0] for i in range(len(iv) - 1))
print("leaves:", len(iv), "| all leaf transforms have nonneg coeffs and T(0)>0:", ok, "| leaves tile [48/25, oo) contiguously:", cover)
