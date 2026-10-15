# Coordinator's independent check of B06's C_SU certificate:
# build Lambda_n by Lambda_{n+1} = (4n+1-2u)Lambda_n - 2n(2n-1)Lambda_{n-1} (own derivation from the Laguerre recurrence),
# P = sum gamma_j Lambda_{2j}; check P(0) < 0 and that P has no root in [48/25, oo) and is positive there,
# via exact integer polynomial in s with u = (48+s)/25 and Descartes / Vincent-Akritas bisection on s in [0, oo).
import sys, time
gam = [int(l) for l in open(sys.argv[1]) if l.strip()]
D = 2 * (len(gam) - 1)
L = [[1], [1, -2]]                                   # coefficient lists in u (index = power)
for n in range(1, D):
    a, b = L[n], L[n - 1]
    c = [0] * (n + 2)
    for k, x in enumerate(a):
        c[k] += (4 * n + 1) * x; c[k + 1] += -2 * x
    for k, x in enumerate(b):
        c[k] -= 2 * n * (2 * n - 1) * x
    L.append(c)
P = [0] * (D + 1)
for j, g in enumerate(gam):
    for k, x in enumerate(L[2 * j]): P[k] += g * x
mono = [int(l) for l in open(sys.argv[2]) if l.strip()]
print("deg", D, "| matches agent's monomial file:", P == mono, "| P(0) =", "negative" if P[0] < 0 else "NOT negative")
# Q(s) = 25^D * P((48+s)/25) = sum_k P_k (48+s)^k 25^(D-k)
def taylor_shift(p, c):                                # p(x) -> p(x + c), p as coeff list low->high
    p = p[:]; n = len(p)
    for i in range(n - 1):
        for k in range(n - 2, i - 1, -1):
            p[k] += c * p[k + 1]
    return p
t0 = time.time()
Q = [P[k] * 25 ** (D - k) for k in range(D + 1)]        # = 25^D P(x/25) in x
Q = taylor_shift(Q, 48)                                # x = 48 + s
def var(p):
    s = [x for x in p if x != 0]
    return sum(1 for a, b in zip(s, s[1:]) if (a < 0) != (b < 0))
print("leading coeff positive:", Q[-1] > 0, "| sign variations on [0,oo):", var(Q), f"({time.time()-t0:.0f}s)")
# Vincent-Akritas-Strzebonski style: count roots in (0, oo) by bisection with transformations.
def roots_pos(p, depth=0):
    v = var(p)
    if v == 0: return 0
    if v == 1: return 1
    if depth > 60: raise RuntimeError("too deep")
    # split (0,oo) into (0,1) and (1,oo)
    p1 = taylor_shift(p, 1)                            # (1, oo): x = 1 + t
    r = 0
    if p1[0] == 0: r += 1                              # root at x = 1
    r += roots_pos(p1, depth + 1)
    q = taylor_shift(p[::-1], 1)                       # (0,1): x = 1/(1+t)
    r += roots_pos(q, depth + 1)
    return r
nr = roots_pos(Q)
print("real roots of P in (48/25, oo):", nr, "| P(48/25) sign:", "positive" if Q[0] > 0 else ("zero" if Q[0] == 0 else "negative"), f"| total {time.time()-t0:.0f}s")
