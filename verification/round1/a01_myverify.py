# Coordinator's independent check of A01: completely additive f mod k with f(q)=g(q) for primes q,
# g(q)=1 except listed primes; report first r>=1 with f(r)=f(r+1)=f(r+2)=0 (mod k), r+2 <= L.
import sys, numpy as np
k, L, fn = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
g = {int(a): int(b) for a, b in (l.split() for l in open(fn) if l.strip())}
N = L + 1
s = np.ones(N, dtype=bool); s[:2] = False
for i in range(2, int(N**0.5) + 1):
    if s[i]: s[i*i::i] = False
primes = np.nonzero(s)[0]; del s
f = np.zeros(N, dtype=np.uint8)
for q in primes.tolist():
    w = g.get(q, 1) % k
    if w == 0 and q not in g: continue
    pe = q
    while pe <= L:
        f[pe::pe] += w
        pe *= q
f %= k
z = (f == 0); z[0] = False
t = z[1:L-1] & z[2:L] & z[3:L+1]          # r = 1..L-2
idx = np.nonzero(t)[0]
print(f"k={k} L={L}: primes={len(primes)}; first zero triple r = {idx[0]+1 if len(idx) else 'none with r+2<=L'}")
