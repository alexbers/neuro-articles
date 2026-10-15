# Coordinator's independent check: S subset of F_p^3 (encoded x + p*y + p^2*z) contains no full line.
import sys, itertools
p = int(sys.argv[1]); S = set(map(int, open(sys.argv[2]).read().split()))
assert all(0 <= s < p**3 for s in S)
enc = lambda v: v[0] + p*v[1] + p*p*v[2]
# canonical directions: first nonzero coordinate = 1
dirs = [d for d in itertools.product(range(p), repeat=3) if any(d) and d[[i for i in range(3) if d[i]][0]] == 1]
lines = set(); bad = 0
for a in itertools.product(range(p), repeat=3):
    for d in dirs:
        L = frozenset(enc(tuple((a[i] + t*d[i]) % p for i in range(3))) for t in range(p))
        if L in lines: continue
        lines.add(L)
        if L <= S: bad += 1
print(f"p={p} |S|={len(S)} lines={len(lines)} (expected {p*p*(p*p+p+1)}) full lines in S: {bad}")
