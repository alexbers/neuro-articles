# Coordinator's independent check: periodic autocorrelation = k*[d=0], entries in {0,±1},
# weight k, and properness (support not inside one residue class mod any prime p | n).
import json, sys
d = json.load(open(sys.argv[1]))
def primes(n):
    ps, m, p = [], n, 2
    while p*p <= m:
        if m % p == 0:
            ps.append(p)
            while m % p == 0: m //= p
        p += 1
    if m > 1: ps.append(m)
    return ps
for name, e in d.items():
    n, k, a = e["n"], e["k"], e["seq"]
    assert len(a) == n and all(x in (-1, 0, 1) for x in a)
    paf = [sum(a[i]*a[(i+s) % n] for i in range(n)) for s in range(n)]
    ok = paf[0] == k and all(v == 0 for v in paf[1:])
    supp = [i for i in range(n) if a[i]]
    proper = all(len({i % p for i in supp}) > 1 for p in primes(n))
    print(f"{name:10s} n={n:4d} k={k:4d} PAF_ok={ok} weight={len(supp)} proper={proper}")
