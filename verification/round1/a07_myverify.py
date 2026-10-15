# Coordinator's independent SDS check: D = P - N in Z_m1 x ... x Z_mr, |supp| = k,
# and sum_g D(g) D(g+y) = lambda for all y != 0.
import json, sys, itertools
from math import prod
def load(fn):
    d = json.load(open(fn))
    return list(d.values()) if isinstance(d, dict) else d
tot = bad = 0
for fn in sys.argv[1:]:
    items = load(fn)
    flat = []
    for it in items:
        flat.extend(it if isinstance(it, list) else [it])
    for e in flat:
        G = e['G']; v = prod(G); k = e['k']; lam = e['lambda']
        assert v == e['v']
        D = {}
        for t in e['P']: D[tuple(t)] = D.get(tuple(t), 0) + 1
        for t in e['N']: D[tuple(t)] = D.get(tuple(t), 0) - 1
        ok = all(c in (-1, 1) for c in D.values()) and len([c for c in D.values() if c]) == k
        els = list(itertools.product(*[range(m) for m in G]))
        for y in els:
            if not any(y): continue
            s = sum(c * D.get(tuple((g[i] + y[i]) % G[i] for i in range(len(G))), 0) for g, c in D.items())
            if s != lam: ok = False; break
        tot += 1; bad += (not ok)
        if not ok: print("FAIL", e['v'], e['k'], e['lambda'], G)
print(f"checked {tot} certificates, failures: {bad}")
