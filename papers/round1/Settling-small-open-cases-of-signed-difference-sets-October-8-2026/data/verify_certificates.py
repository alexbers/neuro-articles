# Independent check of certificates.json: for each entry, D = P - N in Z_{m1} x ... x Z_{mr}
# (P, N as coordinate tuples; P_index/N_index as mixed-radix indices, most significant first),
# verify P, N disjoint, |P|+|N| = k, and sum_g D(g) D(g+y) = lambda for every y != 0.
import json, itertools
C = json.load(open('certificates.json'))
def idx(t, G):
    x = 0
    for a, m in zip(t, G): x = x * m + a
    return x
bad = 0
for key, c in C.items():
    G, k, lam = c["group_moduli"], c["k"], c["lambda"]
    E = list(itertools.product(*[range(m) for m in G]))
    P = [tuple(x) for x in c["P"]]; N = [tuple(x) for x in c["N"]]
    ok = sorted(idx(t, G) for t in P) == c["P_index"] and sorted(idx(t, G) for t in N) == c["N_index"]
    ok &= len(set(P) | set(N)) == len(P) + len(N) == k and all(t in set(E) for t in P + N)
    D = {t: 1 for t in P}; D.update({t: -1 for t in N})
    for y in E:
        if any(y):
            s = sum(D.get(g, 0) * D.get(tuple((a + b) % m for a, b, m in zip(g, y, G)), 0) for g in D)
            ok &= (s == lam)
    print(f"{key:28s} tier {c['tier']}  {'OK' if ok else 'FAIL'}")
    bad += not ok
print("ALL OK" if bad == 0 else f"{bad} FAILED")
