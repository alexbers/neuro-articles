"""Shared helpers (same moves as plus48_closure.py): canonical form, flips, split/plus starts."""

def canon(terms): return tuple(sorted(tuple(t) for t in terms))

def nbrs(st):
    terms = [list(t) for t in st]
    for mo in range(3):
        g = {}
        for i, t in enumerate(terms): g.setdefault(t[mo], []).append(i)
        for v in g.values():
            for i in v:
                for j in v:
                    if i == j: continue
                    for o1 in range(3):
                        if o1 == mo: continue
                        o2 = 3 - mo - o1
                        tt = [list(t) for t in terms]
                        tt[i][o1] ^= tt[j][o1]; tt[j][o2] ^= tt[i][o2]
                        yield canon(tt)

def plus_starts(S0):
    r = len(S0)
    for i in range(r):
        for j in range(r):
            if i == j: continue
            for mo in range(3):
                a, b = list(S0[i]), list(S0[j])
                t1 = list(a); t1[mo] = a[mo] ^ b[mo]
                t2 = list(a); t2[mo] = b[mo]
                if t1[mo] == 0: continue
                yield canon([list(t) for k, t in enumerate(S0) if k not in (i, j)] + [t1, t2, b])
