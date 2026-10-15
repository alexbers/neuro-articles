"""Exhaustive 'plus + flips + reduction' closure at rank r+1 around an F2 rank-r scheme S0:
for every plus transition of S0 (ordered pair of terms, mode), explore the whole flip-graph component at
rank r+1 (BFS over all flips), and reduce every reducible state (zero factor or two terms sharing two
factors). Reports the set of rank<=r schemes obtained (S0 itself excluded).
usage: python plus48_closure.py scheme.txt out.txt [state_limit]"""
import sys, time
from fmm import load_txt, save_txt
def mask(row): return sum((int(b) % 2) << i for i, b in enumerate(row))
n, m, p, U, V, W = load_txt(sys.argv[1])
dims = (n * m, m * p, n * p)
S0 = tuple(sorted((mask(a), mask(b), mask(c)) for a, b, c in zip(U, V, W)))
def canon(terms): return tuple(sorted(tuple(t) for t in terms))
def reduce(terms):
    terms = [list(t) for t in terms]; ch = True
    while ch:
        ch = False
        terms = [t for t in terms if t[0] and t[1] and t[2]]
        for mo in range(3):
            o1, o2 = [x for x in range(3) if x != mo]; seen = {}
            for i, t in enumerate(terms):
                k = (t[o1], t[o2])
                if k in seen: terms[seen[k]][mo] ^= t[mo]; terms.pop(i); ch = True; break
                seen[k] = i
            if ch: break
    return canon(terms)
def reductions(st):
    """all schemes obtained by one reduction step (drop a zero term, or merge two terms sharing two
    factors), each then reduced further greedily"""
    out = set(); terms = [list(t) for t in st]
    for i, t in enumerate(terms):
        if not (t[0] and t[1] and t[2]): out.add(reduce(terms[:i] + terms[i + 1:]))
    for mo in range(3):
        o1, o2 = [x for x in range(3) if x != mo]
        for i in range(len(terms)):
            for j in range(i + 1, len(terms)):
                if terms[i][o1] == terms[j][o1] and terms[i][o2] == terms[j][o2]:
                    tt = [list(t) for t in terms]; tt[i][mo] ^= tt[j][mo]; tt.pop(j)
                    out.add(reduce(tt))
    return out
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
LIM = int(sys.argv[3]) if len(sys.argv) > 3 else 10**9
r = len(S0); seen = set(); found = set(); comps = 0; maxcomp = 0; nplus = 0; t0 = time.time()
for i in range(r):
    for j in range(r):
        if i == j: continue
        for mo in range(3):
            a, b = list(S0[i]), list(S0[j])
            t1 = list(a); t1[mo] = a[mo] ^ b[mo]
            t2 = list(a); t2[mo] = b[mo]
            if t1[mo] == 0: continue
            new = [list(t) for k, t in enumerate(S0) if k not in (i, j)] + [t1, t2, b]
            st = canon(new); nplus += 1
            if st in seen: continue
            comps += 1; seen.add(st); front = [st]; size = 1
            while front and len(seen) < LIM:
                nf = []
                for s in front:
                    for s2 in nbrs(s):
                        if s2 in seen: continue
                        seen.add(s2); nf.append(s2); size += 1
                        for rs in reductions(s2):
                            if rs != S0: found.add(rs)
                front = nf
            maxcomp = max(maxcomp, size)
            if front: print('state limit reached: component not complete'); break
        else: continue
        break
    else: continue
    break
print(f'{sys.argv[1]}: plus transitions {nplus}, distinct rank-{r+1} components {comps}, states {len(seen)}, '
      f'max component {maxcomp}, reduced schemes different from S0: {len(found)} '
      f'(ranks {sorted(set(len(f) for f in found))}), {time.time()-t0:.0f}s', flush=True)
with open(sys.argv[2], 'w') as f:
    for k, sch in enumerate(sorted(found)):
        f.write(' '.join(f'{a},{b},{c}' for a, b, c in sch) + '\n')
