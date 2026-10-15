"""First-order Z/4 lifting test (e=0) for every F2 scheme in the rank-(r+1) plus/flip closure of an F2 rank-r
scheme (same enumeration as plus48_closure.py).  For each state S (rank r+1 over F2) we test whether
  rhs = (T - sum_t u_t v_t w_t)/2 mod 2  lies in the image of the Jacobian J_S over F2,
i.e. whether S lifts to a decomposition of T over Z/4 with the same number of terms.
Sharded: process k of K handles components with index = k (mod K).
usage: python e0_closure.py scheme.txt k K out.txt"""
import sys, time
import numpy as np
from fmm import load_txt, mm_tensor
from plus48_tools import canon, nbrs, plus_starts

path, k, K, out = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
n, m, p, U, V, W = load_txt(path)
DA, DB, DC = n * m, m * p, n * p
T = mm_tensor(n, m, p).astype(np.int64)
def mask(row): return sum((int(b) % 2) << i for i, b in enumerate(row))
S0 = canon([(mask(a), mask(b), mask(c)) for a, b, c in zip(U, V, W)])
bits = [[i for i in range(16) if (x >> i) & 1] for x in range(1 << 16)] if max(DA, DB, DC) <= 16 else None
def supp(x): return bits[x] if bits is not None else [i for i in range(x.bit_length()) if (x >> i) & 1]

def e0_test(st):
    r = len(st); per = DA + DB + DC; nv = r * per
    rows = [0] * (DA * DB * DC)
    S = np.zeros((DA, DB, DC), dtype=np.int64)
    for t, (a, b, c) in enumerate(st):
        ia, ib, ic = supp(a), supp(b), supp(c)
        S[np.ix_(ia, ib, ic)] += 1
        off = t * per
        for bb in ib:
            for cc in ic:
                base = bb * DC + cc
                for aa in range(DA): rows[aa * DB * DC + base] |= 1 << (off + aa)
        for aa in ia:
            for cc in ic:
                for bb in range(DB): rows[aa * DB * DC + bb * DC + cc] |= 1 << (off + DA + bb)
        for aa in ia:
            for bb in ib:
                base = aa * DB * DC + bb * DC
                for cc in range(DC): rows[base + cc] |= 1 << (off + DA + DB + cc)
    F = T - S
    assert not (F % 2).any()
    rhs = ((F // 2) % 2).reshape(-1)
    top = 1 << nv
    piv = {}
    for i, x in enumerate(rows):
        if rhs[i]: x |= top
        while x:
            c = (x & -x).bit_length() - 1
            if c == nv: return False          # 0 = 1: inconsistent, no first-order lift
            if c in piv: x ^= piv[c]
            else: piv[c] = x; break
    return True

seen = set(); comp = 0; tested = 0; passed = []; t0 = time.time()
with open(out, 'w') as fo:
    for st in plus_starts(S0):
        if st in seen: continue
        comp += 1
        front = [st]; seen.add(st); members = [st]
        while front:
            nf = []
            for s in front:
                for s2 in nbrs(s):
                    if s2 not in seen: seen.add(s2); nf.append(s2); members.append(s2)
            front = nf
        if comp % K != k: continue
        for s in members:
            tested += 1
            if e0_test(s):
                passed.append(s)
                fo.write('PASS ' + ' '.join(f'{a},{b},{c}' for a, b, c in s) + '\n'); fo.flush()
        if comp % (10 * K) == k:
            print(f'comp {comp} tested {tested} passed {len(passed)} {time.time()-t0:.0f}s', flush=True)
    fo.write(f'DONE shard {k}/{K}: components {comp} (all), states tested {tested}, first-order lifts {len(passed)}, '
             f'{time.time()-t0:.0f}s\n')
print('DONE', k, K, tested, len(passed), flush=True)
