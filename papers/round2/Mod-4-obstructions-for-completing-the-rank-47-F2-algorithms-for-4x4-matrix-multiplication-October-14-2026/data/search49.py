"""Two-level search for further F2 rank-47 schemes of <4,4,4> near a rigid rank-47 scheme S0, and first-order
Z/4 lift tests of all rank-48 F2 schemes met.
 1. C48 = plus/flip closure of S0 at rank 48 (all reduce only to S0, see plus48_closure.py).
 2. repeat: random state of C48 (or of a new rank-48 component), random split -> rank 49, explore its rank-49 flip
    component (up to LIM1 states), collect all reductions to rank-48 schemes outside the explored 48-components.
 3. explore each new rank-48 component (up to LIM2 states): record every reduction to rank <= 47 different
    from S0 (NEW47), and test each rank-48 state for a first-order Z/4 lift (e0).
usage: python search49.py scheme.txt outdir seconds seed [LIM1 LIM2]"""
import sys, os, random, time
import numpy as np
from fmm import load_txt, save_txt, mm_tensor
from plus48_tools import canon, nbrs, plus_starts

path, outdir, secs, seed = sys.argv[1], sys.argv[2], float(sys.argv[3]), int(sys.argv[4])
LIM1 = int(sys.argv[5]) if len(sys.argv) > 5 else 30000
LIM2 = int(sys.argv[6]) if len(sys.argv) > 6 else 30000
os.makedirs(outdir, exist_ok=True)
rng = random.Random(seed)
n, m, p, U, V, W = load_txt(path)
DA, DB, DC = n * m, m * p, n * p
T = mm_tensor(n, m, p).astype(np.int64)
def mask(row): return sum((int(b) % 2) << i for i, b in enumerate(row))
S0 = canon([(mask(a), mask(b), mask(c)) for a, b, c in zip(U, V, W)])
bits = [[i for i in range(16) if (x >> i) & 1] for x in range(1 << 16)]

def e0_test(st):
    r = len(st); per = DA + DB + DC; nv = r * per
    rows = [0] * (DA * DB * DC)
    S = np.zeros((DA, DB, DC), dtype=np.int64)
    for t, (a, b, c) in enumerate(st):
        ia, ib, ic = bits[a], bits[b], bits[c]
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
    top = 1 << nv; piv = {}
    for i, x in enumerate(rows):
        if rhs[i]: x |= top
        while x:
            c = (x & -x).bit_length() - 1
            if c == nv: return False
            if c in piv: x ^= piv[c]
            else: piv[c] = x; break
    return True

def reduce_greedy(terms):
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
    out = set(); terms = [list(t) for t in st]
    for i, t in enumerate(terms):
        if not (t[0] and t[1] and t[2]): out.add(reduce_greedy(terms[:i] + terms[i + 1:]))
    for mo in range(3):
        o1, o2 = [x for x in range(3) if x != mo]
        for i in range(len(terms)):
            for j in range(i + 1, len(terms)):
                if terms[i][o1] == terms[j][o1] and terms[i][o2] == terms[j][o2]:
                    tt = [list(t) for t in terms]; tt[i][mo] ^= tt[j][mo]; tt.pop(j)
                    out.add(reduce_greedy(tt))
    return out

def component(st, lim):
    seen = {st}; front = [st]
    while front and len(seen) < lim:
        nf = []
        for s in front:
            for s2 in nbrs(s):
                if s2 not in seen: seen.add(s2); nf.append(s2)
        front = nf
    return seen, not front

def save(st, name):
    U = [[(t[0] >> i) & 1 for i in range(DA)] for t in st]
    V = [[(t[1] >> i) & 1 for i in range(DB)] for t in st]
    W = [[(t[2] >> i) & 1 for i in range(DC)] for t in st]
    save_txt(os.path.join(outdir, name), n, m, p, U, V, W)

log = open(os.path.join(outdir, 'log.txt'), 'a')
def say(s): print(s, file=log, flush=True)
t0 = time.time()
done48 = set()
for st in plus_starts(S0):
    if st in done48: continue
    comp, _ = component(st, 10 ** 9); done48 |= comp
say(f'closure48 of S0: {len(done48)} states')
pool48 = list(done48)
new47 = set(); e0_tested = 0; e0_pass = 0; samples = 0; newcomps = 0
while time.time() - t0 < secs:
    samples += 1
    s48 = rng.choice(pool48)
    starts = list(plus_starts(s48))
    st = rng.choice(starts)
    comp49, complete49 = component(st, LIM1)
    cand = set()
    for s in comp49:
        for r_ in reductions(s):
            if len(r_) <= 47:
                if r_ != S0 and r_ not in new47:
                    new47.add(r_); save(r_, f'new47_{len(new47)}.txt'); say(f'NEW rank-{len(r_)} scheme from rank-49 component')
            elif r_ not in done48:
                cand.add(r_)
    for c48 in cand:
        if c48 in done48: continue
        comp48, complete48 = component(c48, LIM2)
        done48 |= comp48; newcomps += 1
        pool48.extend(rng.sample(sorted(comp48), min(50, len(comp48))))
        for s in comp48:
            for r_ in reductions(s):
                if r_ != S0 and r_ not in new47:
                    new47.add(r_); save(r_, f'new47_{len(new47)}.txt'); say(f'NEW rank-{len(r_)} scheme (from new rank-48 component)')
            e0_tested += 1
            if e0_test(s):
                e0_pass += 1; save(s, f'e0pass_{e0_pass}.txt'); say('E0 PASS: rank-48 F2 scheme with first-order Z/4 lift')
    say(f'sample {samples}: 49-comp {len(comp49)} complete={complete49}; new 48-components so far {newcomps}; '
        f'48-states seen {len(done48)}; e0 tested {e0_tested} pass {e0_pass}; new47 {len(new47)}; {time.time()-t0:.0f}s')
say(f'END samples {samples} newcomps {newcomps} states48 {len(done48)} e0 {e0_tested}/{e0_pass} new47 {len(new47)}')
