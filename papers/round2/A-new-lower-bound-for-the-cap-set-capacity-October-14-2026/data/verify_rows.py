#!/usr/bin/env python3
"""Independent verifier for symmetric (pre-)admissible row sets.

A row is a tuple of types t_i in {0..6}; type t stands for the Z3-orbit (cyclic rotations) of
TRIPLES[t] in {0,1,2}^3.  The expanded set is the union over rows of the product of the orbits.
This script checks the TYPE-LEVEL sufficient conditions (proved in README, brute-force validated for
g<=3 in verify_reduction.py / verify_mixed.py):
  (P) the weight profiles of distinct rows are pairwise incomparable (componentwise);
  (T) for any three distinct rows x,y,z there is a group i with sorted(x_i,y_i,z_i) NOT in BAD,
      where BAD is recomputed here from scratch by brute force over rotations.
It also recomputes BAD independently and reports the expanded size, the weight distribution and the
resulting cap-set capacity bound (Edel/Tyrrell/FunSearch recipe with the 6-dim (12,112,112) collection,
middle level I~(m,m-1), arbitrary weights: size factor sum_s b0^(n-|s|) b1^|s|).
usage: verify_rows.py rows.txt [m]
"""
import sys, itertools, math
TRIPLES = [(0,0,0),(0,0,1),(0,0,2),(0,1,2),(0,2,1),(1,1,1),(2,2,2)]
def rots(t):
    x,y,z = TRIPLES[t]
    return {(x,y,z),(z,x,y),(y,z,x)}
def good(a,b,c):
    s = sorted((a,b,c))
    return s == [0,1,2] or (s[0] == 0 and s[1] == 0 and s[2] != 0)
# BAD[t1][t2] = set of t3 such that SOME choice of rotations gives no good coordinate in the group
BAD = [[set() for _ in range(7)] for _ in range(7)]
for t1, t2, t3 in itertools.product(range(7), repeat=3):
    if any(not any(good(r1[k], r2[k], r3[k]) for k in range(3))
           for r1 in rots(t1) for r2 in rots(t2) for r3 in rots(t3)):
        BAD[t1][t2].add(t3)
WT = [sum(1 for v in TRIPLES[t] if v) for t in range(7)]
ORB = [len(rots(t)) for t in range(7)]

def load(fn):
    rows = []
    for line in open(fn):
        digs = [int(c) for c in line if c.isdigit()]
        if digs: rows.append(tuple(digs))
    return rows

def main():
    fn = sys.argv[1]; m = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    rows = load(fn)
    g = len(rows[0]); n = 3 * g
    assert all(len(r) == g for r in rows), 'ragged rows'
    assert len(set(rows)) == len(rows), 'duplicate rows'
    R = len(rows)
    prof = [tuple(WT[t] for t in r) for r in rows]
    # (P) pairwise incomparable profiles
    from collections import defaultdict
    for a in range(R):
        pa = prof[a]
        for b in range(a + 1, R):
            pb = prof[b]
            le = all(x <= y for x, y in zip(pa, pb)); ge = all(x >= y for x, y in zip(pa, pb))
            if le or ge:
                print('FAIL (P): comparable profiles', rows[a], rows[b]); sys.exit(1)
    print('(P) ok: %d rows, profiles pairwise incomparable' % R)
    # (T) bitset check
    M = [[0] * 7 for _ in range(g)]
    for idx, r in enumerate(rows):
        for i, t in enumerate(r): M[i][t] |= (1 << idx)
    BADMASK = [[[0] * 7 for _ in range(7)] for _ in range(g)]
    for i in range(g):
        for t1 in range(7):
            for t2 in range(7):
                v = 0
                for t3 in BAD[t1][t2]: v |= M[i][t3]
                BADMASK[i][t1][t2] = v
    full = (1 << R) - 1
    for a in range(R):
        x = rows[a]
        for b in range(a + 1, R):
            y = rows[b]
            mask = full & ~((1 << a) | (1 << b))
            for i in range(g):
                mask &= BADMASK[i][x[i]][y[i]]
                if not mask: break
            if mask:
                c = (mask & -mask).bit_length() - 1
                print('FAIL (T): bad triple', x, y, rows[c]); sys.exit(1)
        if a % 200 == 0: print('  ... row', a, flush=True)
    print('(T) ok: no bad triple')
    size = sum(math.prod(ORB[t] for t in r) for r in rows)
    wdist = defaultdict(int)
    for r in rows: wdist[sum(WT[t] for t in r)] += math.prod(ORB[t] for t in r)
    a0, a1 = 12, 112
    lb0 = math.log(m * a0) + (m - 1) * math.log(a1); lb1 = m * math.log(a1)
    tot = sum(cnt * math.exp((n - w) * lb0 + w * lb1 - (n * lb0)) for w, cnt in wdist.items())  # relative to all-zero weight
    lncap = (math.log(tot) + n * lb0) / (6 * m * n)
    print('expanded size %d, weights %s' % (size, dict(sorted(wdist.items()))))
    print('capacity bound (m=%d): %.9f' % (m, math.exp(lncap)))

if __name__ == '__main__':
    main()
