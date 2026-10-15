# Coordinator's exact check of Heilbronn-in-triangle certificates: points in triangle (0,0),(1,0),(0,1),
# value = min over triples of 2*area (unit-area normalization of the half-unit triangle), exact Fractions.
import sys, itertools
from fractions import Fraction as F
def parse(fn):
    pts = []
    for line in open(fn):
        s = line.split("#")[0].strip()
        if not s: continue
        a, b = s.replace(",", " ").split()[:2]
        pts.append((F(a), F(b)))
    return pts
for fn in sys.argv[1:]:
    P = parse(fn)
    inside = all(x >= 0 and y >= 0 and x + y <= 1 for x, y in P)
    distinct = len(set(P)) == len(P)
    m = min(abs((b[0]-a[0])*(c[1]-a[1]) - (c[0]-a[0])*(b[1]-a[1])) for a, b, c in itertools.combinations(P, 3))
    # 2*area(abc) = |cross|; normalize to unit-area domain: area(domain)=1/2 => value = area/(1/2) = |cross|
    print(f"{fn}: n={len(P)} inside={inside} distinct={distinct} min 2*area = {float(m):.13f}")
