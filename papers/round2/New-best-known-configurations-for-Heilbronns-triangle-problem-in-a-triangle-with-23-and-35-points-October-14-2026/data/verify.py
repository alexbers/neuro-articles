#!/usr/bin/env python3
"""Independent exact check of a Heilbronn configuration in the triangle T=(0,0),(1,0),(0,1).
usage: python3 verify.py coords.txt      (lines 'x y', decimal literals, '#' comments)
Prints n, containment check, and the exact normalised value 2*min area (= min area / area(T))."""
import sys, itertools
from fractions import Fraction as F
pts = [tuple(F(t) for t in l.split()[:2]) for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
assert all(x >= 0 and y >= 0 and x + y <= 1 for x, y in pts), 'point outside the triangle'
assert len(set(pts)) == len(pts)
m = min(abs((b[0]-a[0])*(c[1]-a[1]) - (b[1]-a[1])*(c[0]-a[0])) for a, b, c in itertools.combinations(pts, 3))
v = m  # 2*area = |cross|; normalised value = area/(1/2) = |cross|
print('n =', len(pts), ' all points in T: yes')
print('normalised value = %s ~ %.20f' % (v, float(v)))
