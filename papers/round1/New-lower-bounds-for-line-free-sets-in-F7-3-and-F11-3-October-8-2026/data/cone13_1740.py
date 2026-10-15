# Cone construction (S. Ball; MathOverflow q/229442) over the 38-point double blocking set of PG(2,13)
# of Csajbok-Heger (Eur. J. Combin. 78 (2019), Sect. 4.1): a 2-blocking set of AG(3,13) of size 1+12*38=457,
# hence a line-free set of 2197-457=1740 points in F_13^3.  Writes linefree_F13_1740_cone.txt (index x+13y+169z).
import itertools, collections
q=13
def norm(v):
    v=tuple(x%q for x in v)
    for x in v:
        if x: inv=pow(x,-1,q); return tuple((y*inv)%q for y in v)
    return None
pts=set()
for x in range(q):
    for z in range(q):
        if (x,z)!=(0,0): pts.add(norm((x,0,z)))   # X axis [0:1:0]
    for y in range(q):
        if (x,y)!=(0,0): pts.add(norm((0,y,x)))   # Y axis [1:0:0]
assert len(pts)==27
for h in [(1,0,1),(1,0,0),(0,1,1),(0,1,0)]: pts.discard(norm(h))
extra=[(1,1,1),(1,12,1),(2,8,1),(3,7,1),(4,3,1),(5,9,1),(6,10,1),(7,4,1),(8,2,1),(9,5,1),(10,11,1),(11,6,1),(12,1,1),(1,3,0),(1,9,0)]
for e in extra: pts.add(norm(e))
B=pts; print("|B| =",len(B))
# all lines of PG(2,13): [a:b:c]; check each contains >=2 points of B
allproj=set(norm(v) for v in itertools.product(range(q),repeat=3) if any(v))
assert len(allproj)==q*q+q+1
mn=min(sum(1 for p in B if (l[0]*p[0]+l[1]*p[1]+l[2]*p[2])%q==0) for l in allproj)
print("min number of B-points on a projective line:",mn,"(double blocking iff >=2)")
# cone: S = {lam*b : b in B, lam in F_q} in F_q^3
S=set()
for b in B:
    for lam in range(q): S.add(tuple((lam*x)%q for x in b))
print("|cone| =",len(S), "expected 1+12*38 =",1+12*38)
C=set(itertools.product(range(q),repeat=3))-S
print("|complement| =",len(C))
# exhaustive check of all affine lines
dirs=[d for d in itertools.product(range(q),repeat=3) if any(d) and next(t for t in d if t)==1]
assert len(dirs)==q*q+q+1
full=0; nlines=0; seen=set()
for d in dirs:
    for a in itertools.product(range(q),repeat=3):
        L=frozenset(tuple((a[i]+t*d[i])%q for i in range(3)) for t in range(q))
        if L in seen: continue
        seen.add(L); nlines+=1
        if L<=C: full+=1
print("lines:",nlines,"expected",q*q*(q*q+q+1)," full lines inside complement:",full)
open(__import__("os").path.join(__import__("os").path.dirname(__import__("os").path.abspath(__file__)),"linefree_F13_1740_cone.txt"),"w").write(" ".join(str(x+q*y+q*q*z) for (x,y,z) in sorted(C))+"\n")
