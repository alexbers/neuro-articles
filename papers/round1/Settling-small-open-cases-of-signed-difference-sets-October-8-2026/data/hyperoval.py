# Hyperoval in PG(2,4) -> (64,18,2,6) PDS in GF(4)^3 = Z2^6; then D = (G \ (S u {0})) - {0} is a (64,46,30) SDS.
import itertools
from collections import Counter
# GF(4) = {0,1,a,a^2} as 2-bit ints with a^2 = a+1
def mul(x,y):
    r=0
    for i in range(2):
        if (y>>i)&1: r^= x<<i
    if r&4: r^=0b111
    return r
pts=[(1,0,0),(0,1,0),(0,0,1),(1,1,1)]  # frame
# conic x^2 = yz? use hyperoval = conic {(1,t,t^2)} u {(0,0,1)} plus nucleus
conic=[(1,t,mul(t,t)) for t in range(4)]+[(0,0,1)]
# nucleus of conic y^2 = xz in char 2: (0,1,0)
H=conic+[(0,1,0)]
S=set()
for p in H:
    for c in (1,2,3): S.add(tuple(mul(c,x) for x in p))
def vec(p): return tuple(((x>>i)&1) for x in p for i in range(2))
Sv=set(vec(p) for p in S)
E=list(itertools.product(range(2),repeat=6)); zero=(0,)*6
sub=lambda a,b: tuple((x-y)%2 for x,y in zip(a,b))
cnt=Counter(sub(a,b) for a in Sv for b in Sv if a!=b)
print(len(Sv), set(cnt[e] for e in Sv), set(cnt[e] for e in E if e not in Sv and e!=zero))
# SDS from complement
P=[e for e in E if e not in Sv and e!=zero]; N=[zero]
c=Counter()
coef={**{e:1 for e in P},**{e:-1 for e in N}}
for a in coef:
    for b in coef: c[sub(a,b)]+=coef[a]*coef[b]
print("SDS k=",len(coef),"lambda set",set(c[e] for e in E if e!=zero))
