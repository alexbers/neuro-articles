# Independent exact verification of the SU certificate from the plain-text data files
# (explicit polynomial expansion per leaf; no Kronecker digits).
import sys, json
from fractions import Fraction as F
dd=sys.argv[1]
meta=json.load(open(dd+'/su_certificate.json'))
gamma=[int(l) for l in open(dd+'/su_gamma.txt')]
Pl=[int(l) for l in open(dd+'/su_P_monomial.txt')]
R=[int(l) for l in open(dd+'/su_R.txt')]
leaves=[tuple(int(x) for x in l.split()) for l in open(dd+'/su_leaves.txt')]
a,b=meta['r_num'],meta['r_den']
def add(p,q):
    n=max(len(p),len(q)); return [(p[i] if i<len(p) else 0)+(q[i] if i<len(q) else 0) for i in range(n)]
def mul(p,q):
    out=[0]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        if x:
            for j,y in enumerate(q): out[i+j]+=x*y
    return out
# (1) P = sum gamma_j Lam_{2j}
lam=[[1],[1,-2]]
for n in range(0,2*len(gamma)):
    lam.append(add(add([(4*n+5)*c for c in lam[-1]],[0]+[-2*c for c in lam[-1]]),[-(2*(n+1)*(2*n+1))*c for c in lam[-2]]))
P=[]
for j,g in enumerate(gamma): P=add(P,[g*c for c in lam[2*j]])
while len(P)>1 and P[-1]==0: P.pop()
assert P==Pl, 'monomial coefficients mismatch'
assert P[0]<0, 'P(0) >= 0'
d=len(P)-1
# (2) R(y) = b^d P((a+y)/b)
Rc=[0]
for k in range(d,-1,-1):           # Horner in y: acc = acc*(a+y) + P_k*b^(d-k)
    Rc=add(mul(Rc,[a,1]),[P[k]*b**(d-k)])
while len(Rc)>1 and Rc[-1]==0: Rc.pop()
assert Rc==R, 'R mismatch'
# (3) leaves (u-variable, for P): chain from r=a/b to infinity, explicit Descartes check
assert leaves[0][0]*b==a*leaves[0][2], 'first leaf does not start at r'
assert leaves[-1][3]==0 and leaves[-1][1]>0
for (u0,u1,v0,v1),(x0,x1,y0,y1) in zip(leaves,leaves[1:]):
    assert v0>0 and v1>0 and u0*v1<u1*v0 and u1*y0==x0*v1
for (u0,u1,v0,v1) in leaves:
    U=[u0,u1]; V=[v0,v1]
    h=[P[d]]; Vp=[1]
    for i in range(d-1,-1,-1):
        Vp=mul(Vp,V)
        h=add(mul(h,U),[P[i]*x for x in Vp])
    assert h[0]>0 and all(t>=0 for t in h), ('leaf fails',(u0,u1,v0,v1))
print('OK: D=%d degree=%d r=%d/%d, %d leaves verified by explicit expansion; P(0)=%s<0'%(meta['D'],d,a,b,len(leaves),str(P[0])[:20]+'...'))
