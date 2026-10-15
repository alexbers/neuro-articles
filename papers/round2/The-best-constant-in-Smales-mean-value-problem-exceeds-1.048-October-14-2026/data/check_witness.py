# Independent referee check of the Koebe witness (exact rationals + mpmath; replays the Lean quadtree).
# Usage: python3 check_witness.py   (reads koebe_witness_data.lean from this directory)
# Independent referee check of the Koebe witness (exact rationals + mpmath)
from fractions import Fraction as Fr
import mpmath as mp
mp.mp.dps = 50

r  = Fr(497498487,500000000)
c  = (Fr(-105117631,125000000), Fr(3016503,10**9))
w0 = (Fr(-149268011,200000000), Fr(313274719,10**9))
a  = (Fr(-744989837,10**9), Fr(-504190327,10**9))

# Gaussian rational arithmetic
def add(x,y): return (x[0]+y[0], x[1]+y[1])
def sub(x,y): return (x[0]-y[0], x[1]-y[1])
def mul(x,y): return (x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0])
def conj(x): return (x[0], -x[1])
def nsq(x): return x[0]*x[0]+x[1]*x[1]
def inv(x): n=nsq(x); return (x[0]/n, -x[1]/n)
def sc(q,x): return (q*x[0], q*x[1])
one=(Fr(1),Fr(0)); zero=(Fr(0),Fr(0))
cb=conj(c); ab=conj(a)

# polynomials as coefficient lists (low degree first)
def padd(p,q):
    n=max(len(p),len(q)); p=p+[zero]*(n-len(p)); q=q+[zero]*(n-len(q))
    return [add(x,y) for x,y in zip(p,q)]
def pmul(p,q):
    out=[zero]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q):
            out[i+j]=add(out[i+j],mul(x,y))
    return out
def pscale(s,p): return [mul(s,x) for x in p]
def peval(p,w):
    acc=zero
    for x in reversed(p): acc=add(mul(acc,w),x)
    return acc

E0 = sub(add(one,mul(cb,w0)), sc(r,add(w0,c)))
z0 = mul(mul(sc(r,add(w0,c)), add(one,mul(cb,w0))), inv(mul(E0,E0)))
S = [add(one, sc(r,c)), add(cb,(r,Fr(0)))]
E = [sub(one, sc(r,c)), sub(cb,(r,Fr(0)))]
wa = [sub(zero,a), one]; oa=[one, sub(zero,ab)]
wc = [c, one]; oc=[one, cb]
K1 = sc(r, sub(one, mul(c,cb))); K2 = sub(one, mul(a,ab))
P = padd(pscale(K1, pmul(S, pmul(wa,oa))),
         pscale(K2, padd(pscale((r,Fr(0)), pmul(pmul(wc,oc),E)),
                         pscale(sub(zero,z0), pmul(E,pmul(E,E))))))
while P and P[-1]==zero: P.pop()
print("deg P =", len(P)-1)

C = lambda x: mp.mpc(mp.mpf(x[0].numerator)/x[0].denominator, mp.mpf(x[1].numerator)/x[1].denominator)
rr=mp.mpf(r.numerator)/r.denominator; cc=C(c); aa=C(a); ww0=C(w0)
def Phi(w): return rr*(w+cc)*(1+mp.conj(cc)*w)/((1+mp.conj(cc)*w)-rr*(w+cc))**2
def Bf(w): return (w-aa)/(1-mp.conj(aa)*w)
Z0=Phi(ww0); B0=Bf(ww0)
def H(w): return (Phi(w)-Z0)*Bf(w)/B0
print("z0 =", mp.nstr(Z0,12), " exact-rational z0 check:", mp.nstr(abs(C(z0)-Z0),5))
print("Phi(a) =", mp.nstr(Phi(aa),12))
m = 1/abs(B0)
print("m = 1/|B(w0)| =", mp.nstr(m,25))
# exact margin inequality (as in Lean margin_check)
lhs = nsq(sub(w0,a))*Fr(131,125)**2; rhs = nsq(sub(one,mul(ab,w0)))
print("margin_check lhs<rhs:", lhs<rhs, " also > 1.048069073225:", nsq(sub(w0,a))*Fr(1048069073225,10**12)**2 < rhs)
print("|c|,|a|,|w0| =", [mp.nstr(abs(x),10) for x in (cc,aa,ww0)])
# pseudo-hyperbolic distance
print("pseudo-hyp dist(w0,a) =", mp.nstr(abs(B0),15))

# Verify identity H'(w) E^3 (1-ab w)^2 B0 = P(w) numerically, H' by numerical differentiation
for w in [mp.mpc('0.3','0.2'), mp.mpc('-0.7','0.5'), mp.mpc('0.1','-0.9')]:
    Hp = mp.diff(H, w)
    Ew = (1+mp.conj(cc)*w)-rr*(w+cc)
    lhs = Hp*Ew**3*(1-mp.conj(aa)*w)**2*B0
    print("identity rel err:", mp.nstr(abs(lhs-C(peval(P,(Fr(w.real),Fr(w.imag)))))/abs(lhs),5))
    # also Phi'(w) formula
    Sw=(1+mp.conj(cc)*w)+rr*(w+cc)
    print("  Phi' formula rel err:", mp.nstr(abs(mp.diff(Phi,w)-rr*(1-abs(cc)**2)*Sw/Ew**3)/abs(mp.diff(Phi,w)),5))

coeffs=[C(x) for x in P]
roots = mp.polyroots(list(reversed(coeffs)), maxsteps=200, extraprec=200)
print("zeros of P:", [mp.nstr(z,15) for z in roots])
print("moduli:", [mp.nstr(abs(z),12) for z in roots])
# Pole of Phi: E(w)=0
wp = (rr*cc-1)/(mp.conj(cc)-rr)
print("pole of Phi at", mp.nstr(wp,12), "|.|=", mp.nstr(abs(wp),12))
# radius rho* where |u|=1 first reached (u = r(w+c)/(1+cb w)); search
def maxu(rho):
    return max(abs(rr*(w+cc)/(1+mp.conj(cc)*w)) for w in [rho*mp.expj(2*mp.pi*k/20000) for k in range(20000)])
lo,hi=mp.mpf(1),mp.mpf('1.01')
for _ in range(30):
    mid=(lo+hi)/2
    if maxu(mid)<1: lo=mid
    else: hi=mid
print("Phi analytic & univalent (|u|<1) for |w| <", mp.nstr(lo,10))
# images of critical points of F (zeros of P with |w| in (1, rho*))
for z in roots:
    if abs(z)<lo:
        cpt=Phi(z); print("crit pt of F: w=",mp.nstr(z,10)," z=",mp.nstr(cpt,12)," |F(c)|/|c-z0| =",mp.nstr(abs(H(z))/abs(cpt-Z0),10))
# winding number of P around |w|=1 and min |P| on circle
import cmath
Pc=[complex(x) for x in coeffs]
def Pn(w):
    s=0
    for x in reversed(Pc): s=s*w+x
    return s
N=2_000_000
import numpy as np
t=np.linspace(0,2*np.pi,N,endpoint=False); W=np.exp(1j*t)
vals=np.polyval(Pc[::-1],W)
ang=np.unwrap(np.angle(vals)); wind=(ang[-1]-ang[0]+np.angle(vals[0]/vals[-1]))/(2*np.pi)
print("winding of P on |w|=1:", round(wind,6), " min|P| on circle:", abs(vals).min(), " max:",abs(vals).max())
# ratio |F|/|z-z0| on boundary
vals2=[abs(H(mp.expj(th)))/abs(Phi(mp.expj(th))-Z0) for th in [0.1,1,2,3,3.14,-2]]
print("boundary ratio samples:", [mp.nstr(v,15) for v in vals2])
# distance z0 to boundary of D (sample boundary densely near the fjord tip)
import numpy as np
def Phin(w): 
    cn=complex(cc); rn=float(rr)
    return rn*(w+cn)*(1+cn.conjugate()*w)/((1+cn.conjugate()*w)-rn*(w+cn))**2
th=np.linspace(0,2*np.pi,4_000_000,endpoint=False); bd=Phin(np.exp(1j*th))
z0n=complex(Z0); print("dist(z0,dD) ~", np.abs(bd-z0n).min(), " fjord tip -r/(1+r)^2 =", float(-rr/(1+rr)**2), " max|z| on dD ~", np.abs(bd).max())

# Exact quadtree replay from the Lean certificate string
import re
import os
txt=open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'koebe_witness_data.lean')).read()
tree=txt.split('def certTree : QTree :=')[1].split('end SmaleKoebe')[0]
toks=re.findall(r'\(|\)|n|l',tree)
pos=0
def parse():
    global pos
    t=toks[pos]
    if t=='l': pos+=1; return 'L'
    if t=='(':
        pos+=1; assert toks[pos]=='n'; pos+=1
        kids=[parse() for _ in range(4)]
        assert toks[pos]==')'; pos+=1
        return kids
    raise ValueError(t)
T=parse(); assert pos==len(toks)
def count(t): return 1 if t=='L' else 1+sum(count(k) for k in t)
print("quadtree nodes:", count(T))
def shift(z,p):
    # Taylor shift p(z+delta)
    out=[zero]
    for x in reversed(p):
        out = padd(pmul(out,[z,one]), [x])
    return out
def gabs1(x): return abs(x[0])+abs(x[1])
def outside(cx,cy,h): return 1 < max(abs(cx)-h,0)**2+max(abs(cy)-h,0)**2
def safe(cx,cy,h):
    t=shift((cx,cy),P); d=Fr(3)*h/2
    tb=sum(gabs1(t[k])*d**k for k in range(1,len(t)))
    return tb*tb < nsq(t[0])
leaves=[0,0]
def check(t,cx,cy,h):
    if t=='L':
        o=outside(cx,cy,h)
        if o: leaves[0]+=1; return True
        s=safe(cx,cy,h); leaves[1]+=1; return s
    h2=h/2
    return (check(t[0],cx-h2,cy-h2,h2) and check(t[1],cx+h2,cy-h2,h2) and
            check(t[2],cx-h2,cy+h2,h2) and check(t[3],cx+h2,cy+h2,h2))
print("exact quadtree check passes:", check(T,Fr(0),Fr(0),Fr(1)), " (outside leaves, safe leaves) =", leaves)
