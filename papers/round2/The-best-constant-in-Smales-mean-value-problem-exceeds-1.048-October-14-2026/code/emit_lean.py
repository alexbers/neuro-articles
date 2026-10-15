"""Exact (Fraction) construction of the Koebe-witness cubic, quadtree certificate and Lean emission."""
from fractions import Fraction as Fr
import json, sys, numpy as np
sys.setrecursionlimit(100000)
def gadd(a,b): return (a[0]+b[0], a[1]+b[1])
def gsub(a,b): return (a[0]-b[0], a[1]-b[1])
def gmul(a,b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
def gconj(a): return (a[0], -a[1])
def gnormSq(a): return a[0]*a[0]+a[1]*a[1]
def ginv(a): n=gnormSq(a); return (a[0]/n, -a[1]/n)
def gabs1(a): return abs(a[0])+abs(a[1])
def gof(q): return (Fr(q), Fr(0))
ONE=(Fr(1),Fr(0)); ZERO=(Fr(0),Fr(0))
def addL(p,q):
    if not p: return list(q)
    if not q: return list(p)
    return [gadd(p[0],q[0])]+addL(p[1:],q[1:])
def scaleL(c,p): return [gmul(c,x) for x in p]
def mulL(p,q):
    if not p: return []
    return addL(scaleL(p[0],q), [ZERO]+mulL(p[1:],q))
def negL(p): return scaleL((Fr(-1),Fr(0)),p)
def shiftL(z,l):
    if not l: return []
    return addL([l[0]], mulL([z,ONE], shiftL(z,l[1:])))
def tb(l,d):
    if not l: return Fr(0)
    return d*(gabs1(l[0])+tb(l[1:],d))
def outside(cx,cy,h): return 1 < max(abs(cx)-h,0)**2 + max(abs(cy)-h,0)**2
def safe(P,cx,cy,h):
    T=shiftL((cx,cy),P)
    if not T: return False
    return tb(T[1:], Fr(3)*h/2)**2 < gnormSq(T[0])
def build(P,cx,cy,h,depth=0,maxdepth=30):
    if outside(cx,cy,h) or safe(P,cx,cy,h): return 'L'
    if depth>=maxdepth: raise ValueError("too deep")
    h2=h/2
    return ('N', build(P,cx-h2,cy-h2,h2,depth+1), build(P,cx+h2,cy-h2,h2,depth+1),
                 build(P,cx-h2,cy+h2,h2,depth+1), build(P,cx+h2,cy+h2,h2,depth+1))
def count(t): return 1 if t=='L' else 1+sum(count(c) for c in t[1:])
def to_lean(t, out):
    if t=='L': out.append("l"); return
    out.append("(n")
    for c in t[1:]: out.append(" "); to_lean(c,out)
    out.append(")")
def make(rq, cq, w0q, aq):
    cbq=gconj(cq); abq=gconj(aq)
    E0=gsub(gadd(ONE,gmul(cbq,w0q)), gmul(gof(rq),gadd(w0q,cq)))
    z0q=gmul(gmul(gmul(gof(rq),gadd(w0q,cq)),gadd(ONE,gmul(cbq,w0q))), ginv(gmul(E0,E0)))
    K1=gmul(gof(rq), gsub(ONE, gmul(cq,cbq))); K2=gsub(ONE, gmul(aq,abq))
    Sl=[gadd(ONE,gmul(gof(rq),cq)), gadd(cbq,gof(rq))]
    El=[gsub(ONE,gmul(gof(rq),cq)), gsub(cbq,gof(rq))]
    wal=[gsub(ZERO,aq), ONE]; oal=[ONE, gsub(ZERO,abq)]
    wcl=[cq, ONE]; ocl=[ONE, cbq]
    P=addL(scaleL(K1, mulL(Sl, mulL(wal,oal))),
           scaleL(K2, addL(scaleL(gof(rq), mulL(mulL(wcl,ocl), El)), negL(scaleL(z0q, mulL(El, mulL(El,El)))))))
    return P, z0q
def q(x):
    x=Fr(x); return "(%d : ℚ)"%x.numerator if x.denominator==1 else "((%d : ℚ)/%d)"%(x.numerator,x.denominator)
def g(a): return "(%s, %s)"%(q(a[0]),q(a[1]))
def rat(x, D): return Fr(round(x*D), D)
if __name__=="__main__":
    p=json.load(open(sys.argv[1])); D=int(sys.argv[2]); m0=Fr(sys.argv[3]); out=sys.argv[4]
    rq=rat(float(p['r']),D); cq=(rat(float(p['c'][0]),D), rat(float(p['c'][1]),D))
    w0q=(rat(float(p['w0'][0]),D), rat(float(p['w0'][1]),D)); aq=(rat(float(p['a'][0]),D), rat(float(p['a'][1]),D))
    P,z0q=make(rq,cq,w0q,aq)
    coeffs=[complex(float(a),float(b)) for a,b in P]
    roots=np.roots(coeffs[::-1]); print("roots |.|:", np.abs(roots))
    B0sq = gnormSq(gsub(w0q,aq))/gnormSq(gsub(ONE,gmul(gconj(aq),w0q)))
    print("margin^2 =", float(1/B0sq), "margin", float(1/B0sq)**0.5, "m0", float(m0), "ok:", B0sq*m0*m0 < 1)
    assert B0sq*m0*m0 < 1
    t=build(P,Fr(0),Fr(0),Fr(1)); print("tree nodes", count(t))
    o=[]; to_lean(t,o)
    json.dump(dict(r=str(rq), c=[str(cq[0]),str(cq[1])], w0=[str(w0q[0]),str(w0q[1])], a=[str(aq[0]),str(aq[1])], m0=str(m0), nodes=count(t)), open(out+".json","w"), indent=1)
    open(out+".lean","w").write("""
namespace SmaleKoebe
def rq : ℚ := %s
def cq : GQ := %s
def w0q : GQ := %s
def aq : GQ := %s
def m0 : ℚ := %s
local notation "l" => QTree.leaf
local notation "n" => QTree.node
def certTree : QTree := %s
end SmaleKoebe
""" % (q(rq), g(cq), g(w0q), g(aq), q(m0), "".join(o)))
    print("written", out)
