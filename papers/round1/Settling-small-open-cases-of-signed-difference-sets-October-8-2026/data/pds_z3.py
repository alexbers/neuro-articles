# z3 search for regular PDS with parameters (64,18,2,6) [NLS type] and (64,21,8,6) [LS type] in abelian groups of order 64.
# Model: boolean x_g for g != 0, x_{-g} = x_g, |S| = k, for each y != 0: #{(a,b): a,b in S, a-b=y} = lam if y in S else mu.
import sys, math, itertools, time
from z3 import *
def run(G,k,lam,mu,timeout_s):
    v=math.prod(G); E=list(itertools.product(*[range(m) for m in G])); ix={t:i for i,t in enumerate(E)}
    z=tuple([0]*len(G)); neg=lambda a: tuple((-x)%m for x,m in zip(a,G)); sub=lambda a,b: tuple((x-y)%m for x,y,m in zip(a,b,G))
    x=[Bool('x%d'%i) for i in range(v)]
    s=Solver(); s.set('timeout',timeout_s*1000)
    s.add(Not(x[0]))
    for e in E:
        if e!=z: s.add(x[ix[e]]==x[ix[neg(e)]])
    s.add(PbEq([(x[i],1) for i in range(1,v)],k))
    prod={}
    def pr(a,b):
        key=(min(a,b),max(a,b))
        if key not in prod: prod[key]=And(x[key[0]],x[key[1]])
        return prod[key]
    for y in E:
        if y==z: continue
        terms=[(pr(ix[a],ix[sub(a,y)]),1) for a in E if a!=z and sub(a,y)!=z]
        # count = lam if x_y else mu  <=> count = mu + (lam-mu) x_y
        d=lam-mu
        if d>=0: s.add(PbEq(terms+[(Not(x[ix[y]]),d)], mu+d))
        else: s.add(PbEq(terms+[(x[ix[y]],-d)], mu))
    t0=time.time(); r=s.check(); dt=time.time()-t0
    out=f'{r} G={G} params=({v},{k},{lam},{mu}) time={dt:.1f}s'
    if r==sat:
        m=s.model(); Sset=[E[i] for i in range(v) if is_true(m[x[i]])]
        from collections import Counter
        cnt=Counter(sub(a,b) for a in Sset for b in Sset if a!=b)
        ok=len(Sset)==k and all(cnt[e]==(lam if e in set(Sset) else mu) for e in E if e!=z)
        out+=f' verified={ok} S={Sset}'
    return out
groups=[(2,2,2,2,2,2),(2,2,2,2,4),(2,2,2,8),(2,2,4,4),(2,4,8),(4,4,4),(4,16),(8,8),(2,2,16),(2,32),(64,)]
which=sys.argv[1]
params=(18,2,6) if which=='nls' else (21,8,6)
for G in groups:
    print(run(G,*params,1800),flush=True)
