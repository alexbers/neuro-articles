# generator files for permutation groups.  usage: gens.py spec n > file
#  cyc | dih | aff:q:k (GF(q) additive + mult by g^((q-1)/k) i.e. subgroup of order k) | afff:q:k (+Frobenius)
#  ab:d1xd2x.. | bicyc:k | mult:u1,u2 (Z_n translations + multipliers)
import sys, itertools
sys.path.insert(0, '.')
from mkinst import GF
spec=sys.argv[1]; n=int(sys.argv[2]); G=[]
if spec=='cyc': G=[[(i+1)%n for i in range(n)]]
elif spec=='dih': G=[[(i+1)%n for i in range(n)],[(-i)%n for i in range(n)]]
elif spec.startswith('mult:'):
    us=[int(x) for x in spec[5:].split(',')]; G=[[(i+1)%n for i in range(n)]]+[[(u*i)%n for i in range(n)] for u in us]
elif spec.startswith('aff:') or spec.startswith('afff:'):
    _,q,k=spec.split(':'); q=int(q); k=int(k); assert q==n; F=GF(q)
    gk=F.exp[(q-1)//k]
    G=[[F.add(x,1) for x in range(q)],[F.mul(gk,x) for x in range(q)]]
    # translations by basis vectors for prime powers
    for i in range(F.m): G.append([F.add(x,F.P[i]) for x in range(q)])
    if spec.startswith('afff'): G.append([F.exp[(F.log[x]*F.p)%(q-1)] if x else 0 for x in range(q)])
elif spec.startswith('affix:'):   # affine group on GF(q) (q prime) plus f fixed points q..q+f-1
    _,q,k,f=spec.split(':'); q=int(q); k=int(k); f=int(f); assert q+f==n
    F=GF(q); gk=F.exp[(q-1)//k]
    G=[[F.add(x,1) if x<q else x for x in range(n)],[F.mul(gk,x) if x<q else x for x in range(n)]]
elif spec.startswith('biaff:'):   # c copies of GF(p) (n = c*p), x->x+1 and x->a x on every copy simultaneously
    _,p,k,c=spec.split(':'); p=int(p); k=int(k); c=int(c); assert p*c==n
    F=GF(p); gk=F.exp[(p-1)//k]
    G=[[ (x//p)*p + F.add(x%p,1) for x in range(n)], [ (x//p)*p + F.mul(gk,x%p) for x in range(n)]]
elif spec.startswith('biaffs:'):  # as biaff plus the cyclic shift of the copies
    _,p,k,c=spec.split(':'); p=int(p); k=int(k); c=int(c); assert p*c==n
    F=GF(p); gk=F.exp[(p-1)//k]
    G=[[ (x//p)*p + F.add(x%p,1) for x in range(n)], [ (x//p)*p + F.mul(gk,x%p) for x in range(n)], [ ((x//p+1)%c)*p + x%p for x in range(n)]]
elif spec.startswith('ab:'):
    dims=[int(x) for x in spec[3:].split('x')]
    def enc(v):
        r=0
        for d,x in zip(dims,v): r=r*d+x
        return r
    els=list(itertools.product(*[range(d) for d in dims]))
    for k in range(len(dims)):
        g=[0]*n
        for v in els:
            w=list(v); w[k]=(w[k]+1)%dims[k]; g[enc(v)]=enc(w)
        G.append(g)
elif spec.startswith('bicyc:'):
    k=int(spec[6:]); m=n//k; G=[[(i//m)*m+((i%m)+1)%m for i in range(n)]]
print(n,len(G))
for g in G: print(' '.join(map(str,g)))
