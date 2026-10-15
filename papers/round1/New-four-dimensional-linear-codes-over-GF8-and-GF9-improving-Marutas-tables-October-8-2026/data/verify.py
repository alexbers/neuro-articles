#!/usr/bin/env python3
"""Independent verifier: reads a multiset-of-points file and computes the exact minimum distance
and weight distribution of the linear code whose generator-matrix columns are the points."""
import sys, itertools
import numpy as np
def gf_tables(q):
    for p in range(2,q+1):
        e=0;t=q
        while t%p==0: t//=p; e+=1
        if t==1 and e>0: break
    poly={4:[1,1],8:[1,1,0],9:[2,1],16:[1,1,0,0]}.get(q,[])
    def dig(a): return [(a//p**i)%p for i in range(e)]
    def und(v): return sum(c*p**i for i,c in enumerate(v))
    ADD=np.zeros((q,q),dtype=np.int64); MUL=np.zeros((q,q),dtype=np.int64)
    for a in range(q):
        for b in range(q):
            da,db=dig(a),dig(b)
            ADD[a,b]=und([(x+y)%p for x,y in zip(da,db)])
            prod=[0]*(2*e)
            for i in range(e):
                for j in range(e): prod[i+j]=(prod[i+j]+da[i]*db[j])%p
            for d in range(2*e-2,e-1,-1):
                c=prod[d]
                if c:
                    prod[d]=0
                    for i in range(e): prod[d-e+i]=(prod[d-e+i]-c*poly[i])%p
            MUL[a,b]=und(prod[:e])
    return ADD,MUL
def load(fn):
    L=open(fn).read().split('\n')
    hdr=dict(kv.split('=') for kv in L[0].split())
    q,k=int(hdr['q']),int(hdr['k'])
    cols=[]
    for line in L[1:]:
        if not line.strip(): continue
        a=list(map(int,line.split())); cols+= [a[1:]]*a[0]
    return q,k,np.array(cols,dtype=np.int64).T, hdr
def weights(q,k,G):
    ADD,MUL=gf_tables(q)
    n=G.shape[1]
    # enumerate all messages with first nonzero coordinate 1
    wd={}
    msgs=[]
    for m in itertools.product(range(q),repeat=k):
        nz=[x for x in m if x]
        if not nz or nz[0]!=1: continue
        msgs.append(m)
    M=np.array(msgs,dtype=np.int64)
    C=np.zeros((len(msgs),n),dtype=np.int64)
    for i in range(k):
        C=ADD[C, MUL[M[:,i][:,None], G[i][None,:]]]
    w=(C!=0).sum(axis=1)
    vals,cnt=np.unique(w,return_counts=True)
    return int(w.min()), dict(zip(map(int,vals),map(int,cnt*(q-1))))
if __name__=='__main__':
    q,k,G,hdr=load(sys.argv[1])
    # rank check via weights: all nonzero messages give nonzero codeword iff min weight>0
    d,wd=weights(q,k,G)
    print('q=%d k=%d n=%d  min distance=%d  (claimed %s)'%(q,k,G.shape[1],d,hdr.get('d')))
    print('weight distribution:',wd)
