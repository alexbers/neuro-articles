#!/usr/bin/env python3
"""Independent reconstruction of W_0 and W_{1/2} over GF(q^3) for odd prime powers q (including non-prime q),
written from Definition 4.1 of the paper during the review of October 8, 2026; FFT autocorrelation with exact rounding.
Usage: python3 twin_check_gf.py range 3 251   (all odd prime powers in the range; log: twin_family_check_q_le_251.log)
       python3 twin_check_gf.py small          (q<=19: also scans all c in F, tests inequivalence to W_0, compares with certificates.json)"""
import numpy as np, json, sys, time
import os; D=os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
C=json.load(open(D+'/data/certificates.json'))
def pk(q):
    for p in range(2,q+1):
        if q%p==0:
            k=0;t=q
            while t%p==0: t//=p;k+=1
            assert t==1; return p,k
def primes_of(n):
    f=set();d=2
    while d*d<=n:
        while n%d==0: f.add(d); n//=d
        d+=1
    if n>1: f.add(n)
    return f
def polmulmod(a,b,h,p):  # a,b lists len d (coeffs x^0..), h monic list len d+1
    d=len(h)-1; r=[0]*(2*d-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b): r[i+j]=(r[i+j]+x*y)%p
    for e in range(2*d-2,d-1,-1):
        c=r[e]
        if c:
            for j in range(d+1): r[e-d+j]=(r[e-d+j]-c*h[j])%p
    return r[:d]
def polpow(a,e,h,p):
    d=len(h)-1; r=[1]+[0]*(d-1)
    while e:
        if e&1: r=polmulmod(r,a,h,p)
        a=polmulmod(a,a,h,p); e>>=1
    return r
def find_primitive(p,d,N):
    one=[1]+[0]*(d-1); x=[0,1]+[0]*(d-2); pr=primes_of(N)
    import itertools
    # constant term of a primitive polynomial is (-1)^d * N(alpha), and N(alpha) must generate GF(p)^*
    prim_roots=[g for g in range(1,p) if all(pow(g,(p-1)//r,p)!=1 for r in primes_of(p-1))] if p>2 else [1]
    c0s=[((-1)**d*g)%p for g in prim_roots]
    for rest in itertools.product(range(p),repeat=d-1):
      for c0 in c0s:
        tail=(c0,)+rest
        h=list(tail)+[1]
        if polpow(x,N,h,p)!=one: continue
        if all(polpow(x,N//r,h,p)!=one for r in pr): return h
    raise RuntimeError
def build_tables(q):
    p,k=pk(q); d=3*k; N=q**3-1; h=find_primitive(p,d,N)
    M=np.zeros((d,d),dtype=np.int64)
    for j in range(d-1): M[j+1,j]=1
    for j in range(d): M[j,d-1]=(-h[j])%p
    B=4096
    V=np.zeros((d,B),dtype=np.int64); V[0,0]=1
    for r in range(1,B): V[:,r]=(M@V[:,r-1])%p
    MB=np.eye(d,dtype=np.int64); Mp=M.copy(); e=B
    while e:
        if e&1: MB=(MB@Mp)%p
        Mp=(Mp@Mp)%p; e>>=1
    nb=N//B+2; out=np.empty((nb*B,d),dtype=np.int16); out[:B]=V.T
    for j in range(1,nb):
        V=(MB@V)%p; out[j*B:(j+1)*B]=V.T
    assert (out[N]==out[0]).all()
    anti=out[:N]
    w=p**np.arange(d,dtype=np.int64); packed=np.zeros(N,dtype=np.int64)
    for j in range(d): packed+=anti[:,j].astype(np.int64)*w[j]
    log=np.full(q**3,-1,dtype=np.int64); log[packed]=np.arange(N)
    assert (log[packed]>=0).all() and len(np.unique(packed))==N
    return p,k,d,N,h,anti,packed,log,w
def paf_fft(a):
    n=len(a); F=np.fft.rfft(a.astype(float)); r=np.fft.irfft(np.abs(F)**2,n)
    ri=np.rint(r); assert np.abs(r-ri).max()<1e-3; return ri.astype(np.int64)
def is_proper(a):
    n=len(a); s=np.nonzero(a)[0]
    return all(len(set((s%e).tolist()))>1 for e in range(2,n+1) if n%e==0)
def twin(q, tabs, cs=None):
    p,k,d,N,h,anti,packed,log,w=tabs; m=q*q+q+1
    i=np.arange(m); y=anti[i].astype(np.int64)
    T=(y+anti[(i*q)%N].astype(np.int64)+anti[(i*q*q)%N].astype(np.int64))%p         # Tr(y) as vectors
    Tp=T@w; Tlog=log[Tp]; Tz=(Tp==0)
    assert ((Tlog[~Tz]%m)==0).all()                       # Tr(y) in F
    def W_from_cT(cT):                                    # cT: vectors c*Tr(y)
        v=(cT-y)%p; vp=v@w; vz=(vp==0); vl=log[np.where(vz,1,vp)]
        e=(vl*m+Tlog)%N                                   # log of N(v)*T
        W=np.where(Tz|vz,0,1-2*((e//m)%2))
        return W.astype(np.int64)
    half=(p+1)//2                                         # 1/2 in GF(p) ⊂ F
    W0=W_from_cT(np.zeros_like(T)); W1=W_from_cT((half*T)%p)
    res={}
    for nm,W in (('W0',W0),('W1/2',W1)):
        r=paf_fft(W); res[nm]=(r[0]==q*q and not r[1:].any())
    res['same_supp']=bool(((W0!=0)==(W1!=0)).all()); res['W1!=±W0']=not((W1==W0).all() or (W1==-W0).all())
    A=np.empty(2*m,dtype=np.int64); kk=np.arange(2*m)
    A[kk%2==0]=(W0[kk[kk%2==0]%m]+W1[kk[kk%2==0]%m])//2
    A[kk%2==1]=(W0[kk[kk%2==1]%m]-W1[kk[kk%2==1]%m])//2
    rA=paf_fft(A); res['A_CW']=(rA[0]==q*q and not rA[1:].any()); res['A_proper']=is_proper(A)
    extra={}
    if cs=='scan':   # all c in F: c = 0 or alpha^(m*j)
        good=[]
        for j in range(q-1):
            cT=anti[(m*j+Tlog)%N].astype(np.int64); cT[Tz]=0
            W=W_from_cT(cT); r=paf_fft(W)
            if r[0]==q*q and not r[1:].any(): good.append(j)
        W=W_from_cT(np.zeros_like(T)); r=paf_fft(W); c0=(r[0]==q*q and not r[1:].any())
        # which j is 1/2: alpha^(mj) = inverse of 2 = vector 2*e0
        two=np.zeros(d,dtype=np.int64); two[0]=2%p; jhalf=((-log[two@w])%N)//m
        extra['c_scan']=(c0,good,'j(1/2)=',jhalf)
    if cs=='equiv':  # W1 = ±W0(t x + s)?
        found=None
        for t in range(1,m):
            if np.gcd(t,m)!=1: continue
            Wt=W0[(t*np.arange(m))%m]
            for s in range(m):
                Z=np.roll(Wt,-s)
                if (Z==W1).all() or (Z==-W1).all(): found=(t,s); break
            if found: break
        extra['equiv_to_W0']=found
    return res,A,extra
if __name__=='__main__':
    mode=sys.argv[1]
    if mode=='small':
        for q in (3,5,7,9,11,13,17,19):
            t0=time.time(); tabs=build_tables(q)
            res,A,extra=twin(q,tabs,'scan' if q in (5,7,11,13) else ('equiv' if q in (3,9,17,19) else None))
            if q in (5,7,11): _,_,ex2=twin(q,tabs,'equiv'); extra.update(ex2)
            cert=np.array(C[f'cwFam{2*(q*q+q+1)}']['seq']); n=len(A); eq=None
            for t in range(1,n):
                if np.gcd(t,n)!=1: continue
                At=A[(t*np.arange(n))%n]
                for s in range(n):
                    Z=np.roll(At,-s)
                    if (Z==cert).all(): eq=(t,s,'+'); break
                    if (Z==-cert).all(): eq=(t,s,'-'); break
                if eq: break
            print(f"q={q} h={tabs[4]} {res} cert_equiv(t,s,sign)={eq} {extra} ({time.time()-t0:.1f}s)",flush=True)
    else:
        lo,hi=int(sys.argv[2]),int(sys.argv[3])
        for q in range(lo,hi+1):
            if q%2==0: continue
            try: p,k=pk(q)
            except AssertionError: continue
            t0=time.time(); tabs=build_tables(q); res,A,_=twin(q,tabs)
            print(f"q={q} m={q*q+q+1} {res} ({time.time()-t0:.1f}s)",flush=True)
