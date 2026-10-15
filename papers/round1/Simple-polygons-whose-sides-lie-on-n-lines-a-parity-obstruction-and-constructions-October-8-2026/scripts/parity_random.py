# Random reduced words of w0 (random sorting networks): check components parity and per-cycle #A.
import random
def rand_word(n, rng):
    perm=list(range(1,n+1)); word=[]; order=[[] for _ in range(n+1)]
    while True:
        asc=[i for i in range(n-1) if perm[i]<perm[i+1]]
        if not asc: break
        i=rng.choice(asc); u,v=perm[i],perm[i+1]; perm[i],perm[i+1]=v,u
        c=(u,v); order[u].append(c); order[v].append(c); word.append(i)
    return order
def analyse(n, order):
    adj={}; pos={}
    for w in range(1,n+1):
        for idx,c in enumerate(order[w]): pos.setdefault(c,[]).append(idx+1)
        for q in range(0,n-1,2):
            a,b=order[w][q],order[w][q+1]
            adj.setdefault(a,[]).append(b); adj.setdefault(b,[]).append(a)
    seen=set(); comps=0; allodd=True
    for v in adj:
        if v in seen: continue
        comps+=1; st=[v]; cyc=[]
        while st:
            x=st.pop()
            if x in seen: continue
            seen.add(x); cyc.append(x); st.extend(adj[x])
        ac=sum(1 for c in cyc if pos[c][0]%2==0 and pos[c][1]%2==0)
        if ac%2==0: allodd=False
    return comps, allodd
rng=random.Random(12345)
for n in range(3,24,2):
    r=(n-1)//2; pred=(r*(r+1)//2)%2
    from collections import Counter
    dist=Counter(); ok=True; T=3000 if n<=13 else 500
    for _ in range(T):
        comps,allodd=analyse(n, rand_word(n,rng))
        dist[comps]+=1
        if comps%2!=pred or not allodd: ok=False
    print(f'n={n}: {T} random words, parity/per-cycle OK={ok}, components seen={dict(sorted(dist.items()))}')
