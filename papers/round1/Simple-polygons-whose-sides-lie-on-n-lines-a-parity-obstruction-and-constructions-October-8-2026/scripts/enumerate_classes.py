# Exhaustive check of the parity theorem over all commutation classes (simple pseudoline
# arrangements, i.e. wiring diagrams) for n = 3,5,7, via lexicographic normal forms of
# reduced words of w0 in S_n.  Also records the distribution of #components of G and #A.
import sys
from collections import Counter

def run(n):
    N = n*(n-1)//2
    dist = Counter(); distA = Counter(); joint = Counter(); classes = 0
    perm = list(range(1,n+1))      # perm[h] = wire at height h (0-based heights)
    word = []
    # along each wire: list of crossings in time order, crossing id = (u,v) sorted
    cnt = [0]*(n+1)                # crossings made per wire
    order = [[] for _ in range(n+1)]
    def dfs():
        nonlocal classes
        if len(word) == N:
            classes += 1
            # build G: pair positions (1,2),(3,4),... along each wire
            adj = {}
            for w in range(1,n+1):
                seq = order[w]
                for q in range(0,n-1,2):
                    a,b = seq[q], seq[q+1]
                    adj.setdefault(a,[]).append(b); adj.setdefault(b,[]).append(a)
            seen=set(); comps=0
            for v in adj:
                if v in seen: continue
                comps+=1; st=[v]
                while st:
                    x=st.pop()
                    if x in seen: continue
                    seen.add(x); st.extend(adj[x])
            # A-crossings: even position on both wires
            pos = {}
            for w in range(1,n+1):
                for idx,c in enumerate(order[w]):
                    pos.setdefault(c,[]).append(idx+1)
            A = sum(1 for c,ps in pos.items() if ps[0]%2==0 and ps[1]%2==0)
            # per-cycle A count parity check
            seen=set()
            for v in adj:
                if v in seen: continue
                st=[v]; cyc=[]
                while st:
                    x=st.pop()
                    if x in seen: continue
                    seen.add(x); cyc.append(x); st.extend(adj[x])
                ac = sum(1 for c in cyc if pos[c][0]%2==0 and pos[c][1]%2==0)
                assert ac % 2 == 1, ('cycle with even #A', n, word, cyc)
            dist[comps]+=1; distA[A%2]+=1; joint[(comps%2, A%2)]+=1
            return
        for i in range(n-1):           # letter i: swap heights i,i+1 (0-based)
            u,v = perm[i], perm[i+1]
            if u > v: continue         # already crossed (reduced word)
            # lexicographic normal form pruning
            ok = True
            for t in range(len(word)-1,-1,-1):
                j = word[t]
                if abs(j-i) >= 2:
                    if j > i: ok=False; break
                else:
                    break
            if not ok: continue
            word.append(i); perm[i],perm[i+1]=v,u
            c=(u,v); order[u].append(c); order[v].append(c)
            dfs()
            order[u].pop(); order[v].pop()
            perm[i],perm[i+1]=u,v; word.pop()
    sys.setrecursionlimit(10000)
    dfs()
    r=(n-1)//2
    print(f'n={n}: commutation classes={classes}; #components distribution={dict(sorted(dist.items()))};',
          f'#A parity distribution={dict(distA)}; predicted parity={(r*(r+1)//2)%2};',
          f'(comps mod 2, A mod 2) joint={dict(joint)}')

for n in (3,5,7):
    run(n)
