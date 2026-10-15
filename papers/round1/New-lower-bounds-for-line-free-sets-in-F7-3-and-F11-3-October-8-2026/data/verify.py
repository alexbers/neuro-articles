import sys, itertools
p=int(sys.argv[1]); n=int(sys.argv[2])
S=set(int(x) for x in open(sys.argv[3]).read().split())
def dec(x): return tuple((x//p**i)%p for i in range(n))
P=set(dec(x) for x in S)
assert len(P)==len(S)
bad=0
for c in itertools.product(range(p),repeat=n):
  for d in itertools.product(range(p),repeat=n):
    if not any(d): continue
    if all(tuple((c[i]+t*d[i])%p for i in range(n)) in P for t in range(p)): bad+=1
print("size",len(P),"full lines (with multiplicity)",bad)
