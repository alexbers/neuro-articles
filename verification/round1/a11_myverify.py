# Coordinator's independent check of A11's (6,9)-graph: build the voltage lift over SL(2,13),
# check simple, symmetric, 6-regular, and compute the exact girth by BFS from every vertex.
import itertools, collections
P = 13
darts = {0: [(0,(0,9,10,2)),(0,(2,4,3,0)),(1,(1,0,0,1)),(1,(1,4,4,4)),(1,(9,11,1,10)),(1,(5,4,9,10))],
         1: [(1,(1,0,8,1)),(1,(1,0,5,1)),(0,(1,0,0,1)),(0,(4,9,9,1)),(0,(10,2,12,9)),(0,(10,9,4,5))]}
def mm(x, y):
    a,b,c,d = x; e,f,g,h = y
    return ((a*e+b*g)%P, (a*f+b*h)%P, (c*e+d*g)%P, (c*f+d*h)%P)
SL = [m for m in itertools.product(range(P), repeat=4) if (m[0]*m[3]-m[1]*m[2]) % P == 1]
for u in darts:
    for _, A in darts[u]: assert (A[0]*A[3]-A[1]*A[2]) % P == 1
V = [(u, m) for u in (0, 1) for m in SL]; idx = {v: i for i, v in enumerate(V)}
adj = [[idx[(w, mm(m, A))] for (w, A) in darts[u]] for (u, m) in V]
n = len(V)
assert all(len(set(a)) == 6 for a in adj), "multi-edge"
assert all(i not in adj[i] for i in range(n)), "loop"
S = [set(a) for a in adj]
assert all(i in S[j] for i in range(n) for j in adj[i]), "not symmetric"
girth = 10**9
for r in range(n):
    dist = {r: 0}; par = {r: -1}; q = collections.deque([r])
    while q:
        x = q.popleft()
        if 2*dist[x] + 1 >= girth: break
        for y in adj[x]:
            if y not in dist:
                dist[y] = dist[x] + 1; par[y] = x; q.append(y)
            elif par[x] != y:
                girth = min(girth, dist[x] + dist[y] + 1)
print(f"n={n} regular degree 6, simple, symmetric; girth = {girth}")
