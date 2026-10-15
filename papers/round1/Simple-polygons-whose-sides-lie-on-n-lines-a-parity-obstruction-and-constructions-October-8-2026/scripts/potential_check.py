# Brute-force check of the potential function
#   Phi(pi) = sum_h [pi(h) odd]*floor(h/2) + #{inversions (u<v): u odd, v even}
# Claim: for every permutation pi of 1..n and every ascent i (pi(i) < pi(i+1)),
#   Phi(pi s_i) - Phi(pi) == [i-u odd]*[i+1-v odd]  (mod 2),  u=pi(i), v=pi(i+1).
# Then #A(w) == Phi(w0) - Phi(id) == r(r+1)/2 for every reduced word w of w0.
import itertools
def Phi(p):  # p is a tuple, p[h-1] = wire at height h
    n=len(p); s=0
    for h in range(1,n+1):
        if p[h-1]%2==1: s+= h//2
    for a in range(n):
        for b in range(a+1,n):
            if p[a]>p[b] and p[b]%2==1 and p[a]%2==0: s+=1
    return s%2
for n in range(2,9):
    bad=0; checked=0
    for p in itertools.permutations(range(1,n+1)):
        for i in range(1,n):
            u,v=p[i-1],p[i]
            if u<v:
                q=list(p); q[i-1],q[i]=v,u
                lhs=(Phi(tuple(q))-Phi(p))%2
                rhs=((i-u)%2)*((i+1-v)%2)
                checked+=1
                if lhs!=rhs: bad+=1
    r=(n-1)//2
    idp=tuple(range(1,n+1)); w0=tuple(range(n,0,-1))
    print(f'n={n}: ascents checked={checked}, violations={bad}, Phi(w0)-Phi(id) mod 2 = {(Phi(w0)-Phi(idp))%2}',
          f', r(r+1)/2 mod 2 = {(r*(r+1)//2)%2}' if n%2==1 else '')
