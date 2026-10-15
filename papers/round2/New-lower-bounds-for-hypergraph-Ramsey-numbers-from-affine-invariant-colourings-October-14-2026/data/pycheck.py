# independent check: translation invariance mod n + all k-sets through 0, for 2-colouring avoiding red K_a, blue K_b
import sys, itertools
n,a,b=map(int,sys.argv[1:4]); red=set()
for l in open(sys.argv[4]):
    x,y,z=map(int,l.split()); red.add((x,y,z))
def col(t): return tuple(sorted(t)) in red
inv=all(col(((x+1)%n,(y+1)%n,(z+1)%n))==col((x,y,z)) for (x,y,z) in itertools.combinations(range(n),3))
print('translation invariant:',inv, flush=True)
for k,c in ((a,True),(b,False)):
    bad=0
    for S in itertools.combinations(range(1,n),k-1):
        T=(0,)+S
        if all(col(t)==c for t in itertools.combinations(T,3)): bad+=1
    print(f'k={k} colour={"red" if c else "blue"}: monochromatic sets through 0 = {bad}', flush=True)
