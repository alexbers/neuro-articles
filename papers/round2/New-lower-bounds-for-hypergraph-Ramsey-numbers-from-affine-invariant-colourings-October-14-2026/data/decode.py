import sys
sol,orb,out=sys.argv[1:4]
lits=[int(x) for l in open(sol) if l.startswith('v') for x in l.split()[1:]]
true={x for x in lits if x>0}
c=0
with open(out,'w') as f:
    for l in open(orb):
        x,y,z,o=map(int,l.split())
        if (o+1) in true: f.write(f'{x} {y} {z}\n'); c+=1
print(out,'red',c)
