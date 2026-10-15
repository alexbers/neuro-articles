# Lean certificate with pruned (clique-extension) kernel checks for a translation-invariant 2-colouring of the
# triples of {0..n-1} with no red K_A^(3) and no blue K_B^(3).   usage: mklean_prune.py n A B redfile out.lean Name
import sys, itertools
n,A,B=map(int,sys.argv[1:4]); red=set()
for l in open(sys.argv[4]):
    x,y,z=map(int,l.split()); red.add(tuple(sorted((x,y,z))))
def col(t): return tuple(sorted(t)) in red
assert all(col(((x+1)%n,(y+1)%n,(z+1)%n))==col((x,y,z)) for (x,y,z) in itertools.combinations(range(n),3))
M=0
for d1 in range(1,n):
    for d2 in range(d1+1,n):
        if col((0,d1,d2)): M|=1<<(d1*n+d2)
name=sys.argv[6]
def check_fn(k, colour, nm):
    # vertices 0 < v1 < v2 < ... < v_{k-1}; at level j>=2 require v_{j-1}<v_j and all triples {x,y,v_j} (x<y earlier) coloured
    lit=(lambda t: f'col {t[0]} {t[1]} {t[2]}') if colour else (lambda t: f'!(col {t[0]} {t[1]} {t[2]})')
    vs=['0']+[f'v{i}' for i in range(1,k)]
    expr=None
    for j in range(k-1,1,-1):
        new=[lit((x,y,vs[j])) for x,y in itertools.combinations(vs[:j],2)]
        cond=' && '.join([f'{vs[j-1]} < {vs[j]}']+new)
        inner = f'!({cond})' if expr is None else f'!({cond}) || {expr}'
        expr=f'((List.range {n}).all fun {vs[j]} => {inner})'
    return f'def {nm} : Bool :=\n  (List.range {n}).all fun v1 => v1 == 0 || {expr}\n'
L=f'''set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace {name}

/-- `Fmask` encodes the colour of the triples `{{0, d₁, d₂}}` (0 < d₁ < d₂ < {n}): bit `d₁*{n}+d₂` (1 = red). -/
def Fmask : Nat := {hex(M)}

/-- The colouring of the triple `x < y < z` of `{{0,…,{n-1}}}`: the colour of `{{0, y-x, z-x}}`
(true = red). It is translation invariant by construction. -/
def col (x y z : Nat) : Bool := Fmask.testBit ((y - x) * {n} + (z - x))

/-- pruned search: no red `K_{A}^(3)` containing the vertex 0 -/
{check_fn(A,True,'chkRed')}
/-- pruned search: no blue `K_{B}^(3)` containing the vertex 0 -/
{check_fn(B,False,'chkBlue')}
theorem chkRed_ok : chkRed = true := by decide +kernel
theorem chkBlue_ok : chkBlue = true := by decide +kernel

end {name}
'''
open(sys.argv[5],'w').write(L)
print('written',sys.argv[5])
