# Lean certificate for an arbitrary 2-colouring of the triples of {0..n-1} (no symmetry used):
# pruned kernel search over all increasing tuples.  usage: mklean_full.py n A B redfile out.lean Name
import sys, itertools
n,A,B=map(int,sys.argv[1:4]); red=set()
for l in open(sys.argv[4]):
    x,y,z=map(int,l.split()); red.add(tuple(sorted((x,y,z))))
M=0
for t in red: M|=1<<(t[0]*n*n+t[1]*n+t[2])
name=sys.argv[6]; V='abcdefghij'
def check_fn(k, colour, nm):
    lit=(lambda t: f'col {t[0]} {t[1]} {t[2]}') if colour else (lambda t: f'!(col {t[0]} {t[1]} {t[2]})')
    vs=[f'v{i}' for i in range(k)]
    expr=None
    for j in range(k-1,1,-1):
        new=[lit((x,y,vs[j])) for x,y in itertools.combinations(vs[:j],2)]
        cond=' && '.join([f'{vs[j-1]} < {vs[j]}']+new)
        inner = f'!({cond})' if expr is None else f'!({cond}) || {expr}'
        expr=f'((List.range {n}).all fun {vs[j]} => {inner})'
    return f'def {nm} : Bool :=\n  (List.range {n}).all fun v0 => (List.range {n}).all fun v1 => !(v0 < v1) || {expr}\n'
def noK(k, colour, nm, chk, defnm):
    vs=V[:k]; trips=list(itertools.combinations(vs,3))
    s=f'theorem {nm} : ¬ {defnm} {n} col {"true" if colour else "false"} := by\n'
    s+=f'  rintro ⟨{", ".join(vs)}, ' + ', '.join(f'l{i}' for i in range(k-1)) + ', hn, ' + ', '.join(f'h{j}' for j in range(len(trips))) + '⟩\n'
    s+=f'  have hc := {chk}_ok\n  unfold {chk} at hc\n'
    s+='  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true\',\n    Bool.and_eq_false_iff, decide_eq_false_iff_not] at hc\n'
    s+=f'  rcases hc {vs[0]} (by omega) {vs[1]} (by omega) with h | h\n  · omega\n'
    for i in range(2,k):
        s+=f'  rcases h {vs[i]} (by omega) with h | h\n'
        if i<k-1: s+='  · simp_all\n'
    s+='  all_goals simp_all\n'
    return s
def mono_def(k, nm):
    vs=V[:k]
    lt=' ∧ '.join(f'{vs[i]} < {vs[i+1]}' for i in range(k-1))
    cols=' ∧ '.join(f'col {t[0]} {t[1]} {t[2]} = χ' for t in itertools.combinations(vs,3))
    return f'''/-- `col` (a colouring of the triples `x<y<z` of `{{0,…,N-1}}`) contains a `K_{k}^(3)` of colour `χ`. -/
def {nm} (N : Nat) (col : Nat → Nat → Nat → Bool) (χ : Bool) : Prop :=
  ∃ {" ".join(vs)} : Nat, {lt} ∧ {vs[-1]} < N ∧ {cols}
'''
L=f'''set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace {name}

/-- the colouring: the triple `x<y<z` of `{{0,…,{n-1}}}` is red iff bit `x*{n*n}+y*{n}+z` of `Fmask` is 1 -/
def Fmask : Nat := {hex(M)}
def col (x y z : Nat) : Bool := Fmask.testBit (x * {n*n} + y * {n} + z)

{check_fn(A,True,'chkRed')}
{check_fn(B,False,'chkBlue')}
theorem chkRed_ok : chkRed = true := by decide +kernel
theorem chkBlue_ok : chkBlue = true := by decide +kernel

{mono_def(A,'HasMonoK'+str(A))}{'' if A==B else mono_def(B,'HasMonoK'+str(B))}
{noK(A,True,'noRedK','chkRed','HasMonoK'+str(A))}
{noK(B,False,'noBlueK','chkBlue','HasMonoK'+str(B))}
/-- **R({A},{B};3) ≥ {n+1}** -/
theorem main : ∃ col : Nat → Nat → Nat → Bool, ¬ HasMonoK{A} {n} col true ∧ ¬ HasMonoK{B} {n} col false :=
  ⟨col, noRedK, noBlueK⟩

end {name}

#print axioms {name}.main
'''
open(sys.argv[5],'w').write(L)
print('written',sys.argv[5])
