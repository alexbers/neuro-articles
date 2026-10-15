# Generate the Lean main part (soundness of pruned checks + translation reduction + statement) for (A,B), n.
import sys, itertools
n,A,B=map(int,sys.argv[1:4]); out=sys.argv[4]; name=sys.argv[5]
V='abcdefghij'
def no0(k, colour, nm, chk):
    vs=['0']+[f'x{i}' for i in range(1,k)]
    params=' '.join(vs[1:])
    hyps=['(h1 : 0 < x1)']+[f'(h{i} : x{i-1} < x{i})' for i in range(2,k)]+[f'(hn : x{k-1} < {n})']
    trips=list(itertools.combinations(vs,3))
    rs=[f'(r{j} : col {t[0]} {t[1]} {t[2]} = {"true" if colour else "false"})' for j,t in enumerate(trips)]
    s=f'theorem {nm} ({params} : Nat) {" ".join(hyps)}\n    {" ".join(rs)} : False := by\n'
    s+=f'  have hc := {chk}_ok\n  unfold {chk} at hc\n'
    s+='  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true\',\n    Bool.and_eq_false_iff, decide_eq_false_iff_not] at hc\n'
    s+=f'  rcases hc x1 (by omega) with h | h\n  · omega\n'
    for i in range(2,k):
        s+=f'  rcases h x{i} (by omega) with h | h\n'
        if i<k-1: s+='  · simp_all\n'
    s+='  all_goals simp_all\n'
    return s
def mono_def(k, nm):
    vs=V[:k]
    lt=' ∧ '.join(f'{vs[i]} < {vs[i+1]}' for i in range(k-1))
    cols=' ∧ '.join(f'col {t[0]} {t[1]} {t[2]} = χ' for t in itertools.combinations(vs,3))
    return f'''/-- `col` (a colouring of the triples `x<y<z` of `{{0,…,N-1}}`) contains a `K_{k}^(3)` of colour `χ`:
{k} vertices all of whose triples have colour `χ`. -/
def {nm} (N : Nat) (col : Nat → Nat → Nat → Bool) (χ : Bool) : Prop :=
  ∃ {" ".join(vs)} : Nat, {lt} ∧ {vs[-1]} < N ∧ {cols}
'''
def reduce_thm(k, colour, nm, no0nm, defnm):
    vs=V[:k]
    s=f'theorem {nm} : ¬ {defnm} {n} col {"true" if colour else "false"} := by\n'
    s+=f'  rintro ⟨{", ".join(vs)}, ' + ', '.join(f'l{i}' for i in range(k-1)) + ', hn, ' + ', '.join(f'h{j}' for j,_ in enumerate(itertools.combinations(vs,3))) + '⟩\n'
    a=vs[0]
    for j,t in enumerate(itertools.combinations(vs,3)):
        s+=f'  have s{j} := col_shift {a} {t[0]} {t[1]} {t[2]} (by omega) (by omega) (by omega)\n'
    s+='  simp only [Nat.sub_self] at ' + ' '.join(f's{j}' for j,_ in enumerate(itertools.combinations(vs,3))) + '\n'
    args=' '.join(f'({v} - {a})' for v in vs[1:])
    s+=f'  exact {no0nm} {args} ' + ' '.join('(by omega)' for _ in range(k)) + ' ' + ' '.join(f'(by rw [s{j}, h{j}])' for j,_ in enumerate(itertools.combinations(vs,3))) + '\n'
    return s
L=f'namespace {name}\n\n'
L+=no0(A,True,'noRed0','chkRed')+'\n'+no0(B,False,'noBlue0','chkBlue')+'\n'
L+='''/-- translation: the colour of `x<y<z` only depends on `y-x, z-x` -/
theorem col_shift (a x y z : Nat) (hx : a ≤ x) (hxy : x < y) (hyz : y < z) :
    col (x - a) (y - a) (z - a) = col x y z := by
  unfold col
  rw [show y - a - (x - a) = y - x by omega, show z - a - (x - a) = z - x by omega]

'''
L+=mono_def(A,'HasMonoK'+str(A)) + ('\n'+mono_def(B,'HasMonoK'+str(B)) if B!=A else '') + '\n'
L+=reduce_thm(A,True,'noRedK','noRed0','HasMonoK'+str(A))+'\n'
L+=reduce_thm(B,False,'noBlueK','noBlue0','HasMonoK'+str(B))+'\n'
L+=f'''/-- **R({A},{B};3) ≥ {n+1}**: there is a red/blue colouring of the triples of `{{0,…,{n-1}}}` with no red
`K_{A}^(3)` and no blue `K_{B}^(3)`. -/
theorem main : ∃ col : Nat → Nat → Nat → Bool, ¬ HasMonoK{A} {n} col true ∧ ¬ HasMonoK{B} {n} col false :=
  ⟨col, noRedK, noBlueK⟩

end {name}

#print axioms {name}.main
'''
open(out,'w').write(L)
