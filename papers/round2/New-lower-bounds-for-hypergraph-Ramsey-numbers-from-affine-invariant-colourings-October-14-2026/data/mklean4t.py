# Lean certificate for a translation-invariant 2-colouring of the 4-subsets of {0..n-1} with no red K_A^(4)
# and no blue K_B^(4).  usage: mklean4.py n A B redfile out.lean Name
import sys, itertools
n,A,B=map(int,sys.argv[1:4]); red=set()
for l in open(sys.argv[4]):
    t=tuple(sorted(map(int,l.split()))); red.add(t)
def col(t): return tuple(sorted(t)) in red
assert all(col(tuple((x+1)%n for x in t))==col(t) for t in itertools.combinations(range(n),4))
rows=[0]*n
for d in itertools.combinations(range(1,n),3):
    if col((0,)+d): rows[d[0]]|=1<<(d[1]*n+d[2])
name=sys.argv[6]
def tree(lo, hi):
    # value for d in [lo,hi)
    if hi-lo==1: return hex(rows[lo])
    mid=(lo+hi)//2
    return f"if d < {mid} then ({tree(lo,mid)}) else ({tree(mid,hi)})"
V='abcdefghij'
def check_fn(k, colour, nm):
    lit=(lambda t: 'col %s %s %s %s'%t) if colour else (lambda t: '!(col %s %s %s %s)'%t)
    vs=['0']+[f'v{i}' for i in range(1,k)]
    expr=None
    for j in range(k-1,2,-1):
        new=[lit(tuple(c)+(vs[j],)) for c in itertools.combinations(vs[:j],3)]
        cond=' && '.join([f'{vs[j-1]} < {vs[j]}']+new)
        inner = f'!({cond})' if expr is None else f'!({cond}) || {expr}'
        expr=f'((List.range {n}).all fun {vs[j]} => {inner})'
    return f'def {nm} (v1 : Nat) : Bool :=\n  (List.range {n}).all fun v2 => !(v1 < v2) || {expr}\n'
def per_v1(chk, pre):
    out=[]
    for v in range(1,n):
        out.append(f'theorem {pre}{v} : {chk} {v} = true := by decide +kernel')
    out.append(f'theorem {chk}_all (v : Nat) (h0 : 0 < v) (hv : v < {n}) : {chk} v = true :=')
    out.append('  match v, h0, hv with')
    out.append('  | 0, h, _ => absurd h (Nat.lt_irrefl 0)')
    for v in range(1,n): out.append(f'  | {v}, _, _ => {pre}{v}')
    out.append(f'  | v + {n}, _, h => absurd h (by omega)')
    return '\n'.join(out)+'\n'

def no0(k, colour, nm, chk):
    vs=['0']+[f'x{i}' for i in range(1,k)]
    hyps=['(h1 : 0 < x1)']+[f'(h{i} : x{i-1} < x{i})' for i in range(2,k)]+[f'(hn : x{k-1} < {n})']
    quads=list(itertools.combinations(vs,4))
    rs=[f'(r{j} : col {t[0]} {t[1]} {t[2]} {t[3]} = {"true" if colour else "false"})' for j,t in enumerate(quads)]
    s=f'theorem {nm} ({" ".join(vs[1:])} : Nat) {" ".join(hyps)}\n    {" ".join(rs)} : False := by\n'
    s+=f'  have h := {chk}_all x1 (by omega) (by omega)\n  unfold {chk} at h\n'
    s+='  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true\',\n    Bool.and_eq_false_iff, decide_eq_false_iff_not] at h\n'
    s+='  rcases h x2 (by omega) with h | h\n  · omega\n'
    for i in range(3,k):
        s+=f'  rcases h x{i} (by omega) with h | h\n'
        if i<k-1: s+='  · simp_all\n'
    s+='  all_goals simp_all\n'
    return s
def mono_def(k, nm):
    vs=V[:k]
    lt=' ∧ '.join(f'{vs[i]} < {vs[i+1]}' for i in range(k-1))
    cols=' ∧ '.join('col %s %s %s %s = χ'%t for t in itertools.combinations(vs,4))
    return f'''/-- `col` (a colouring of the 4-sets `x<y<z<w` of `{{0,…,N-1}}`) contains a `K_{k}^(4)` of colour `χ`. -/
def {nm} (N : Nat) (col : Nat → Nat → Nat → Nat → Bool) (χ : Bool) : Prop :=
  ∃ {" ".join(vs)} : Nat, {lt} ∧ {vs[-1]} < N ∧ {cols}
'''
def reduce_thm(k, colour, nm, no0nm, defnm):
    vs=V[:k]; quads=list(itertools.combinations(vs,4))
    s=f'theorem {nm} : ¬ {defnm} {n} col {"true" if colour else "false"} := by\n'
    s+=f'  rintro ⟨{", ".join(vs)}, ' + ', '.join(f'l{i}' for i in range(k-1)) + ', hn, ' + ', '.join(f'h{j}' for j in range(len(quads))) + '⟩\n'
    a=vs[0]
    for j,t in enumerate(quads):
        s+=f'  have s{j} := col_shift {a} {t[0]} {t[1]} {t[2]} {t[3]} (by omega) (by omega) (by omega) (by omega)\n'
    s+='  simp only [Nat.sub_self] at ' + ' '.join(f's{j}' for j in range(len(quads))) + '\n'
    args=' '.join(f'({v} - {a})' for v in vs[1:])
    s+=f'  exact {no0nm} {args} ' + ' '.join('(by omega)' for _ in range(k)) + ' ' + ' '.join(f'(by rw [s{j}, h{j}])' for j in range(len(quads))) + '\n'
    return s
L=f'''set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace {name}

/-- `row d₁` encodes the colours of the 4-sets `{{0, d₁, d₂, d₃}}` (0 < d₁ < d₂ < d₃ < {n}): bit `d₂*{n}+d₃`
(a binary decision tree on `d₁`, for fast kernel evaluation). -/
def row (d : Nat) : Nat := {tree(0, n)}

/-- The colouring of the 4-set `x < y < z < w` of `{{0,…,{n-1}}}`: the colour of `{{0, y-x, z-x, w-x}}`
(true = red); translation invariant by construction. -/
def col (x y z w : Nat) : Bool := (row (y - x)).testBit ((z - x) * {n} + (w - x))

{check_fn(A,True,'chkRed')}
{check_fn(B,False,'chkBlue')}
{per_v1('chkRed','cr')}
{per_v1('chkBlue','cb')}

{no0(A,True,'noRed0','chkRed')}
{no0(B,False,'noBlue0','chkBlue')}
/-- translation: the colour of `x<y<z<w` only depends on the differences to `x` -/
theorem col_shift (a x y z w : Nat) (hx : a ≤ x) (hxy : x < y) (hyz : y < z) (hzw : z < w) :
    col (x - a) (y - a) (z - a) (w - a) = col x y z w := by
  unfold col
  rw [show y - a - (x - a) = y - x by omega, show z - a - (x - a) = z - x by omega,
    show w - a - (x - a) = w - x by omega]

{mono_def(A,'HasMonoK'+str(A))}{'' if A==B else mono_def(B,'HasMonoK'+str(B))}
{reduce_thm(A,True,'noRedK','noRed0','HasMonoK'+str(A))}
{reduce_thm(B,False,'noBlueK','noBlue0','HasMonoK'+str(B))}
/-- **R({A},{B};4) ≥ {n+1}**: a red/blue colouring of the 4-subsets of `{{0,…,{n-1}}}` with no red
`K_{A}^(4)` and no blue `K_{B}^(4)`. -/
theorem main : ∃ col : Nat → Nat → Nat → Nat → Bool, ¬ HasMonoK{A} {n} col true ∧ ¬ HasMonoK{B} {n} col false :=
  ⟨col, noRedK, noBlueK⟩

end {name}

#print axioms {name}.main
'''
open(sys.argv[5],'w').write(L)
print('written',sys.argv[5])
