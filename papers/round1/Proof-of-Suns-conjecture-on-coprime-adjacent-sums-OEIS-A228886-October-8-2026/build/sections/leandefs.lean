/-- The cyclic adjacent sums of `l = [a_0, a_1, …, a_k]`, namely
`[a_0 + a_1, a_1 + a_2, …, a_{k-1} + a_k, a_k + a_0]` (entry `i` is `l[i] + l[(i+1) mod length]`). -/
def cyclicSums (l : List Nat) : List Nat :=
  (List.range l.length).map (fun i => l.getD i 0 + l.getD ((i + 1) % l.length) 0)

/-- `SunCycle n A B l`: the list `l = [i_0, i_1, …, i_n]` is a permutation of `[0, 1, …, n]`
with `i_0 = 0` and `i_n = n`, and every cyclic adjacent sum `i_0+i_1, …, i_{n-1}+i_n, i_n+i_0`
is coprime to both `A` and `B`.  A228886(n) counts `SunCycle n (n - 1) (n + 1)`. -/
def SunCycle (n A B : Nat) (l : List Nat) : Prop :=
  l.Perm (List.range (n + 1)) ∧ l.head? = some 0 ∧ l.getLast? = some n ∧
  ∀ s ∈ cyclicSums l, Nat.gcd s A = 1 ∧ Nat.gcd s B = 1
