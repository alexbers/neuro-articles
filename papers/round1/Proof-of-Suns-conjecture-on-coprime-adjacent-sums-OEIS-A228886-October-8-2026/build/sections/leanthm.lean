/-- **Sun's conjecture (OEIS A228886).**  For every `n ≥ 1` there is a permutation
`l = [i_0, …, i_n]` of `[0, …, n]` with `i_0 = 0`, `i_n = n` such that all `n + 1` cyclic adjacent
sums `i_0+i_1, …, i_{n-1}+i_n, i_n+i_0` are coprime to both `n - 1` and `n + 1`,
if and only if `n ≠ 2` and `n ≠ 4`.   (I.e. A228886(n) > 0 for all n ≥ 1 except n = 2, 4.) -/
theorem sun_conjecture (n : Nat) (hn : 1 ≤ n) :
    (∃ l, SunCycle n (n - 1) (n + 1) l) ↔ (n ≠ 2 ∧ n ≠ 4) := by
  rw [exists_list_iff]; exact sun_conjecture_fun n hn

/-- **Sun's companion conjecture** (A228886 comments; arXiv:1309.1679 Remark 3.9(i)):
the same with the moduli `2n - 1` and `2n + 1`; it holds for every `n ≥ 1` except `n = 2`. -/
theorem sun_companion (n : Nat) (hn : 1 ≤ n) :
    (∃ l, SunCycle n (2 * n - 1) (2 * n + 1) l) ↔ n ≠ 2 := by
  rw [exists_list_iff]; exact sun_companion_fun n hn

