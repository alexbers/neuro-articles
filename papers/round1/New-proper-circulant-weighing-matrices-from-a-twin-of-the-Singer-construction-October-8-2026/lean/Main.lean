/-
  A15: new proper circulant weighing matrices (Lean 4 core, no Mathlib).

  A circulant weighing matrix CW(n,k) is an n x n circulant {0,+1,-1}-matrix W with W W^T = k I.
  It is determined by its first row a = (a_0,...,a_{n-1}); the condition W W^T = k I says exactly
  that the periodic autocorrelation  PAF_a(d) = sum_{i<n} a_i * a_{(i+d) mod n}
  equals k for d = 0 and 0 for 0 < d < n.
  It is *proper* if its support is not contained in a coset of a proper subgroup e*Z_n of Z_n
  (e | n, e > 1), i.e. it is not a "lift" A(X^e) of a smaller circulant weighing matrix.

  All certificates below are checked by `decide +kernel` (kernel evaluation; no native code).
-/
set_option Elab.async false

/-- Dot product of two integer lists (truncating `zip`; we only use it on lists of equal length). -/
def dot : List Int → List Int → Int
  | x :: xs, y :: ys => x * y + dot xs ys
  | _, _ => 0

/-- **Periodic autocorrelation** of `a` (length `n`) at shift `d`, index form:
    `pafIdx a d = Σ_{i<n} a[i] * a[(i+d) mod n]`. This is the definition used in the statements. -/
def pafIdx (a : List Int) (d : Nat) : Int :=
  ((List.range a.length).map (fun i => a.getD i 0 * a.getD ((i + d) % a.length) 0)).sum

/-- Fast form used only inside proofs: `dot a (rotateLeft a d)`. -/
def paf (a : List Int) (d : Nat) : Int := dot a (a.rotateLeft d)

/-- `a` is the first row of a circulant weighing matrix `CW(n,k)`:
    length `n`, entries in `{-1,0,1}`, and periodic autocorrelation `k` at shift 0 and `0` at
    every shift `0 < d < n`  (equivalently `W Wᵀ = k I` for the circulant matrix `W` with first row `a`). -/
def IsCW (n k : Nat) (a : List Int) : Prop :=
  a.length = n ∧ (∀ x ∈ a, x = -1 ∨ x = 0 ∨ x = 1) ∧
  ∀ d, d < n → pafIdx a d = if d = 0 then (k : Int) else 0

/-! ### The fast autocorrelation agrees with the index form (general proof). -/
theorem dot_eq_sum : ∀ (a b : List Int), a.length = b.length →
    dot a b = ((List.range a.length).map (fun i => a.getD i 0 * b.getD i 0)).sum
  | [], [], _ => by simp [dot]
  | x :: xs, y :: ys, h => by
    have h' : xs.length = ys.length := by simpa using h
    rw [dot, dot_eq_sum xs ys h', List.length_cons, List.range_succ_eq_map]
    simp [List.map_map, Function.comp_def]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem rotateLeft_getD (a : List Int) (d i : Nat) (hd : d < a.length) (hi : i < a.length) :
    (a.rotateLeft d).getD i 0 = a.getD ((i + d) % a.length) 0 := by
  unfold List.rotateLeft
  by_cases h1 : a.length ≤ 1
  · have hi0 : i = 0 := by omega
    have hd0 : d = 0 := by omega
    subst hi0; subst hd0
    simp [h1]
  · simp only [h1, ite_false]
    have hdm : d % a.length = d := Nat.mod_eq_of_lt hd
    rw [hdm]
    simp only [List.getD_eq_getElem?_getD]
    by_cases h2 : i + d < a.length
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_drop, Nat.mod_eq_of_lt h2]
      congr 2; omega
    · have hl : (a.drop d).length = a.length - d := by simp
      rw [List.getElem?_append_right (by simp; omega), List.getElem?_take_of_lt (by simp; omega)]
      have hm : (i + d) % a.length = i + d - a.length := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hm]; congr 2; omega

theorem length_rotL (a : List Int) (d : Nat) : (a.rotateLeft d).length = a.length := by
  unfold List.rotateLeft
  by_cases h1 : a.length ≤ 1
  · simp only [h1, ite_true]
  · simp only [h1, ite_false, List.length_append, List.length_drop, List.length_take]
    have : d % a.length < a.length := Nat.mod_lt _ (by omega)
    omega

theorem paf_eq_pafIdx (a : List Int) (d : Nat) (hd : d < a.length) : paf a d = pafIdx a d := by
  unfold paf pafIdx
  rw [dot_eq_sum a (a.rotateLeft d) (length_rotL a d).symm]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [rotateLeft_getD a d i hd (by simpa using hi)]

/-- Support (positions of nonzero entries). -/
def supp (a : List Int) : List Nat := (List.range a.length).filter (fun i => a.getD i 0 != 0)

/-- Proper: for every divisor `e > 1` of `n = a.length`, the support is not contained in one
    residue class mod `e` (i.e. not in a coset of the proper subgroup `e·Z_n`). -/
def IsProper (a : List Int) : Prop :=
  ∀ e, e ≤ a.length → 1 < e → e ∣ a.length → ∃ i ∈ supp a, ∃ j ∈ supp a, i % e ≠ j % e

instance (n k : Nat) (a : List Int) : Decidable (IsCW n k a) := by unfold IsCW; infer_instance
instance (a : List Int) : Decidable (IsProper a) := by unfold IsProper; infer_instance

/-- **Main statement.** Proper circulant weighing matrices exist for the parameters
    CW(146,8^2), CW(266,11^2), CW(366,13^2), CW(504,12^2), CW(614,17^2), CW(762,19^2),
    all listed as open in the La Jolla CW repository (v1.3) and absent from Gordon (2026) Table 7.
    Proved at the end of the file (`new_proper_circulant_weighing_matrices`). -/
def MainStatement : Prop :=
    (∃ a, IsCW 146 64 a ∧ IsProper a) ∧
    (∃ a, IsCW 266 121 a ∧ IsProper a) ∧
    (∃ a, IsCW 366 169 a ∧ IsProper a) ∧
    (∃ a, IsCW 504 144 a ∧ IsProper a) ∧
    (∃ a, IsCW 614 289 a ∧ IsProper a) ∧
    (∃ a, IsCW 762 361 a ∧ IsProper a)

/-- Sanity check of the definitions: the classical CW(7,4) = -1 + X + X^2 + X^4 is a proper CW,
    while its lift to Z_14 (A(X^2)) is a CW(14,4) that is NOT proper. -/
def cw7 : List Int := [-1, 1, 1, 0, 1, 0, 0]
example : IsCW 7 4 cw7 ∧ IsProper cw7 := by decide +kernel
example : IsCW 14 4 (cw7.flatMap (fun x => [x, 0])) ∧ ¬ IsProper (cw7.flatMap (fun x => [x, 0])) := by
  decide +kernel
example : ¬ IsCW 7 4 [1, 1, 1, 0, 1, 0, 0] := by decide +kernel

/-- q=3: proper CW(26,3^2) (known order; boxed sporadic in Gordon 2026 Table 7) -/
def cwFam26 : List Int :=
  [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, -1, 0, 1, 0, 0, 1, -1, 0, -1]

theorem cwFam26_len : cwFam26.length = 26 := by decide +kernel
theorem cwFam26_ent : ∀ x ∈ cwFam26, x = -1 ∨ x = 0 ∨ x = 1 := by decide +kernel
theorem cwFam26_paf_0 : ∀ d, d < 26 → 0 ≤ d → paf cwFam26 d = if d = 0 then (9 : Int) else 0 := by
  decide +kernel
theorem cwFam26_paf : ∀ d, d < 26 → paf cwFam26 d = if d = 0 then (9 : Int) else 0 := by
  intro d hd
  exact cwFam26_paf_0 d hd (by omega)
theorem cwFam26_proper : IsProper cwFam26 := by decide +kernel
theorem cwFam26_isCW : IsCW 26 9 cwFam26 :=
  ⟨cwFam26_len, cwFam26_ent, fun d hd => by
    rw [← paf_eq_pafIdx cwFam26 d (by rw [cwFam26_len]; exact hd)]; exact cwFam26_paf d hd⟩

/-- q=5: proper CW(62,5^2) (known order) -/
def cwFam62 : List Int :=
  [0, 1, 1, 1, 0, 1, 0, 0, 1, 0, 1, -1, -1, 1, 1, 1, -1, 1, -1, 0, 0, 0, 0, 1, 0, 1, 0, -1, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0,
   1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 1, 0, -1, 0, 0, 0, 0, -1, 0]

theorem cwFam62_len : cwFam62.length = 62 := by decide +kernel
theorem cwFam62_ent : ∀ x ∈ cwFam62, x = -1 ∨ x = 0 ∨ x = 1 := by decide +kernel
theorem cwFam62_paf_0 : ∀ d, d < 62 → 0 ≤ d → paf cwFam62 d = if d = 0 then (25 : Int) else 0 := by
  decide +kernel
theorem cwFam62_paf : ∀ d, d < 62 → paf cwFam62 d = if d = 0 then (25 : Int) else 0 := by
  intro d hd
  exact cwFam62_paf_0 d hd (by omega)
theorem cwFam62_proper : IsProper cwFam62 := by decide +kernel
theorem cwFam62_isCW : IsCW 62 25 cwFam62 :=
  ⟨cwFam62_len, cwFam62_ent, fun d hd => by
    rw [← paf_eq_pafIdx cwFam62 d (by rw [cwFam62_len]; exact hd)]; exact cwFam62_paf d hd⟩

/-- q=7: proper CW(114,7^2) (known order) -/
def cwFam114 : List Int :=
  [0, 1, 0, 0, 0, 1, -1, 1, 0, 0, 0, 0, 0, -1, 0, 0, -1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, -1, 0, 0, 1, 0, -1, 0, 0, 1, 1, 0, 0, 0,
   0, -1, -1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, -1, -1, 1, 0, 0, 0, 0, -1, -1, 1, -1, 0, -1, 0, 0, 0, -1, 0, 0, -1, 1,
   0, 0, 0, 0, 0, 1, -1, 0, 1, 0, -1, -1, 0, 0, 1, 0, 1, 1, 0, 0, -1, 1, 1, 0, 0, 0, 0, 0, 0, 1, -1, 0, -1, 0]

theorem cwFam114_len : cwFam114.length = 114 := by decide +kernel
theorem cwFam114_ent : ∀ x ∈ cwFam114, x = -1 ∨ x = 0 ∨ x = 1 := by decide +kernel
theorem cwFam114_paf_0 : ∀ d, d < 64 → 0 ≤ d → paf cwFam114 d = if d = 0 then (49 : Int) else 0 := by
  decide +kernel
theorem cwFam114_paf_64 : ∀ d, d < 114 → 64 ≤ d → paf cwFam114 d = if d = 0 then (49 : Int) else 0 := by
  decide +kernel
theorem cwFam114_paf : ∀ d, d < 114 → paf cwFam114 d = if d = 0 then (49 : Int) else 0 := by
  intro d hd
  if h0 : d < 64 then exact cwFam114_paf_0 d h0 (by omega) else
  exact cwFam114_paf_64 d hd (by omega)
theorem cwFam114_proper : IsProper cwFam114 := by decide +kernel
theorem cwFam114_isCW : IsCW 114 49 cwFam114 :=
  ⟨cwFam114_len, cwFam114_ent, fun d hd => by
    rw [← paf_eq_pafIdx cwFam114 d (by rw [cwFam114_len]; exact hd)]; exact cwFam114_paf d hd⟩

/-- q=9: proper CW(182,9^2) (known order) -/
def cwFam182 : List Int :=
  [0, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, -1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, -1, 1, 0, 0, 0, -1, 0, -1,
   0, 0, 1, 1, -1, 0, -1, 0, 0, 0, -1, 1, 0, -1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 1, 0, 0, -1, 0, 1, -1, 0, 0, 0,
   1, 1, 0, 0, 1, -1, -1, 0, 0, -1, 0, 0, 0, 0, 0, 1, -1, 0, 1, 1, 0, -1, 0, 1, 0, 0, -1, -1, 0, 0, 1, -1, 1, -1, 0, 1, 0, -1, 0, 0,
   0, -1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, -1, 0, 0, 0, -1, 0, -1, -1, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, -1, -1, 0, 1, 1, -1, 0, -1, 1, -1,
   0, 0, 1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, 1, 0, 0, 0, 0, -1, 0, -1]

theorem cwFam182_len : cwFam182.length = 182 := by decide +kernel
theorem cwFam182_ent : ∀ x ∈ cwFam182, x = -1 ∨ x = 0 ∨ x = 1 := by decide +kernel
theorem cwFam182_paf_0 : ∀ d, d < 64 → 0 ≤ d → paf cwFam182 d = if d = 0 then (81 : Int) else 0 := by
  decide +kernel
theorem cwFam182_paf_64 : ∀ d, d < 128 → 64 ≤ d → paf cwFam182 d = if d = 0 then (81 : Int) else 0 := by
  decide +kernel
theorem cwFam182_paf_128 : ∀ d, d < 182 → 128 ≤ d → paf cwFam182 d = if d = 0 then (81 : Int) else 0 := by
  decide +kernel
theorem cwFam182_paf : ∀ d, d < 182 → paf cwFam182 d = if d = 0 then (81 : Int) else 0 := by
  intro d hd
  if h0 : d < 64 then exact cwFam182_paf_0 d h0 (by omega) else
  if h1 : d < 128 then exact cwFam182_paf_64 d h1 (by omega) else
  exact cwFam182_paf_128 d hd (by omega)
theorem cwFam182_proper : IsProper cwFam182 := by decide +kernel
theorem cwFam182_isCW : IsCW 182 81 cwFam182 :=
  ⟨cwFam182_len, cwFam182_ent, fun d hd => by
    rw [← paf_eq_pafIdx cwFam182 d (by rw [cwFam182_len]; exact hd)]; exact cwFam182_paf d hd⟩

/-- q=11: proper CW(266,11^2) -- NEW (open in La Jolla CW repository; absent from Gordon 2026 Table 7) -/
def cwFam266 : List Int :=
  [-1, 0, 0, 0, 1, 0, -1, 1, 1, -1, 0, 0, 1, -1, 1, 0, -1, 0, 1, 0, 0, 0, 0, 0, 1, -1, 0, 1, 1, 0, 0, 1, 1, 0, -1, 1, -1, 0, 1, 1,
   1, 0, 1, 0, 1, -1, 0, 0, -1, 1, 1, 0, 1, 0, 0, 0, 0, -1, 1, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, -1, -1, 0, -1, 1, 1, 1, 0, -1,
   0, -1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, -1, 0, -1, 0, 0, 1, -1, -1, 0, 1, -1, 0, 1, 1, 1, -1, 0, 0, 0, 0, 1, 0, 1, 0, 1, -1, 1,
   1, 0, 1, 0, -1, -1, 0, 0, 0, 0, -1, 0, 1, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, -1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0,
   0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, -1, 0, 0, 1, -1, 0, 0, 0, -1, 0, -1, 0, -1, -1, 0, 0, 0, -1, -1, 0, 1, 1, 1, 0,
   -1, 1, 0, 1, 0, 0, -1, 0, 0, 0, 0, -1, 0, 1, 0, 1, 0, -1, 1, 0, 0, 0, -1, 1, 0, -1, 0, -1, 0, -1, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0,
   0, 0, 0, -1, 1, 1, 0, -1, 0, -1, 0, 0, 0, 0, 1, 0, 1, 0, 0, -1, -1, -1, -1, 0, 1, 0]

theorem cwFam266_len : cwFam266.length = 266 := by decide +kernel
theorem cwFam266_ent : ∀ x ∈ cwFam266, x = -1 ∨ x = 0 ∨ x = 1 := by decide +kernel
theorem cwFam266_paf_0 : ∀ d, d < 64 → 0 ≤ d → paf cwFam266 d = if d = 0 then (121 : Int) else 0 := by
  decide +kernel
theorem cwFam266_paf_64 : ∀ d, d < 128 → 64 ≤ d → paf cwFam266 d = if d = 0 then (121 : Int) else 0 := by
  decide +kernel
theorem cwFam266_paf_128 : ∀ d, d < 192 → 128 ≤ d → paf cwFam266 d = if d = 0 then (121 : Int) else 0 := by
  decide +kernel
theorem cwFam266_paf_192 : ∀ d, d < 256 → 192 ≤ d → paf cwFam266 d = if d = 0 then (121 : Int) else 0 := by
  decide +kernel
theorem cwFam266_paf_256 : ∀ d, d < 266 → 256 ≤ d → paf cwFam266 d = if d = 0 then (121 : Int) else 0 := by
  decide +kernel
theorem cwFam266_paf : ∀ d, d < 266 → paf cwFam266 d = if d = 0 then (121 : Int) else 0 := by
  intro d hd
  if h0 : d < 64 then exact cwFam266_paf_0 d h0 (by omega) else
  if h1 : d < 128 then exact cwFam266_paf_64 d h1 (by omega) else
  if h2 : d < 192 then exact cwFam266_paf_128 d h2 (by omega) else
  if h3 : d < 256 then exact cwFam266_paf_192 d h3 (by omega) else
  exact cwFam266_paf_256 d hd (by omega)
theorem cwFam266_proper : IsProper cwFam266 := by decide +kernel
theorem cwFam266_isCW : IsCW 266 121 cwFam266 :=
  ⟨cwFam266_len, cwFam266_ent, fun d hd => by
    rw [← paf_eq_pafIdx cwFam266 d (by rw [cwFam266_len]; exact hd)]; exact cwFam266_paf d hd⟩

/-- q=13: proper CW(366,13^2) -- NEW (open; removed from table in Gordon 2025/26) -/
def cwFam366 : List Int :=
  [0, 0, 1, 1, -1, -1, -1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 1, -1, 1, -1, -1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 1, -1, 1, 0, 1,
   0, -1, -1, 0, 0, 0, 1, 0, 1, 0, 0, 0, -1, -1, -1, 0, 0, -1, -1, 1, 1, 0, 0, 0, 0, -1, 0, 0, -1, 1, -1, -1, 0, 0, 0, 0, 1, 0, -1, 0,
   -1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 0, 0, -1, -1, 1, -1, 0, 0, 0, 0, 1, -1, 0, 0, 1, 1, 1, 0, 1, 0, -1, 1, -1, 1, 1, 0, -1, -1, 0,
   -1, 1, 0, -1, -1, 0, 0, 0, 0, 1, 0, 1, 0, -1, 0, -1, 0, 1, 1, 0, 0, 1, 0, 0, -1, 0, -1, 0, -1, 1, -1, -1, -1, 0, 0, 0, 1, -1, 0, 0,
   1, 0, 0, 0, -1, 1, -1, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, -1, 1, -1, -1, 0, 1, -1, 0, 0, 0, 0, 0, 1, -1, 0, 0, 1, 0, -1, 1, 1, 1,
   0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, -1, 0, 0, 0, 1, 1, 1, 0, 0, 0, -1, 1,
   0, 0, 0, 0, 0, 0, 1, -1, 0, 1, 1, 0, 0, 0, 0, -1, 1, 0, 1, 0, 1, 0, 1, 0, 1, -1, -1, 1, 1, 0, 1, 0, 0, -1, 1, 1, 0, 0, 0, 0,
   1, 1, -1, -1, 0, 0, -1, -1, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, -1, 1, -1, 0, 0, 0, 0, 1, 0, 1, 0, 1,
   0, 0, 1, -1, 0, 1, 1, 0, -1, 0, 1, 0, 0, 0, 0, 0, -1, -1, 1, 0, 0, -1, -1, 0, -1, -1, 1, 0, 0, 0, 0, 0, -1, 1, 0, -1, 0, 1, 1, 1,
   0, 0, 0, 0, 0, 1]

theorem cwFam366_len : cwFam366.length = 366 := by decide +kernel
theorem cwFam366_ent : ∀ x ∈ cwFam366, x = -1 ∨ x = 0 ∨ x = 1 := by decide +kernel
theorem cwFam366_paf_0 : ∀ d, d < 64 → 0 ≤ d → paf cwFam366 d = if d = 0 then (169 : Int) else 0 := by
  decide +kernel
theorem cwFam366_paf_64 : ∀ d, d < 128 → 64 ≤ d → paf cwFam366 d = if d = 0 then (169 : Int) else 0 := by
  decide +kernel
theorem cwFam366_paf_128 : ∀ d, d < 192 → 128 ≤ d → paf cwFam366 d = if d = 0 then (169 : Int) else 0 := by
  decide +kernel
theorem cwFam366_paf_192 : ∀ d, d < 256 → 192 ≤ d → paf cwFam366 d = if d = 0 then (169 : Int) else 0 := by
  decide +kernel
theorem cwFam366_paf_256 : ∀ d, d < 320 → 256 ≤ d → paf cwFam366 d = if d = 0 then (169 : Int) else 0 := by
  decide +kernel
theorem cwFam366_paf_320 : ∀ d, d < 366 → 320 ≤ d → paf cwFam366 d = if d = 0 then (169 : Int) else 0 := by
  decide +kernel
theorem cwFam366_paf : ∀ d, d < 366 → paf cwFam366 d = if d = 0 then (169 : Int) else 0 := by
  intro d hd
  if h0 : d < 64 then exact cwFam366_paf_0 d h0 (by omega) else
  if h1 : d < 128 then exact cwFam366_paf_64 d h1 (by omega) else
  if h2 : d < 192 then exact cwFam366_paf_128 d h2 (by omega) else
  if h3 : d < 256 then exact cwFam366_paf_192 d h3 (by omega) else
  if h4 : d < 320 then exact cwFam366_paf_256 d h4 (by omega) else
  exact cwFam366_paf_320 d hd (by omega)
theorem cwFam366_proper : IsProper cwFam366 := by decide +kernel
theorem cwFam366_isCW : IsCW 366 169 cwFam366 :=
  ⟨cwFam366_len, cwFam366_ent, fun d hd => by
    rw [← paf_eq_pafIdx cwFam366 d (by rw [cwFam366_len]; exact hd)]; exact cwFam366_paf d hd⟩

/-- q=17: proper CW(614,17^2) -- NEW (open; removed from table in Gordon 2025/26) -/
def cwFam614 : List Int :=
  [-1, 0, 1, 0, -1, 1, 1, -1, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1,
   0, -1, 0, -1, 0, 0, 0, -1, 0, -1, 1, 0, 0, 0, 0, 1, 1, -1, -1, 0, 1, -1, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, -1, 0, -1, 1, -1,
   -1, -1, 0, -1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, -1, 0, 0, -1, 1, 0, 0, -1, 1, -1, 1, 1, 0, 1, -1, 0, 0, 0, 1, -1, 0, -1, 0, -1, 1, -1,
   -1, 1, 1, 0, 1, -1, -1, 0, 0, 1, 0, 0, -1, 0, 0, 1, 0, 0, -1, 0, -1, 1, 0, 1, -1, 1, 0, -1, 1, -1, -1, 0, 0, 1, 0, -1, -1, -1, 1, 1,
   1, 0, 0, 1, 1, 0, 0, 1, 0, -1, 1, 0, -1, 1, 0, 1, 1, 0, 0, -1, 1, -1, 0, -1, -1, -1, 0, 0, -1, 1, 1, 0, 0, 0, 0, -1, -1, 0, -1, 0,
   1, 0, 0, -1, 1, 0, 0, 1, 0, 0, -1, 0, 0, -1, -1, 1, 0, 1, -1, -1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0,
   1, -1, 1, 0, 0, -1, -1, 1, 0, 0, 0, 0, 1, 0, -1, 0, 0, 0, 1, 1, 1, 0, -1, 1, 1, 1, 1, -1, 1, -1, 0, 0, 0, 1, 1, -1, -1, 0, 0, 0,
   0, 0, 0, -1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, -1, -1, 0, 0, 0, -1, 0, 0, 0, 0, 1, 1, 0, 1, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0,
   0, 1, -1, -1, 1, 0, 0, 0, 1, 0, 1, -1, 1, 1, 0, -1, 0, -1, 1, 1, -1, 0, 1, 1, -1, 1, 0, 0, 0, 0, 0, 1, -1, 1, 0, -1, 0, 0, -1, 1,
   1, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, -1, 0, -1, 0, 1, -1, 1, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0, 1, 1, 1, 1,
   0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, -1, -1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, -1, 1, 0,
   1, 1, 0, 1, 1, 0, -1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0,
   0, -1, 0, 0, -1, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, -1, -1, -1, -1, 0, 0, -1, 0, 1, 0, 0, -1, 0, 0, -1, -1, 0, 1, 1, 0, -1, 1,
   0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 1, 0, -1, 0, 1, -1, -1, 0, 0, 1, 0, 0, 0, 0, -1, -1, 0, 0, 0, 1, 1, 1, -1, 0,
   -1, 0, -1, -1, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, 0, 0, 0, 0, 1, 1, -1, -1, -1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1,
   1, -1, 0, 0, 1, 0, -1, 0, -1, 1, 0, -1, 0, 0]

theorem cwFam614_len : cwFam614.length = 614 := by decide +kernel
theorem cwFam614_ent : ∀ x ∈ cwFam614, x = -1 ∨ x = 0 ∨ x = 1 := by decide +kernel
theorem cwFam614_paf_0 : ∀ d, d < 64 → 0 ≤ d → paf cwFam614 d = if d = 0 then (289 : Int) else 0 := by
  decide +kernel
theorem cwFam614_paf_64 : ∀ d, d < 128 → 64 ≤ d → paf cwFam614 d = if d = 0 then (289 : Int) else 0 := by
  decide +kernel
theorem cwFam614_paf_128 : ∀ d, d < 192 → 128 ≤ d → paf cwFam614 d = if d = 0 then (289 : Int) else 0 := by
  decide +kernel
theorem cwFam614_paf_192 : ∀ d, d < 256 → 192 ≤ d → paf cwFam614 d = if d = 0 then (289 : Int) else 0 := by
  decide +kernel
theorem cwFam614_paf_256 : ∀ d, d < 320 → 256 ≤ d → paf cwFam614 d = if d = 0 then (289 : Int) else 0 := by
  decide +kernel
theorem cwFam614_paf_320 : ∀ d, d < 384 → 320 ≤ d → paf cwFam614 d = if d = 0 then (289 : Int) else 0 := by
  decide +kernel
theorem cwFam614_paf_384 : ∀ d, d < 448 → 384 ≤ d → paf cwFam614 d = if d = 0 then (289 : Int) else 0 := by
  decide +kernel
theorem cwFam614_paf_448 : ∀ d, d < 512 → 448 ≤ d → paf cwFam614 d = if d = 0 then (289 : Int) else 0 := by
  decide +kernel
theorem cwFam614_paf_512 : ∀ d, d < 576 → 512 ≤ d → paf cwFam614 d = if d = 0 then (289 : Int) else 0 := by
  decide +kernel
theorem cwFam614_paf_576 : ∀ d, d < 614 → 576 ≤ d → paf cwFam614 d = if d = 0 then (289 : Int) else 0 := by
  decide +kernel
theorem cwFam614_paf : ∀ d, d < 614 → paf cwFam614 d = if d = 0 then (289 : Int) else 0 := by
  intro d hd
  if h0 : d < 64 then exact cwFam614_paf_0 d h0 (by omega) else
  if h1 : d < 128 then exact cwFam614_paf_64 d h1 (by omega) else
  if h2 : d < 192 then exact cwFam614_paf_128 d h2 (by omega) else
  if h3 : d < 256 then exact cwFam614_paf_192 d h3 (by omega) else
  if h4 : d < 320 then exact cwFam614_paf_256 d h4 (by omega) else
  if h5 : d < 384 then exact cwFam614_paf_320 d h5 (by omega) else
  if h6 : d < 448 then exact cwFam614_paf_384 d h6 (by omega) else
  if h7 : d < 512 then exact cwFam614_paf_448 d h7 (by omega) else
  if h8 : d < 576 then exact cwFam614_paf_512 d h8 (by omega) else
  exact cwFam614_paf_576 d hd (by omega)
theorem cwFam614_proper : IsProper cwFam614 := by decide +kernel
theorem cwFam614_isCW : IsCW 614 289 cwFam614 :=
  ⟨cwFam614_len, cwFam614_ent, fun d hd => by
    rw [← paf_eq_pafIdx cwFam614 d (by rw [cwFam614_len]; exact hd)]; exact cwFam614_paf d hd⟩

/-- q=19: proper CW(762,19^2) -- NEW (open; removed from table in Gordon 2025/26) -/
def cwFam762 : List Int :=
  [1, 0, 0, -1, -1, 0, 1, 1, 0, 1, 0, 1, -1, 0, 1, 0, -1, 0, -1, 0, 0, 0, -1, 0, -1, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0,
   0, 0, 0, 1, 0, -1, 0, 1, 0, -1, -1, -1, 0, 1, -1, 1, 1, -1, -1, 0, 1, 0, 0, 0, 0, 0, 1, 0, -1, 0, 1, -1, 0, -1, 0, 0, -1, 0, 1, 0,
   1, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 1, -1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, -1, 0, -1, 0, 0, 0, 0, 1, 1, 0, -1, 0, -1,
   0, 0, 0, -1, 1, 0, 0, 0, 0, -1, 1, 1, 1, 1, -1, 1, -1, -1, 1, -1, 1, 0, 1, 0, -1, 1, 0, 1, 0, 0, 0, 1, 0, 1, -1, 0, 0, 0, 1, -1,
   0, 1, 0, -1, -1, -1, 0, 0, -1, -1, 0, 1, 0, -1, 1, -1, 0, 0, 1, -1, 0, -1, 0, -1, 1, -1, 0, 0, -1, 0, 0, 1, 0, 1, 0, 1, 0, 1, -1, 1,
   0, 1, 0, 1, 1, 0, 0, -1, 1, 1, 0, 1, 1, -1, -1, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, -1, 1, 0, 0, -1, -1, 0, -1, 0, -1, 0, -1,
   0, 1, -1, -1, 0, 1, 0, 0, 1, -1, 1, 1, 0, -1, 0, -1, -1, 1, 1, 0, -1, 0, 1, -1, -1, -1, 1, 1, 0, 0, -1, 1, -1, -1, 0, 0, 0, -1, 1, 1,
   0, 0, -1, 1, 0, 0, 1, -1, 1, 0, 0, 1, -1, -1, 0, 1, 0, -1, -1, 0, 1, 0, 1, 1, -1, 0, 0, -1, 0, -1, 0, 1, 0, 0, 0, 0, -1, -1, 0, 1,
   1, -1, -1, 0, 1, 0, 1, -1, -1, 0, 1, 1, 1, 0, 1, 0, 1, -1, 1, 0, -1, -1, -1, -1, 1, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, -1, 0, 1, 1, 0,
   1, 0, 0, 0, -1, 0, 1, 1, -1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, -1, 0, 0, 1, -1, 0, 0, -1, 0, 0, 1, 0, -1, 0, 0, 0, 0, 1, 0, 1, 0,
   1, 1, -1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, -1, 0, 1, -1, -1, 1, -1, 1, 1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
   1, 0, -1, 1, -1, -1, 1, 0, 1, 0, -1, 0, 0, 0, 0, -1, -1, 0, 1, 0, 1, 0, 1, -1, 0, 0, -1, -1, 0, 1, -1, 1, -1, 0, 0, 0, -1, 0, 0, 0,
   0, 0, 1, 0, 0, -1, 0, -1, 0, 1, 0, -1, 1, 0, -1, 0, 0, 0, 0, -1, 0, 1, 0, 1, 0, 0, -1, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, -1, 0, -1, 0, 0, -1, 0, 1, -1, -1, 0, 1, 0, 0, 1, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, -1, 0, 0, 1, 0, -1, 0, 0, 0, -1, -1, 0,
   0, -1, 0, 1, 0, 0, 0, 1, 1, 0, 0, -1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, -1, -1, 0, 0, 0, -1, 0, 0, 0, 0, -1, 1, -1, 0,
   0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, -1, 0, 0, -1, 0, -1, 0, 1, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
   -1, 0, 1, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, -1, -1, 1, 0, 0, 0, 1, -1, 0, 0, 1, 1, 0, 0, 0, -1, -1, 0, 0, 0, 1, 0, -1, 0, 0,
   0, 0, -1, 0, 0, 0, 1, 1, 0, -1, 0, -1, 0, -1, -1, 1, -1, 0, 0, -1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 1, 0, 0, 0,
   1, 0, 0, 0, 0, 0, 1, 1, 0, 1, -1, -1, 0, 1, 0, -1, 0, -1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 1, 0,
   0, 1]

theorem cwFam762_len : cwFam762.length = 762 := by decide +kernel
theorem cwFam762_ent : ∀ x ∈ cwFam762, x = -1 ∨ x = 0 ∨ x = 1 := by decide +kernel
theorem cwFam762_paf_0 : ∀ d, d < 64 → 0 ≤ d → paf cwFam762 d = if d = 0 then (361 : Int) else 0 := by
  decide +kernel
theorem cwFam762_paf_64 : ∀ d, d < 128 → 64 ≤ d → paf cwFam762 d = if d = 0 then (361 : Int) else 0 := by
  decide +kernel
theorem cwFam762_paf_128 : ∀ d, d < 192 → 128 ≤ d → paf cwFam762 d = if d = 0 then (361 : Int) else 0 := by
  decide +kernel
theorem cwFam762_paf_192 : ∀ d, d < 256 → 192 ≤ d → paf cwFam762 d = if d = 0 then (361 : Int) else 0 := by
  decide +kernel
theorem cwFam762_paf_256 : ∀ d, d < 320 → 256 ≤ d → paf cwFam762 d = if d = 0 then (361 : Int) else 0 := by
  decide +kernel
theorem cwFam762_paf_320 : ∀ d, d < 384 → 320 ≤ d → paf cwFam762 d = if d = 0 then (361 : Int) else 0 := by
  decide +kernel
theorem cwFam762_paf_384 : ∀ d, d < 448 → 384 ≤ d → paf cwFam762 d = if d = 0 then (361 : Int) else 0 := by
  decide +kernel
theorem cwFam762_paf_448 : ∀ d, d < 512 → 448 ≤ d → paf cwFam762 d = if d = 0 then (361 : Int) else 0 := by
  decide +kernel
theorem cwFam762_paf_512 : ∀ d, d < 576 → 512 ≤ d → paf cwFam762 d = if d = 0 then (361 : Int) else 0 := by
  decide +kernel
theorem cwFam762_paf_576 : ∀ d, d < 640 → 576 ≤ d → paf cwFam762 d = if d = 0 then (361 : Int) else 0 := by
  decide +kernel
theorem cwFam762_paf_640 : ∀ d, d < 704 → 640 ≤ d → paf cwFam762 d = if d = 0 then (361 : Int) else 0 := by
  decide +kernel
theorem cwFam762_paf_704 : ∀ d, d < 762 → 704 ≤ d → paf cwFam762 d = if d = 0 then (361 : Int) else 0 := by
  decide +kernel
theorem cwFam762_paf : ∀ d, d < 762 → paf cwFam762 d = if d = 0 then (361 : Int) else 0 := by
  intro d hd
  if h0 : d < 64 then exact cwFam762_paf_0 d h0 (by omega) else
  if h1 : d < 128 then exact cwFam762_paf_64 d h1 (by omega) else
  if h2 : d < 192 then exact cwFam762_paf_128 d h2 (by omega) else
  if h3 : d < 256 then exact cwFam762_paf_192 d h3 (by omega) else
  if h4 : d < 320 then exact cwFam762_paf_256 d h4 (by omega) else
  if h5 : d < 384 then exact cwFam762_paf_320 d h5 (by omega) else
  if h6 : d < 448 then exact cwFam762_paf_384 d h6 (by omega) else
  if h7 : d < 512 then exact cwFam762_paf_448 d h7 (by omega) else
  if h8 : d < 576 then exact cwFam762_paf_512 d h8 (by omega) else
  if h9 : d < 640 then exact cwFam762_paf_576 d h9 (by omega) else
  if h10 : d < 704 then exact cwFam762_paf_640 d h10 (by omega) else
  exact cwFam762_paf_704 d hd (by omega)
theorem cwFam762_proper : IsProper cwFam762 := by decide +kernel
theorem cwFam762_isCW : IsCW 762 361 cwFam762 :=
  ⟨cwFam762_len, cwFam762_ent, fun d hd => by
    rw [← paf_eq_pafIdx cwFam762 d (by rw [cwFam762_len]; exact hd)]; exact cwFam762_paf d hd⟩

/-- proper CW(146,8^2) -- NEW (open in La Jolla CW repository; absent from Gordon 2026 Table 7); found by multiplier-2 doubling search -/
def cw146 : List Int :=
  [-1, 0, -1, -1, -1, 1, 0, 1, -1, 0, 0, 1, 0, 0, 0, 1, -1, -1, 0, -1, 0, 1, 1, -1, 0, 0, 0, 0, 0, 0, 1, 0, -1, -1, 1, 0, 0, 0, 0, 1,
   0, 0, 1, 0, 1, -1, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 1, 0, 0, -1, -1, 0, 1, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1,
   0, 0, 0, 1, 1, -1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, -1, 0, 0, 0, 1, 0, 1, 0, 0, 1, -1, 0, 0, -1, -1, 0, 1, 0, 1, 0, 1, 1, -1,
   1, -1, 0, 0, 0, 0, 1, 0, -1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0]

theorem cw146_len : cw146.length = 146 := by decide +kernel
theorem cw146_ent : ∀ x ∈ cw146, x = -1 ∨ x = 0 ∨ x = 1 := by decide +kernel
theorem cw146_paf_0 : ∀ d, d < 64 → 0 ≤ d → paf cw146 d = if d = 0 then (64 : Int) else 0 := by
  decide +kernel
theorem cw146_paf_64 : ∀ d, d < 128 → 64 ≤ d → paf cw146 d = if d = 0 then (64 : Int) else 0 := by
  decide +kernel
theorem cw146_paf_128 : ∀ d, d < 146 → 128 ≤ d → paf cw146 d = if d = 0 then (64 : Int) else 0 := by
  decide +kernel
theorem cw146_paf : ∀ d, d < 146 → paf cw146 d = if d = 0 then (64 : Int) else 0 := by
  intro d hd
  if h0 : d < 64 then exact cw146_paf_0 d h0 (by omega) else
  if h1 : d < 128 then exact cw146_paf_64 d h1 (by omega) else
  exact cw146_paf_128 d hd (by omega)
theorem cw146_proper : IsProper cw146 := by decide +kernel
theorem cw146_isCW : IsCW 146 64 cw146 :=
  ⟨cw146_len, cw146_ent, fun d hd => by
    rw [← paf_eq_pafIdx cw146 d (by rw [cw146_len]; exact hd)]; exact cw146_paf d hd⟩

/-- proper CW(504,12^2) -- NEW (open); product of CW(24,3^2) and CW(63,4^2) over non-coprime orders -/
def cw504 : List Int :=
  [-1, 0, 1, 0, 1, 1, 0, 0, -1, 0, -1, 0, 0, -1, 0, 0, -1, 0, 0, 0, -1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, -1, 1, -1, 0, 0, 1, 0, 0,
   1, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   1, 0, 0, 0, 0, 1, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0,
   0, 1, 0, 0, 0, -1, -1, 0, -1, 1, 1, 0, 0, 0, -1, 0, 1, 1, 0, 0, 0, 0, -1, 0, 0, -1, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, -1, 0,
   1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, -1, 0, 0, 0, -1, 0, 0, 0, -1, -1, 0, 0, 0, -1, 0, 0, -1, 0, 0,
   0, 1, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0,
   0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -1, -1, 0, -1, 0, 0, 0, 1, 0, 1, 0, 0, -1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0,
   0, 1, 0, 0, 1, 1, 1, 0, 0, 1, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, -1, 0, 0,
   1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0,
   -1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 1, 0, 1, 1, -1, 0, 0, 0, 1, 0, -1, 1, 0, 0, 0, 0, 1, 0, 0, -1, 1, 0,
   0, 1, 0, 0, 0, -1, 0, 0, 0, -1, 1, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, -1, 0, 0,
   0, 0, 1, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 1, -1, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem cw504_len : cw504.length = 504 := by decide +kernel
theorem cw504_ent : ∀ x ∈ cw504, x = -1 ∨ x = 0 ∨ x = 1 := by decide +kernel
theorem cw504_paf_0 : ∀ d, d < 64 → 0 ≤ d → paf cw504 d = if d = 0 then (144 : Int) else 0 := by
  decide +kernel
theorem cw504_paf_64 : ∀ d, d < 128 → 64 ≤ d → paf cw504 d = if d = 0 then (144 : Int) else 0 := by
  decide +kernel
theorem cw504_paf_128 : ∀ d, d < 192 → 128 ≤ d → paf cw504 d = if d = 0 then (144 : Int) else 0 := by
  decide +kernel
theorem cw504_paf_192 : ∀ d, d < 256 → 192 ≤ d → paf cw504 d = if d = 0 then (144 : Int) else 0 := by
  decide +kernel
theorem cw504_paf_256 : ∀ d, d < 320 → 256 ≤ d → paf cw504 d = if d = 0 then (144 : Int) else 0 := by
  decide +kernel
theorem cw504_paf_320 : ∀ d, d < 384 → 320 ≤ d → paf cw504 d = if d = 0 then (144 : Int) else 0 := by
  decide +kernel
theorem cw504_paf_384 : ∀ d, d < 448 → 384 ≤ d → paf cw504 d = if d = 0 then (144 : Int) else 0 := by
  decide +kernel
theorem cw504_paf_448 : ∀ d, d < 504 → 448 ≤ d → paf cw504 d = if d = 0 then (144 : Int) else 0 := by
  decide +kernel
theorem cw504_paf : ∀ d, d < 504 → paf cw504 d = if d = 0 then (144 : Int) else 0 := by
  intro d hd
  if h0 : d < 64 then exact cw504_paf_0 d h0 (by omega) else
  if h1 : d < 128 then exact cw504_paf_64 d h1 (by omega) else
  if h2 : d < 192 then exact cw504_paf_128 d h2 (by omega) else
  if h3 : d < 256 then exact cw504_paf_192 d h3 (by omega) else
  if h4 : d < 320 then exact cw504_paf_256 d h4 (by omega) else
  if h5 : d < 384 then exact cw504_paf_320 d h5 (by omega) else
  if h6 : d < 448 then exact cw504_paf_384 d h6 (by omega) else
  exact cw504_paf_448 d hd (by omega)
theorem cw504_proper : IsProper cw504 := by decide +kernel
theorem cw504_isCW : IsCW 504 144 cw504 :=
  ⟨cw504_len, cw504_ent, fun d hd => by
    rw [← paf_eq_pafIdx cw504 d (by rw [cw504_len]; exact hd)]; exact cw504_paf d hd⟩


/-! ## Main theorem: proper CW(n,k) for parameters open in the La Jolla CW repository / Gordon 2026 Table 7 -/
theorem new_proper_circulant_weighing_matrices : MainStatement := by
  unfold MainStatement
  exact ⟨⟨cw146, cw146_isCW, cw146_proper⟩, ⟨cwFam266, cwFam266_isCW, cwFam266_proper⟩, ⟨cwFam366, cwFam366_isCW, cwFam366_proper⟩, ⟨cw504, cw504_isCW, cw504_proper⟩, ⟨cwFam614, cwFam614_isCW, cwFam614_proper⟩, ⟨cwFam762, cwFam762_isCW, cwFam762_proper⟩⟩

/-- The twin-Singer family CW(2(q^2+q+1), q^2) for q = 3,5,7,9,11,13,17,19 (explicit rows). -/
theorem twin_singer_family_members :
    (IsCW 26 9 cwFam26 ∧ IsProper cwFam26) ∧
    (IsCW 62 25 cwFam62 ∧ IsProper cwFam62) ∧
    (IsCW 114 49 cwFam114 ∧ IsProper cwFam114) ∧
    (IsCW 182 81 cwFam182 ∧ IsProper cwFam182) ∧
    (IsCW 266 121 cwFam266 ∧ IsProper cwFam266) ∧
    (IsCW 366 169 cwFam366 ∧ IsProper cwFam366) ∧
    (IsCW 614 289 cwFam614 ∧ IsProper cwFam614) ∧
    (IsCW 762 361 cwFam762 ∧ IsProper cwFam762) :=
  ⟨⟨cwFam26_isCW, cwFam26_proper⟩, ⟨cwFam62_isCW, cwFam62_proper⟩, ⟨cwFam114_isCW, cwFam114_proper⟩, ⟨cwFam182_isCW, cwFam182_proper⟩, ⟨cwFam266_isCW, cwFam266_proper⟩, ⟨cwFam366_isCW, cwFam366_proper⟩, ⟨cwFam614_isCW, cwFam614_proper⟩, ⟨cwFam762_isCW, cwFam762_proper⟩⟩

#print axioms new_proper_circulant_weighing_matrices
#print axioms twin_singer_family_members
#print axioms cwFam26_isCW
#print axioms cwFam26_proper
#print axioms cwFam62_isCW
#print axioms cwFam62_proper
#print axioms cwFam114_isCW
#print axioms cwFam114_proper
#print axioms cwFam182_isCW
#print axioms cwFam182_proper
#print axioms cwFam266_isCW
#print axioms cwFam266_proper
#print axioms cwFam366_isCW
#print axioms cwFam366_proper
#print axioms cwFam614_isCW
#print axioms cwFam614_proper
#print axioms cwFam762_isCW
#print axioms cwFam762_proper
#print axioms cw146_isCW
#print axioms cw146_proper
#print axioms cw504_isCW
#print axioms cw504_proper
