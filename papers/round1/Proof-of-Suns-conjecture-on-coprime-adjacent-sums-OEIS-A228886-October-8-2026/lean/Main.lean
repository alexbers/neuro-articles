/-
  OEIS A228886 — two conjectures of Zhi-Wei Sun (Sep 2013), proved in Lean 4 core (no Mathlib).

  A228886(n) = number of permutations i_0, i_1, ..., i_n of 0, 1, ..., n with i_0 = 0 and
  i_n = n such that the n+1 cyclic adjacent sums
        i_0 + i_1, i_1 + i_2, ..., i_{n-1} + i_n, i_n + i_0
  are all coprime to both n - 1 and n + 1.

  (1) Conjecture (Sun, OEIS A228886; arXiv:1309.1679, Conjecture 3.9):
        A228886(n) > 0 for every n ≥ 1 except n = 2, 4.
      Sun proved it for odd n (arXiv:1309.1679, Remark 3.9(ii)); the even case was open.
      Theorem `A228886.sun_conjecture` proves the full statement (both parities):
        for n ≥ 1:  (∃ l, SunCycle n (n - 1) (n + 1) l) ↔ (n ≠ 2 ∧ n ≠ 4).
      Odd n: Sun's permutations.  Even n ≥ 8: a new explicit permutation.  n = 6: explicit.
      n = 2, 4: impossible.

  (2) Companion conjecture (stated in the comments of A228886 and in Remark 3.9(i) of
      arXiv:1309.1679): the same with n - 1, n + 1 replaced by 2n - 1, 2n + 1.
      Theorem `A228886.sun_companion`:
        for n ≥ 1:  (∃ l, SunCycle n (2 * n - 1) (2 * n + 1) l) ↔ n ≠ 2.
      (n = 2 is a trivial exception: the only candidate is [0, 1, 2] and 1 + 2 = 3 = 2n - 1.)
-/

-- Lean's asynchronous elaboration spawns many threads, which exceeds the resource limits of the
-- (shared) checking machine; elaborate sequentially instead.  This has no logical effect.
set_option Elab.async false

namespace A228886

/-! ## Definitions used in the main statements -/

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

/-- Function version (`i_k = p k`): `(p 0, …, p n)` is a permutation of `0..n` (an injective map
`{0,…,n} → {0,…,n}`), `p 0 = 0`, `p n = n`, and every cyclic adjacent sum
`p i + p ((i + 1) mod (n + 1))`, `0 ≤ i ≤ n`, is coprime to both `A` and `B`. -/
def SunFun (n A B : Nat) (p : Nat → Nat) : Prop :=
  (∀ i, i ≤ n → p i ≤ n) ∧
  (∀ i j, i ≤ n → j ≤ n → p i = p j → i = j) ∧
  p 0 = 0 ∧ p n = n ∧
  ∀ i, i ≤ n →
    Nat.gcd (p i + p ((i + 1) % (n + 1))) A = 1 ∧
    Nat.gcd (p i + p ((i + 1) % (n + 1))) B = 1

/-! ## Generic builder -/

theorem sunFun_of (n A B : Nat) (p : Nat → Nat) (S : Nat → Prop)
    (hS : ∀ s, S s → Nat.gcd s A = 1 ∧ Nat.gcd s B = 1)
    (hb : ∀ i, i ≤ n → p i ≤ n)
    (hinj : ∀ i j, i ≤ n → j ≤ n → p i = p j → i = j)
    (h0 : p 0 = 0) (hn : p n = n)
    (hstep : ∀ i, i < n → S (p i + p (i + 1)))
    (hlast : S (p n + p 0)) : SunFun n A B p := by
  refine ⟨hb, hinj, h0, hn, ?_⟩
  intro i hi
  rcases Nat.lt_or_ge i n with h | h
  · have e : (i + 1) % (n + 1) = i + 1 := Nat.mod_eq_of_lt (by omega)
    rw [e]; exact hS _ (hstep i h)
  · have e : i = n := by omega
    subst e
    rw [Nat.mod_self]; exact hS _ hlast

/-- If some `p` has the "step" property with admissible sum set `S`, so does the mirrored map
`i ↦ n - p (n - i)` with the admissible set `{2n - s : s ∈ S}`. -/
theorem mirror_props (n : Nat) (p : Nat → Nat) (S : Nat → Prop)
    (hb : ∀ i, i ≤ n → p i ≤ n)
    (hinj : ∀ i j, i ≤ n → j ≤ n → p i = p j → i = j)
    (h0 : p 0 = 0) (hn : p n = n)
    (hstep : ∀ i, i < n → S (p i + p (i + 1))) :
    (∀ i, i ≤ n → n - p (n - i) ≤ n) ∧
    (∀ i j, i ≤ n → j ≤ n → n - p (n - i) = n - p (n - j) → i = j) ∧
    n - p (n - 0) = 0 ∧ n - p (n - n) = n ∧
    (∀ i, i < n → ∃ a b, a ≤ n ∧ b ≤ n ∧ S (a + b) ∧
        (n - p (n - i)) + (n - p (n - (i + 1))) + (a + b) = 2 * n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i _; omega
  · intro i j hi hj e
    have b1 := hb (n - i) (by omega)
    have b2 := hb (n - j) (by omega)
    have := hinj (n - i) (n - j) (by omega) (by omega) (by omega)
    omega
  · rw [Nat.sub_zero, hn, Nat.sub_self]
  · rw [Nat.sub_self, h0, Nat.sub_zero]
  · intro i hi
    have hs := hstep (n - (i + 1)) (by omega)
    have e : n - (i + 1) + 1 = n - i := by omega
    rw [e] at hs
    have b1 := hb (n - i) (by omega)
    have b2 := hb (n - (i + 1)) (by omega)
    exact ⟨p (n - (i + 1)), p (n - i), b2, b1, hs, by omega⟩

/-! ## gcd facts -/

theorem gcd_add_left_eq (a k : Nat) : Nat.gcd (a + k) a = Nat.gcd (a % k) k := by
  rw [Nat.gcd_self_add_left, Nat.gcd_rec]

theorem gcd_add_right_eq (a k : Nat) : Nat.gcd a (a + k) = Nat.gcd (a % k) k := by
  rw [Nat.gcd_self_add_right, Nat.gcd_comm, Nat.gcd_rec]

/-- `gcd x y = 1` when `x = y + k` and `gcd (y mod k) k = 1`. -/
theorem gcd_one_left_add (x y k : Nat) (hx : x = y + k) (hg : Nat.gcd (y % k) k = 1) :
    Nat.gcd x y = 1 := by
  subst hx; rw [gcd_add_left_eq]; exact hg

/-- `gcd x y = 1` when `y = x + k` and `gcd (x mod k) k = 1`. -/
theorem gcd_one_right_add (x y k : Nat) (hy : y = x + k) (hg : Nat.gcd (x % k) k = 1) :
    Nat.gcd x y = 1 := by
  subst hy; rw [gcd_add_right_eq]; exact hg

/-- `gcd x y = 1` when `y = r + x * q` and `gcd x r = 1`. -/
theorem gcd_one_right_mul (x y r q : Nat) (hy : y = r + x * q) (hg : Nat.gcd x r = 1) :
    Nat.gcd x y = 1 := by
  subst hy; rw [Nat.gcd_add_mul_left_right]; exact hg

theorem cop1 (x : Nat) : Nat.gcd (x % 1) 1 = 1 := by
  rw [Nat.mod_one]; decide

theorem cop2 (x : Nat) (h : x % 2 = 1) : Nat.gcd (x % 2) 2 = 1 := by
  rw [h]; decide

theorem cop3 (x : Nat) (h : x % 3 ≠ 0) : Nat.gcd (x % 3) 3 = 1 := by
  have : x % 3 = 1 ∨ x % 3 = 2 := by omega
  rcases this with e | e <;> rw [e] <;> decide

theorem cop4 (x : Nat) (h : x % 2 = 1) : Nat.gcd (x % 4) 4 = 1 := by
  have : x % 4 = 1 ∨ x % 4 = 3 := by omega
  rcases this with e | e <;> rw [e] <;> decide

/-! ### Admissible sums for the moduli `n - 1`, `n + 1` -/

/-- `s` is admissible for Sun's conjecture: coprime to `n - 1` and `n + 1`. -/
abbrev Good (n s : Nat) : Prop := Nat.gcd s (n - 1) = 1 ∧ Nat.gcd s (n + 1) = 1

theorem good_one (n : Nat) : Good n 1 := ⟨Nat.gcd_one_left _, Nat.gcd_one_left _⟩

theorem good_n (n : Nat) (h : 1 ≤ n) : Good n n :=
  ⟨gcd_one_left_add n (n - 1) 1 (by omega) (cop1 _),
   gcd_one_right_add n (n + 1) 1 rfl (cop1 _)⟩

theorem good_add3 (n : Nat) (h : 2 ≤ n) (he : n % 2 = 0) : Good n (n + 3) :=
  ⟨gcd_one_left_add (n + 3) (n - 1) 4 (by omega) (cop4 _ (by omega)),
   gcd_one_left_add (n + 3) (n + 1) 2 (by omega) (cop2 _ (by omega))⟩

theorem good_sub3 (n : Nat) (h : 4 ≤ n) (he : n % 2 = 0) : Good n (n - 3) :=
  ⟨gcd_one_right_add (n - 3) (n - 1) 2 (by omega) (cop2 _ (by omega)),
   gcd_one_right_add (n - 3) (n + 1) 4 (by omega) (cop4 _ (by omega))⟩

theorem good_add2 (n : Nat) (h : 1 ≤ n) (h3 : n % 3 ≠ 1) : Good n (n + 2) :=
  ⟨gcd_one_left_add (n + 2) (n - 1) 3 (by omega) (cop3 _ (by omega)),
   gcd_one_left_add (n + 2) (n + 1) 1 (by omega) (cop1 _)⟩

theorem good_sub2 (n : Nat) (h : 3 ≤ n) (h3 : n % 3 ≠ 2) : Good n (n - 2) :=
  ⟨gcd_one_right_add (n - 2) (n - 1) 1 (by omega) (cop1 _),
   gcd_one_right_add (n - 2) (n + 1) 3 (by omega) (cop3 _ (by omega))⟩

theorem good_two_mul_sub1 (n : Nat) (h : 1 ≤ n) (h3 : n % 3 ≠ 2) : Good n (2 * n - 1) := by
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · have e : n = 1 := by omega
    subst e; decide
  · refine ⟨?_, ?_⟩
    · rw [show 2 * n - 1 = 1 + (n - 1) * 2 by omega, Nat.gcd_add_mul_left_left]
      exact Nat.gcd_one_left _
    · rw [show 2 * n - 1 = (n + 1) + (n - 2) by omega, Nat.gcd_self_add_left]
      exact gcd_one_right_add (n - 2) (n + 1) 3 (by omega) (cop3 _ (by omega))

/-! ### Admissible sums for the moduli `2n - 1`, `2n + 1` -/

/-- `s` is admissible for the companion conjecture: coprime to `2n - 1` and `2n + 1`. -/
abbrev Good2 (n s : Nat) : Prop := Nat.gcd s (2 * n - 1) = 1 ∧ Nat.gcd s (2 * n + 1) = 1

theorem good2_n (n : Nat) (h : 1 ≤ n) : Good2 n n :=
  ⟨gcd_one_right_mul n (2 * n - 1) (n - 1) 1 (by omega)
      (gcd_one_left_add n (n - 1) 1 (by omega) (cop1 _)),
   gcd_one_right_mul n (2 * n + 1) 1 2 (by omega) (Nat.gcd_one_right _)⟩

/-- `s = n + 1` is admissible when `n % 3 ≠ 2`. -/
theorem good2_add1 (n : Nat) (h : 1 ≤ n) (h3 : n % 3 ≠ 2) : Good2 n (n + 1) := by
  refine ⟨?_, gcd_one_right_mul (n + 1) (2 * n + 1) n 1 (by omega)
      (gcd_one_left_add (n + 1) n 1 rfl (cop1 _))⟩
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · have e : n = 1 := by omega
    subst e; decide
  · -- gcd (n+1) (2n-1) = gcd (n+1) (n-2) = gcd (n-2) ((n-2)+3)
    rw [show 2 * n - 1 = (n - 2) + (n + 1) * 1 by omega, Nat.gcd_add_mul_left_right,
      Nat.gcd_comm]
    exact gcd_one_right_add (n - 2) (n + 1) 3 (by omega) (cop3 _ (by omega))

/-- `s = n - 1` is admissible when `n % 3 ≠ 1`. -/
theorem good2_sub1 (n : Nat) (h : 2 ≤ n) (h3 : n % 3 ≠ 1) : Good2 n (n - 1) :=
  ⟨gcd_one_right_mul (n - 1) (2 * n - 1) n 1 (by omega)
      (gcd_one_right_add (n - 1) n 1 (by omega) (cop1 _)),
   gcd_one_right_mul (n - 1) (2 * n + 1) (n + 2) 1 (by omega)
      (gcd_one_right_add (n - 1) (n + 2) 3 (by omega) (cop3 _ (by omega)))⟩

/-- `s` with `2 s = n` (i.e. `s = n / 2` for even `n`) is admissible. -/
theorem good2_half (n s : Nat) (hs : 2 * s = n) (h : 1 ≤ s) : Good2 n s :=
  ⟨gcd_one_right_mul s (2 * n - 1) (s - 1) 3 (by omega)
      (gcd_one_left_add s (s - 1) 1 (by omega) (cop1 _)),
   gcd_one_right_mul s (2 * n + 1) 1 4 (by omega) (Nat.gcd_one_right _)⟩

/-- `s` with `2 s = n + 1` (i.e. `s = (n + 1) / 2` for odd `n`) is admissible when `n % 3 ≠ 2`. -/
theorem good2_half_up (n s : Nat) (hs : 2 * s = n + 1) (h3 : n % 3 ≠ 2) : Good2 n s := by
  refine ⟨?_, gcd_one_right_mul s (2 * n + 1) (s - 1) 3 (by omega)
      (gcd_one_left_add s (s - 1) 1 (by omega) (cop1 _))⟩
  rcases Nat.lt_or_ge s 3 with h1 | h2
  · have e : s = 1 ∨ s = 2 := by omega
    rcases e with e | e <;> subst e
    · exact Nat.gcd_one_left _
    · have e' : 2 * n - 1 = 5 := by omega
      rw [e']; decide
  · -- 2n - 1 = 4s - 3 = (s - 3) + 3 s
    exact gcd_one_right_mul s (2 * n - 1) (s - 3) 3 (by omega)
      (gcd_one_left_add s (s - 3) 3 (by omega) (cop3 _ (by omega)))

/-- `s` with `2 s + 1 = n` (i.e. `s = (n - 1) / 2` for odd `n`) is admissible when `n % 3 ≠ 1`. -/
theorem good2_half_down (n s : Nat) (hs : 2 * s + 1 = n) (h3 : n % 3 ≠ 1) :
    Good2 n s :=
  ⟨gcd_one_right_mul s (2 * n - 1) 1 4 (by omega) (Nat.gcd_one_right _),
   gcd_one_right_mul s (2 * n + 1) 3 4 (by omega)
      (by rw [Nat.gcd_comm, Nat.gcd_rec]; exact cop3 _ (by omega))⟩

theorem good2_four (n : Nat) (h : 1 ≤ n) : Good2 n 4 :=
  ⟨by rw [Nat.gcd_rec]; exact cop4 _ (by omega), by rw [Nat.gcd_rec]; exact cop4 _ (by omega)⟩

theorem good2_two_mul_sub3 (n : Nat) (h : 2 ≤ n) : Good2 n (2 * n - 3) :=
  ⟨gcd_one_right_add (2 * n - 3) (2 * n - 1) 2 (by omega) (cop2 _ (by omega)),
   gcd_one_right_add (2 * n - 3) (2 * n + 1) 4 (by omega) (cop4 _ (by omega))⟩

/-! ## Conjecture (1), odd n: Sun's permutations -/

/-- Sun's permutation for odd `n` with `n % 3 ≠ 2`:  `0, n-2, 2, n-4, 4, …, 1, n-1, n`. -/
def oddA (n i : Nat) : Nat :=
  if i = n then n else if i % 2 = 0 then i else n - 1 - i

/-- Sun's permutation for odd `n` with `n % 3 ≠ 1`:  `0, 1, n-1, 3, n-3, …, n-2, 2, n`. -/
def oddB (n i : Nat) : Nat :=
  if i = 0 then 0 else if i = n then n else if i % 2 = 1 then i else n + 1 - i

set_option maxHeartbeats 2000000 in
theorem oddA_ok (n : Nat) (h1 : 1 ≤ n) (hodd : n % 2 = 1) (h3 : n % 3 ≠ 2) :
    SunFun n (n - 1) (n + 1) (oddA n) := by
  refine sunFun_of n _ _ (oddA n) (fun s => s + 2 = n ∨ s = n ∨ s + 1 = 2 * n)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rcases hs with e | e | e
    · have : s = n - 2 := by omega
      subst this; exact good_sub2 n (by omega) h3
    · rw [e]; exact good_n n h1
    · have : s = 2 * n - 1 := by omega
      subst this; exact good_two_mul_sub1 n h1 h3
  · intro i hi; unfold oddA; repeat' split
    all_goals omega
  · intro i j hi hj h; unfold oddA at h; repeat' (split at h)
    all_goals omega
  · unfold oddA; repeat' split
    all_goals omega
  · unfold oddA; simp
  · intro i hi; unfold oddA; repeat' split
    all_goals omega
  · unfold oddA; repeat' split
    all_goals omega

set_option maxHeartbeats 2000000 in
theorem oddB_ok (n : Nat) (h1 : 3 ≤ n) (hodd : n % 2 = 1) (h3 : n % 3 ≠ 1) :
    SunFun n (n - 1) (n + 1) (oddB n) := by
  refine sunFun_of n _ _ (oddB n) (fun s => s = 1 ∨ s = n ∨ s = n + 2) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rcases hs with e | e | e
    · subst e; exact good_one n
    · rw [e]; exact good_n n (by omega)
    · subst e; exact good_add2 n (by omega) h3
  · intro i hi; unfold oddB; repeat' split
    all_goals omega
  · intro i j hi hj h; unfold oddB at h; repeat' (split at h)
    all_goals omega
  · unfold oddB; simp
  · unfold oddB; repeat' split
    all_goals omega
  · intro i hi; unfold oddB; repeat' split
    all_goals omega
  · unfold oddB; repeat' split
    all_goals omega

/-! ## Conjecture (1), even n: new permutations -/

/-- New permutation for `n ≡ 0 (mod 4)`, `n ≥ 8`, `m = n/2`:
`0, 1, n-1, 3, n-3, …, m+5, m-3,  m, m+3, m-1, m+1,  m+2, m-2, m+4, m-4, …, n-2, 2, n`.
Adjacent sums: `1`, then alternately `n`, `n+2`, …, then `n-3, n+3, n+2, n, n+3`,
then alternately `n`, `n+2`, …, and finally `n + 0 = n`. -/
def evenA (n i : Nat) : Nat :=
  if i = 0 then 0
  else if i + 3 ≤ n / 2 then (if i % 2 = 1 then i else n + 1 - i)
  else if i = n / 2 - 2 then n / 2
  else if i = n / 2 - 1 then n / 2 + 3
  else if i = n / 2 then n / 2 - 1
  else if i = n / 2 + 1 then n / 2 + 1
  else (if i % 2 = 0 then i else n + 1 - i)

/-- New permutation for `n ≡ 2 (mod 4)`, `n ≥ 10`, `m = n/2` (odd):
`0, 1, n-1, 3, n-3, …, m-2, m+2,  m+1, m-1, m+3, m, m-3,  m+5, m-5, m+7, m-7, …, n-2, 2, n`;
precisely: position `i ↦ i` (odd `i`), `i ↦ n+1-i` (even `i`) for `1 ≤ i ≤ m-1`; then the values
`m+1, m-1, m+3, m, m-3` at positions `m, …, m+4`; then `i ↦ i` (even `i`), `i ↦ n+1-i` (odd `i`)
for `m+5 ≤ i ≤ n`.  Adjacent sums: `1`, alternately `n`, `n+2`, …, then
`n+3, n, n+2, n+3, n-3, n+2`, alternately `n`, `n+2`, …, and finally `n + 0 = n`. -/
def evenB (n i : Nat) : Nat :=
  if i = 0 then 0
  else if i + 1 ≤ n / 2 then (if i % 2 = 1 then i else n + 1 - i)
  else if i = n / 2 then n / 2 + 1
  else if i = n / 2 + 1 then n / 2 - 1
  else if i = n / 2 + 2 then n / 2 + 3
  else if i = n / 2 + 3 then n / 2
  else if i = n / 2 + 4 then n / 2 - 3
  else (if i % 2 = 0 then i else n + 1 - i)

/-- The permutation `0, 1, 2, 4, 5, 3, 6` for `n = 6`. -/
def six (i : Nat) : Nat :=
  if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 2 else if i = 3 then 4
  else if i = 4 then 5 else if i = 5 then 3 else 6

/-- The admissible sums used by `evenA`/`evenB`. -/
def SE (n s : Nat) : Prop := s = 1 ∨ s = n ∨ s = n + 2 ∨ s = n + 3 ∨ s + 3 = n

theorem SE_good (n : Nat) (h : 8 ≤ n) (he : n % 2 = 0) (h3 : n % 3 ≠ 1) :
    ∀ s, SE n s → Good n s := by
  intro s hs
  rcases hs with e | e | e | e | e
  · subst e; exact good_one n
  · rw [e]; exact good_n n (by omega)
  · subst e; exact good_add2 n (by omega) h3
  · subst e; exact good_add3 n (by omega) he
  · have : s = n - 3 := by omega
    subst this; exact good_sub3 n (by omega) he

set_option maxHeartbeats 4000000 in
theorem evenA_props (n : Nat) (h : 8 ≤ n) (h4 : n % 4 = 0) :
    (∀ i, i ≤ n → evenA n i ≤ n) ∧
    (∀ i j, i ≤ n → j ≤ n → evenA n i = evenA n j → i = j) ∧
    evenA n 0 = 0 ∧ evenA n n = n ∧
    (∀ i, i < n → SE n (evenA n i + evenA n (i + 1))) ∧
    SE n (evenA n n + evenA n 0) := by
  unfold SE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; unfold evenA; repeat' split
    all_goals omega
  · intro i j hi hj e; unfold evenA at e; repeat' (split at e)
    all_goals omega
  · unfold evenA; simp
  · unfold evenA; repeat' split
    all_goals omega
  · intro i hi; unfold evenA; repeat' split
    all_goals omega
  · unfold evenA; repeat' split
    all_goals omega

set_option maxHeartbeats 4000000 in
theorem evenB_props (n : Nat) (h : 10 ≤ n) (h4 : n % 4 = 2) :
    (∀ i, i ≤ n → evenB n i ≤ n) ∧
    (∀ i j, i ≤ n → j ≤ n → evenB n i = evenB n j → i = j) ∧
    evenB n 0 = 0 ∧ evenB n n = n ∧
    (∀ i, i < n → SE n (evenB n i + evenB n (i + 1))) ∧
    SE n (evenB n n + evenB n 0) := by
  unfold SE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; unfold evenB; repeat' split
    all_goals omega
  · intro i j hi hj e; unfold evenB at e; repeat' (split at e)
    all_goals omega
  · unfold evenB; simp
  · unfold evenB; repeat' split
    all_goals omega
  · intro i hi; unfold evenB; repeat' split
    all_goals omega
  · unfold evenB; repeat' split
    all_goals omega

/-- Combined even construction, for even `n ≥ 8`. -/
theorem even_props (n : Nat) (h : 8 ≤ n) (he : n % 2 = 0) :
    ∃ p : Nat → Nat,
    (∀ i, i ≤ n → p i ≤ n) ∧
    (∀ i j, i ≤ n → j ≤ n → p i = p j → i = j) ∧
    p 0 = 0 ∧ p n = n ∧
    (∀ i, i < n → SE n (p i + p (i + 1))) ∧
    SE n (p n + p 0) := by
  rcases Nat.lt_or_ge n 10 with h10 | h10
  · have e : n = 8 := by omega
    subst e; exact ⟨evenA 8, evenA_props 8 (by omega) (by omega)⟩
  · by_cases h4 : n % 4 = 0
    · exact ⟨evenA n, evenA_props n h h4⟩
    · exact ⟨evenB n, evenB_props n h10 (by omega)⟩

theorem even_ok (n : Nat) (h : 8 ≤ n) (he : n % 2 = 0) : ∃ p, SunFun n (n - 1) (n + 1) p := by
  obtain ⟨p, hb, hinj, h0, hn, hstep, hlast⟩ := even_props n h he
  by_cases h3 : n % 3 = 1
  · -- mirrored permutation i ↦ n - p (n - i); sums become 2n - s ∈ {2n-1, n, n-2, n-3, n+3}
    obtain ⟨mb, minj, m0, mn, mstep⟩ := mirror_props n p (SE n) hb hinj h0 hn hstep
    refine ⟨fun i => n - p (n - i), ?_⟩
    refine sunFun_of n _ _ (fun i => n - p (n - i))
      (fun s => s + 1 = 2 * n ∨ s = n ∨ s + 2 = n ∨ s + 3 = n ∨ s = n + 3)
      ?_ mb minj m0 mn ?_ ?_
    · intro s hs
      rcases hs with e | e | e | e | e
      · have : s = 2 * n - 1 := by omega
        subst this; exact good_two_mul_sub1 n (by omega) (by omega)
      · rw [e]; exact good_n n (by omega)
      · have : s = n - 2 := by omega
        subst this; exact good_sub2 n (by omega) (by omega)
      · have : s = n - 3 := by omega
        subst this; exact good_sub3 n (by omega) he
      · subst e; exact good_add3 n (by omega) he
    · intro i hi
      obtain ⟨a, b, ha, hb', hs, e⟩ := mstep i hi
      unfold SE at hs
      omega
    · rw [Nat.sub_self, Nat.sub_zero, h0, hn]; omega
  · exact ⟨p, sunFun_of n _ _ p (SE n) (SE_good n h he h3) hb hinj h0 hn hstep hlast⟩

theorem six_ok : SunFun 6 (6 - 1) (6 + 1) six := by
  refine sunFun_of 6 _ _ six (fun s => s = 1 ∨ s = 3 ∨ s = 6 ∨ s = 8 ∨ s = 9)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rcases hs with e | e | e | e | e <;> subst e <;> decide
  · intro i hi; unfold six; repeat' split
    all_goals omega
  · intro i j hi hj h; unfold six at h; repeat' (split at h)
    all_goals omega
  · decide
  · decide
  · intro i hi; unfold six; repeat' split
    all_goals omega
  · decide

/-! ## Conjecture (2) (moduli 2n-1, 2n+1): new permutations -/

/-- Even `n` with `n % 3 ≠ 2`, `m = n/2`:  `0, m, m+1, m-1, m+2, m-2, …, n-1, 1, n`.
Adjacent sums: `m`, then alternately `n+1`, `n`, …, `n+1`, and `n + 0 = n`. -/
def compA (n i : Nat) : Nat :=
  if i = 0 then 0 else if i = n then n
  else if i % 2 = 1 then n / 2 - (i - 1) / 2 else n / 2 + i / 2

/-- Odd `n` with `n % 3 ≠ 2`, `m = (n-1)/2`:  `0, m+1, m, m+2, m-1, …, n-1, 1, n`.
Adjacent sums: `(n+1)/2`, then alternately `n`, `n+1`, …, `n+1`, and `n + 0 = n`. -/
def compB (n i : Nat) : Nat :=
  if i = 0 then 0 else if i = n then n
  else if i % 2 = 1 then n / 2 + 1 + (i - 1) / 2 else n / 2 + 1 - i / 2

/-- `n % 3 = 2`, `n ≥ 8`, `m = ⌊n/2⌋`:  `0`, a zig-zag `m, m∓1, m±1, …, 4, n-4, 3` with sums
alternately `n - 1`, `n` (positions `1 … n-6`), then `1, n-1, n-2, 2, n-3, n`.
Adjacent sums: `m`, alternately `n-1`/`n`, then `4, n, 2n-3, n, n-1, 2n-3`, and `n + 0 = n`. -/
def compC (n i : Nat) : Nat :=
  if i = 0 then 0
  else if i + 6 ≤ n then
    (if n % 2 = 0 then (if i % 2 = 1 then n / 2 + (i - 1) / 2 else n / 2 - i / 2)
     else (if i % 2 = 1 then n / 2 - (i - 1) / 2 else n / 2 + i / 2))
  else if i + 5 = n then 1
  else if i + 4 = n then n - 1
  else if i + 3 = n then n - 2
  else if i + 2 = n then 2
  else if i + 1 = n then n - 3
  else n

/-- The permutation `0, 1, 4, 3, 2, 5` for `n = 5` (moduli 9 and 11). -/
def five (i : Nat) : Nat :=
  if i = 0 then 0 else if i = 1 then 1 else if i = 2 then 4 else if i = 3 then 3
  else if i = 4 then 2 else 5

set_option maxHeartbeats 2000000 in
theorem compA_ok (n : Nat) (h : 2 ≤ n) (he : n % 2 = 0) (h3 : n % 3 ≠ 2) :
    SunFun n (2 * n - 1) (2 * n + 1) (compA n) := by
  refine sunFun_of n _ _ (compA n) (fun s => 2 * s = n ∨ s = n + 1 ∨ s = n)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rcases hs with e | e | e
    · exact good2_half n s e (by omega)
    · subst e; exact good2_add1 n (by omega) h3
    · rw [e]; exact good2_n n (by omega)
  · intro i hi; unfold compA; repeat' split
    all_goals omega
  · intro i j hi hj e; unfold compA at e; repeat' (split at e)
    all_goals omega
  · unfold compA; simp
  · unfold compA; repeat' split
    all_goals omega
  · intro i hi; unfold compA; repeat' split
    all_goals omega
  · unfold compA; repeat' split
    all_goals omega

set_option maxHeartbeats 2000000 in
theorem compB_ok (n : Nat) (h : 1 ≤ n) (ho : n % 2 = 1) (h3 : n % 3 ≠ 2) :
    SunFun n (2 * n - 1) (2 * n + 1) (compB n) := by
  refine sunFun_of n _ _ (compB n) (fun s => 2 * s = n + 1 ∨ s = n + 1 ∨ s = n)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rcases hs with e | e | e
    · exact good2_half_up n s e h3
    · subst e; exact good2_add1 n (by omega) h3
    · rw [e]; exact good2_n n (by omega)
  · intro i hi; unfold compB; repeat' split
    all_goals omega
  · intro i j hi hj e; unfold compB at e; repeat' (split at e)
    all_goals omega
  · unfold compB; simp
  · unfold compB; repeat' split
    all_goals omega
  · intro i hi; unfold compB; repeat' split
    all_goals omega
  · unfold compB; repeat' split
    all_goals omega

set_option maxHeartbeats 4000000 in
theorem compC_ok (n : Nat) (h : 8 ≤ n) (h3 : n % 3 = 2) :
    SunFun n (2 * n - 1) (2 * n + 1) (compC n) := by
  refine sunFun_of n _ _ (compC n)
    (fun s => (2 * s = n ∨ 2 * s + 1 = n) ∨ s + 1 = n ∨ s = n ∨ s = 4 ∨ s + 3 = 2 * n)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rcases hs with (e | e) | e | e | e | e
    · exact good2_half n s e (by omega)
    · exact good2_half_down n s e (by omega)
    · have : s = n - 1 := by omega
      subst this; exact good2_sub1 n (by omega) (by omega)
    · rw [e]; exact good2_n n (by omega)
    · subst e; exact good2_four n (by omega)
    · have : s = 2 * n - 3 := by omega
      subst this; exact good2_two_mul_sub3 n (by omega)
  · intro i hi; unfold compC; repeat' split
    all_goals omega
  · intro i j hi hj e; unfold compC at e; repeat' (split at e)
    all_goals omega
  · unfold compC; simp
  · unfold compC; repeat' split
    all_goals omega
  · intro i hi; unfold compC; repeat' split
    all_goals omega
  · unfold compC; repeat' split
    all_goals omega

theorem five_ok : SunFun 5 (2 * 5 - 1) (2 * 5 + 1) five := by
  refine sunFun_of 5 _ _ five (fun s => s = 1 ∨ s = 5 ∨ s = 7) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro s hs
    rcases hs with e | e | e <;> subst e <;> decide
  · intro i hi; unfold five; repeat' split
    all_goals omega
  · intro i j hi hj h; unfold five at h; repeat' (split at h)
    all_goals omega
  · decide
  · decide
  · intro i hi; unfold five; repeat' split
    all_goals omega
  · decide

/-! ## Impossibility for n = 2 and n = 4 -/

/-- For `n = 2` the only candidate is `0, 1, 2`; its adjacent sum `1 + 2 = 3` must therefore be
coprime to both moduli.  (Used with `3 = n + 1` and with `3 = 2n - 1`.) -/
theorem two_forced (A B : Nat) (p : Nat → Nat) (hp : SunFun 2 A B p) :
    Nat.gcd 3 A = 1 ∧ Nat.gcd 3 B = 1 := by
  obtain ⟨hb, hinj, h0, h2, hs⟩ := hp
  have b1 := hb 1 (by omega)
  have i10 : p 1 ≠ p 0 := fun e => by have := hinj 1 0 (by omega) (by omega) e; omega
  have i12 : p 1 ≠ p 2 := fun e => by have := hinj 1 2 (by omega) (by omega) e; omega
  have e1 : p 1 = 1 := by omega
  have := hs 1 (by omega)
  simp only [show (1 + 1) % (2 + 1) = 2 by decide, e1, h2] at this
  exact this

theorem not_two (p : Nat → Nat) : ¬ SunFun 2 (2 - 1) (2 + 1) p := by
  intro hp
  have := (two_forced _ _ p hp).2
  exact absurd this (by decide)

theorem not_two' (p : Nat → Nat) : ¬ SunFun 2 (2 * 2 - 1) (2 * 2 + 1) p := by
  intro hp
  have := (two_forced _ _ p hp).1
  exact absurd this (by decide)

theorem not_four (p : Nat → Nat) : ¬ SunFun 4 (4 - 1) (4 + 1) p := by
  intro ⟨hb, hinj, h0, h4, hs⟩
  have ne : ∀ i j, i ≤ 4 → j ≤ 4 → i ≠ j → p i ≠ p j :=
    fun i j hi hj hij e => hij (hinj i j hi hj e)
  have b1 := hb 1 (by omega); have b2 := hb 2 (by omega); have b3 := hb 3 (by omega)
  have n10 := ne 1 0 (by omega) (by omega) (by omega)
  have n14 := ne 1 4 (by omega) (by omega) (by omega)
  have n20 := ne 2 0 (by omega) (by omega) (by omega)
  have n24 := ne 2 4 (by omega) (by omega) (by omega)
  have n30 := ne 3 0 (by omega) (by omega) (by omega)
  have n34 := ne 3 4 (by omega) (by omega) (by omega)
  have n12 := ne 1 2 (by omega) (by omega) (by omega)
  have n13 := ne 1 3 (by omega) (by omega) (by omega)
  have n23 := ne 2 3 (by omega) (by omega) (by omega)
  have s1 := hs 1 (by omega)
  have s3 := hs 3 (by omega)
  simp only [show (1 + 1) % (4 + 1) = 2 by decide, show (3 + 1) % (4 + 1) = 4 by decide,
    show 4 - 1 = 3 by decide, show 4 + 1 = 5 by decide, h4] at s1 s3
  rw [h0] at n10 n20 n30
  rw [h4] at n14 n24 n34
  generalize p 1 = a at *
  generalize p 2 = b at *
  generalize p 3 = c at *
  obtain ⟨g1, _⟩ := s1
  obtain ⟨g2, g3⟩ := s3
  -- c + 4 must avoid multiples of 3 and 5, so c = 3; then {a, b} = {1, 2} and a + b = 3
  have hc : c = 3 := by
    rcases (by omega : c = 1 ∨ c = 2 ∨ c = 3) with e | e | e
    · rw [e] at g3; exact absurd g3 (by decide)
    · rw [e] at g2; exact absurd g2 (by decide)
    · exact e
  have hab : a + b = 3 := by omega
  rw [hab] at g1
  exact absurd g1 (by decide)

/-! ## Main theorems, function form -/

/-- **Sun's conjecture (OEIS A228886), function form.** -/
theorem sun_conjecture_fun (n : Nat) (hn : 1 ≤ n) :
    (∃ p, SunFun n (n - 1) (n + 1) p) ↔ (n ≠ 2 ∧ n ≠ 4) := by
  constructor
  · intro ⟨p, hp⟩
    refine ⟨fun e => ?_, fun e => ?_⟩
    · subst e; exact not_two p hp
    · subst e; exact not_four p hp
  · intro ⟨h2, h4⟩
    rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · -- even n
      rcases Nat.lt_or_ge n 8 with h8 | h8
      · have e : n = 6 := by omega
        subst e; exact ⟨six, six_ok⟩
      · exact even_ok n h8 he
    · -- odd n (Sun)
      by_cases h3 : n % 3 = 2
      · exact ⟨oddB n, oddB_ok n (by omega) ho (by omega)⟩
      · exact ⟨oddA n, oddA_ok n hn ho h3⟩

/-- **Sun's companion conjecture (moduli 2n-1, 2n+1), function form.** -/
theorem sun_companion_fun (n : Nat) (hn : 1 ≤ n) :
    (∃ p, SunFun n (2 * n - 1) (2 * n + 1) p) ↔ n ≠ 2 := by
  constructor
  · intro ⟨p, hp⟩ e
    subst e; exact not_two' p hp
  · intro h2
    by_cases h3 : n % 3 = 2
    · rcases Nat.lt_or_ge n 8 with h8 | h8
      · have e : n = 5 := by omega
        subst e; exact ⟨five, five_ok⟩
      · exact ⟨compC n, compC_ok n h8 h3⟩
    · rcases Nat.mod_two_eq_zero_or_one n with he | ho
      · exact ⟨compA n, compA_ok n (by omega) he h3⟩
      · exact ⟨compB n, compB_ok n hn ho h3⟩

/-! ## From functions to lists and back -/

/-- Pigeonhole: an injective self-map of `{0,…,n}` is onto. -/
theorem surj_of_inj : ∀ (n : Nat) (p : Nat → Nat), (∀ i, i ≤ n → p i ≤ n) →
    (∀ i j, i ≤ n → j ≤ n → p i = p j → i = j) → ∀ v, v ≤ n → ∃ i, i ≤ n ∧ p i = v := by
  intro n
  induction n with
  | zero =>
    intro p hb _ v hv
    exact ⟨0, Nat.le_refl 0, by have := hb 0 (Nat.le_refl 0); omega⟩
  | succ n ih =>
    intro p hb hinj v hv
    let q : Nat → Nat := fun i => if p i = n + 1 then p (n + 1) else p i
    have hq : ∀ i, q i = if p i = n + 1 then p (n + 1) else p i := fun _ => rfl
    have top : ∀ i, i ≤ n → p i = n + 1 → p (n + 1) ≤ n := by
      intro i hi e
      have b := hb (n + 1) (Nat.le_refl _)
      have : p (n + 1) ≠ n + 1 := fun e' => by
        have := hinj i (n + 1) (by omega) (Nat.le_refl _) (by rw [e, e']); omega
      omega
    have qb : ∀ i, i ≤ n → q i ≤ n := by
      intro i hi
      rw [hq]
      split
      · exact top i hi (by assumption)
      · have := hb i (by omega); omega
    have qinj : ∀ i j, i ≤ n → j ≤ n → q i = q j → i = j := by
      intro i j hi hj e
      rw [hq, hq] at e
      split at e <;> split at e
      · exact hinj i j (by omega) (by omega) (by omega)
      · have := hinj (n + 1) j (Nat.le_refl _) (by omega) e; omega
      · have := hinj i (n + 1) (by omega) (Nat.le_refl _) e; omega
      · exact hinj i j (by omega) (by omega) e
    rcases Nat.lt_or_ge v (n + 1) with hv' | hv'
    · obtain ⟨i, hi, e⟩ := ih q qb qinj v (by omega)
      rw [hq] at e
      split at e
      · exact ⟨n + 1, Nat.le_refl _, e⟩
      · exact ⟨i, by omega, e⟩
    · have ev : v = n + 1 := by omega
      subst ev
      by_cases hp : p (n + 1) = n + 1
      · exact ⟨n + 1, Nat.le_refl _, hp⟩
      · have b := hb (n + 1) (Nat.le_refl _)
        obtain ⟨i, hi, e⟩ := ih q qb qinj (p (n + 1)) (by omega)
        rw [hq] at e
        split at e
        · exact ⟨i, by omega, by assumption⟩
        · have := hinj i (n + 1) (by omega) (Nat.le_refl _) e; omega

theorem getD_map_range (p : Nat → Nat) (n i : Nat) (hi : i < n) :
    ((List.range n).map p).getD i 0 = p i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem list_of_fun (n A B : Nat) (p : Nat → Nat) (hp : SunFun n A B p) :
    SunCycle n A B ((List.range (n + 1)).map p) := by
  obtain ⟨hb, hinj, h0, hn, hs⟩ := hp
  have hnd : ((List.range (n + 1)).map p).Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ List.pairwise_lt_range
    intro a b ha hb' hab e
    rw [List.mem_range] at ha hb'
    have := hinj a b (by omega) (by omega) e
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [List.perm_ext_iff_of_nodup hnd List.nodup_range]
    intro a
    rw [List.mem_map, List.mem_range]
    constructor
    · intro ⟨i, hi, e⟩
      rw [List.mem_range] at hi
      have := hb i (by omega); omega
    · intro ha
      obtain ⟨i, hi, e⟩ := surj_of_inj n p hb hinj a (by omega)
      exact ⟨i, List.mem_range.2 (by omega), e⟩
  · rw [List.head?_map, List.head?_range]; simp [h0]
  · rw [List.getLast?_map, List.getLast?_range]; simp [hn]
  · intro s hsm
    unfold cyclicSums at hsm
    rw [List.mem_map] at hsm
    obtain ⟨i, hi, e⟩ := hsm
    rw [List.length_map, List.length_range, List.mem_range] at *
    have hmod : (i + 1) % (n + 1) < n + 1 := Nat.mod_lt _ (by omega)
    rw [getD_map_range p (n + 1) i hi, getD_map_range p (n + 1) _ hmod] at e
    subst e
    exact hs i (by omega)

theorem fun_of_list (n A B : Nat) (l : List Nat) (hl : SunCycle n A B l) :
    SunFun n A B (fun i => l.getD i 0) := by
  obtain ⟨hperm, hhead, hlast, hs⟩ := hl
  have hlen : l.length = n + 1 := by rw [hperm.length_eq, List.length_range]
  have hnd : l.Nodup := hperm.nodup_iff.2 List.nodup_range
  have gd : ∀ i, (hi : i < l.length) → l.getD i 0 = l[i] := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    dsimp only
    have hi' : i < l.length := by omega
    rw [gd i hi']
    have := (hperm.mem_iff).1 (List.getElem_mem hi')
    rw [List.mem_range] at this; omega
  · intro i j hi hj e
    dsimp only at e
    have hi' : i < l.length := by omega
    have hj' : j < l.length := by omega
    rw [gd i hi', gd j hj'] at e
    have := (List.Nodup.getElem?_inj (xs := l) (i := i) (j := j) hi' hnd).1
    rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj', e] at this
    exact this rfl
  · simp only
    rw [List.head?_eq_getElem?] at hhead
    rw [List.getD_eq_getElem?_getD, hhead]; rfl
  · simp only
    rw [List.getLast?_eq_getElem?, hlen, Nat.add_sub_cancel] at hlast
    rw [List.getD_eq_getElem?_getD, hlast]; rfl
  · intro i hi
    apply hs
    unfold cyclicSums
    rw [List.mem_map]
    refine ⟨i, List.mem_range.2 (by omega), ?_⟩
    rw [hlen]

theorem exists_list_iff (n A B : Nat) :
    (∃ l, SunCycle n A B l) ↔ (∃ p, SunFun n A B p) := by
  constructor
  · intro ⟨l, hl⟩; exact ⟨_, fun_of_list n A B l hl⟩
  · intro ⟨p, hp⟩; exact ⟨_, list_of_fun n A B p hp⟩

/-! ## Main theorems -/

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

/-! ## Sanity checks (non-vacuity of the definitions) -/

example : SunCycle 6 (6 - 1) (6 + 1) [0, 1, 2, 4, 5, 3, 6] := by unfold SunCycle; decide
-- the gcd condition really bites: here the adjacent sum 1 + 4 = 5 is not coprime to n - 1 = 5
example : ¬ SunCycle 6 (6 - 1) (6 + 1) [0, 2, 1, 4, 5, 3, 6] := by unfold SunCycle; decide
-- the endpoint conditions really bite: a rotation of the good cycle (same cyclic sums) is rejected
example : ¬ SunCycle 6 (6 - 1) (6 + 1) [1, 2, 4, 5, 3, 6, 0] := by unfold SunCycle; decide
-- the permutation condition really bites
example : ¬ SunCycle 6 (6 - 1) (6 + 1) [0, 1, 2, 4, 6] := by unfold SunCycle; decide
-- companion, n = 8
example : SunCycle 8 (2 * 8 - 1) (2 * 8 + 1) [0, 4, 3, 1, 7, 6, 2, 5, 8] := by
  unfold SunCycle; decide

end A228886

/-! ## Outputs of the constructions and axioms -/

-- conjecture (1): the new even construction for n = 8, 10, 12 (n = 10 uses the mirror: 10 % 3 = 1)
#eval (List.range 9).map (A228886.evenA 8)
#eval (List.range 11).map (fun i => 10 - A228886.evenB 10 (10 - i))
#eval (List.range 13).map (A228886.evenA 12)
#eval A228886.cyclicSums ((List.range 13).map (A228886.evenA 12))
-- conjecture (2): n = 8, 11, 12
#eval (List.range 9).map (A228886.compC 8)
#eval (List.range 12).map (A228886.compC 11)
#eval (List.range 13).map (A228886.compA 12)

#print axioms A228886.sun_conjecture
#print axioms A228886.sun_companion
