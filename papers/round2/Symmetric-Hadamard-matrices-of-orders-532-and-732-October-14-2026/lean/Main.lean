import Mathlib

/-! # Symmetric Hadamard matrices of orders 532 = 4 * 133 and 732 = 4 * 183 (propus construction)

Agent B03, October 14 2026.  Part 1: general propus theorem.  Parts 2, 3: the explicit families. -/

/-!
# The propus construction of symmetric Hadamard matrices

For `v > 0`, sequences `a b d : ZMod v → ℤ` with entries `±1`, `a` symmetric, and
`PAF_a(t) + 2 PAF_b(t) + PAF_d(t) = 0` for all `t ≠ 0`, the propus array
```
  [ -A   BR   BR   DR ]
  [  BR  RD    A  -RB ]
  [  BR   A  -RD   RB ]
  [  DR -RB   RB    A ]
```
(`A, B, D` circulant with first rows `a, b, d`, `R` the back-circulant identity) is a symmetric
Hadamard matrix of order `4v`.  Indices: `Fin 4 × ZMod v`; circulant `A(i,k) = a(k-i)`,
`(AR)(i,k) = a(-i-k)`, `(RA)(i,k) = a(i+k)`.
-/

open Finset

namespace Propus

variable {v : ℕ} [NeZero v]

/-- periodic cross-correlation -/
def C (x y : ZMod v → ℤ) (t : ZMod v) : ℤ := ∑ u : ZMod v, x u * y (u + t)
/-- periodic convolution -/
def K (x y : ZMod v → ℤ) (t : ZMod v) : ℤ := ∑ u : ZMod v, x u * y (t - u)

lemma K_comm (x y : ZMod v → ℤ) (t : ZMod v) : K x y t = K y x t := by
  unfold K
  rw [← Equiv.sum_comp (Equiv.subLeft t)]
  apply Finset.sum_congr rfl
  intro u _
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  ring

lemma C_swap (x y : ZMod v → ℤ) (t : ZMod v) : C x y t = C y x (-t) := by
  unfold C
  conv_rhs => rw [← Equiv.sum_comp (Equiv.addRight t)]
  apply Finset.sum_congr rfl
  intro u _
  simp only [Equiv.coe_addRight, add_neg_cancel_right]
  ring

-- reindexing lemmas (k is the summation variable)
lemma sCC (x y : ZMod v → ℤ) (i j : ZMod v) :
    ∑ k : ZMod v, x (k - i) * y (k - j) = C x y (i - j) := by
  unfold C; rw [← Equiv.sum_comp (Equiv.addRight i)]
  apply Finset.sum_congr rfl; intro u _
  simp only [Equiv.coe_addRight]
  rw [show u + i - i = u by ring, show u + i - j = u + (i - j) by ring]

lemma sARAR (x y : ZMod v → ℤ) (i j : ZMod v) :
    ∑ k : ZMod v, x (-i - k) * y (-j - k) = C x y (i - j) := by
  unfold C; rw [← Equiv.sum_comp (Equiv.subLeft (-i))]
  apply Finset.sum_congr rfl; intro u _
  simp only [Equiv.subLeft_apply]
  rw [show -i - (-i - u) = u by ring, show -j - (-i - u) = u + (i - j) by ring]

lemma sRARA (x y : ZMod v → ℤ) (i j : ZMod v) :
    ∑ k : ZMod v, x (i + k) * y (j + k) = C x y (j - i) := by
  unfold C; rw [← Equiv.sum_comp (Equiv.subRight i)]
  apply Finset.sum_congr rfl; intro u _
  simp only [Equiv.subRight_apply]
  rw [show i + (u - i) = u by ring, show j + (u - i) = u + (j - i) by ring]

lemma sCAR (x y : ZMod v → ℤ) (i j : ZMod v) :
    ∑ k : ZMod v, x (k - i) * y (-j - k) = K x y (-i - j) := by
  unfold K; rw [← Equiv.sum_comp (Equiv.addRight i)]
  apply Finset.sum_congr rfl; intro u _
  simp only [Equiv.coe_addRight]
  rw [show u + i - i = u by ring, show -j - (u + i) = -i - j - u by ring]

lemma sARC (x y : ZMod v → ℤ) (i j : ZMod v) :
    ∑ k : ZMod v, x (-i - k) * y (k - j) = K x y (-i - j) := by
  unfold K; rw [← Equiv.sum_comp (Equiv.subLeft (-i))]
  apply Finset.sum_congr rfl; intro u _
  simp only [Equiv.subLeft_apply]
  rw [show -i - (-i - u) = u by ring, show -i - u - j = -i - j - u by ring]

lemma sCRA (x y : ZMod v → ℤ) (i j : ZMod v) :
    ∑ k : ZMod v, x (k - i) * y (j + k) = C x y (i + j) := by
  unfold C; rw [← Equiv.sum_comp (Equiv.addRight i)]
  apply Finset.sum_congr rfl; intro u _
  simp only [Equiv.coe_addRight]
  rw [show u + i - i = u by ring, show j + (u + i) = u + (i + j) by ring]

lemma sRAC (x y : ZMod v → ℤ) (i j : ZMod v) :
    ∑ k : ZMod v, x (i + k) * y (k - j) = C x y (-i - j) := by
  unfold C; rw [← Equiv.sum_comp (Equiv.subRight i)]
  apply Finset.sum_congr rfl; intro u _
  simp only [Equiv.subRight_apply]
  rw [show i + (u - i) = u by ring, show u - i - j = u + (-i - j) by ring]

lemma sARRA (x y : ZMod v → ℤ) (i j : ZMod v) :
    ∑ k : ZMod v, x (-i - k) * y (j + k) = K x y (j - i) := by
  unfold K; rw [← Equiv.sum_comp (Equiv.subLeft (-i))]
  apply Finset.sum_congr rfl; intro u _
  simp only [Equiv.subLeft_apply]
  rw [show -i - (-i - u) = u by ring, show j + (-i - u) = j - i - u by ring]

lemma sRAAR (x y : ZMod v → ℤ) (i j : ZMod v) :
    ∑ k : ZMod v, x (i + k) * y (-j - k) = K x y (i - j) := by
  unfold K; rw [← Equiv.sum_comp (Equiv.subRight i)]
  apply Finset.sum_congr rfl; intro u _
  simp only [Equiv.subRight_apply]
  rw [show i + (u - i) = u by ring, show -j - (u - i) = i - j - u by ring]

/-- The propus matrix built from `a` (symmetric block), `b` (repeated block) and `d`. -/
def propus (a b d : ZMod v → ℤ) : Matrix (Fin 4 × ZMod v) (Fin 4 × ZMod v) ℤ :=
  fun P Q =>
    match P.1, Q.1 with
    | 0, 0 => -a (Q.2 - P.2) | 0, 1 => b (-P.2 - Q.2) | 0, 2 => b (-P.2 - Q.2) | 0, 3 => d (-P.2 - Q.2)
    | 1, 0 => b (-P.2 - Q.2) | 1, 1 => d (P.2 + Q.2) | 1, 2 => a (Q.2 - P.2) | 1, 3 => -b (P.2 + Q.2)
    | 2, 0 => b (-P.2 - Q.2) | 2, 1 => a (Q.2 - P.2) | 2, 2 => -d (P.2 + Q.2) | 2, 3 => b (P.2 + Q.2)
    | 3, 0 => d (-P.2 - Q.2) | 3, 1 => -b (P.2 + Q.2) | 3, 2 => b (P.2 + Q.2) | 3, 3 => a (Q.2 - P.2)


lemma C_swap' (x y : ZMod v → ℤ) (s t : ZMod v) (h : s = -t) : C x y t = C y x s := by
  subst h; exact C_swap x y t

lemma C_self_zero (x : ZMod v → ℤ) (hx : ∀ u, x u = 1 ∨ x u = -1) : C x x 0 = v := by
  unfold C
  have : ∀ u : ZMod v, x u * x (u + 0) = 1 := by
    intro u; rw [add_zero]; rcases hx u with h | h <;> rw [h] <;> norm_num
  simp only [this, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]

lemma entry_expand (a b d : ZMod v → ℤ) (P Q : Fin 4 × ZMod v) :
    (propus a b d * (propus a b d).transpose) P Q =
      ∑ k, propus a b d P (0, k) * propus a b d Q (0, k) + ∑ k, propus a b d P (1, k) * propus a b d Q (1, k) +
      ∑ k, propus a b d P (2, k) * propus a b d Q (2, k) + ∑ k, propus a b d P (3, k) * propus a b d Q (3, k) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_four]
  rfl

section blocks
variable (a b d : ZMod v → ℤ) (i j : ZMod v)

lemma e01 : (propus a b d * (propus a b d).transpose) (0, i) (1, j) = 0 := by
  rw [entry_expand]
  simp only [propus, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib, sCC, sARAR, sRARA, sCAR, sARC, sCRA, sRAC, sARRA, sRAAR]
  linarith [K_comm a a (i - j), C_swap' a a (j - i) (i - j) (by ring), K_comm a a (j - i), C_swap' a a (i - j) (j - i) (by ring), K_comm a a (i + j), C_swap' a a (-i - j) (i + j) (by ring), K_comm a a (-i - j), C_swap' a a (i + j) (-i - j) (by ring), K_comm a b (i - j), C_swap' a b (j - i) (i - j) (by ring), K_comm a b (j - i), C_swap' a b (i - j) (j - i) (by ring), K_comm a b (i + j), C_swap' a b (-i - j) (i + j) (by ring), K_comm a b (-i - j), C_swap' a b (i + j) (-i - j) (by ring), K_comm a d (i - j), C_swap' a d (j - i) (i - j) (by ring), K_comm a d (j - i), C_swap' a d (i - j) (j - i) (by ring), K_comm a d (i + j), C_swap' a d (-i - j) (i + j) (by ring), K_comm a d (-i - j), C_swap' a d (i + j) (-i - j) (by ring), K_comm b a (i - j), C_swap' b a (j - i) (i - j) (by ring), K_comm b a (j - i), C_swap' b a (i - j) (j - i) (by ring), K_comm b a (i + j), C_swap' b a (-i - j) (i + j) (by ring), K_comm b a (-i - j), C_swap' b a (i + j) (-i - j) (by ring), K_comm b b (i - j), C_swap' b b (j - i) (i - j) (by ring), K_comm b b (j - i), C_swap' b b (i - j) (j - i) (by ring), K_comm b b (i + j), C_swap' b b (-i - j) (i + j) (by ring), K_comm b b (-i - j), C_swap' b b (i + j) (-i - j) (by ring), K_comm b d (i - j), C_swap' b d (j - i) (i - j) (by ring), K_comm b d (j - i), C_swap' b d (i - j) (j - i) (by ring), K_comm b d (i + j), C_swap' b d (-i - j) (i + j) (by ring), K_comm b d (-i - j), C_swap' b d (i + j) (-i - j) (by ring), K_comm d a (i - j), C_swap' d a (j - i) (i - j) (by ring), K_comm d a (j - i), C_swap' d a (i - j) (j - i) (by ring), K_comm d a (i + j), C_swap' d a (-i - j) (i + j) (by ring), K_comm d a (-i - j), C_swap' d a (i + j) (-i - j) (by ring), K_comm d b (i - j), C_swap' d b (j - i) (i - j) (by ring), K_comm d b (j - i), C_swap' d b (i - j) (j - i) (by ring), K_comm d b (i + j), C_swap' d b (-i - j) (i + j) (by ring), K_comm d b (-i - j), C_swap' d b (i + j) (-i - j) (by ring), K_comm d d (i - j), C_swap' d d (j - i) (i - j) (by ring), K_comm d d (j - i), C_swap' d d (i - j) (j - i) (by ring), K_comm d d (i + j), C_swap' d d (-i - j) (i + j) (by ring), K_comm d d (-i - j), C_swap' d d (i + j) (-i - j) (by ring)]

lemma e02 : (propus a b d * (propus a b d).transpose) (0, i) (2, j) = 0 := by
  rw [entry_expand]
  simp only [propus, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib, sCC, sARAR, sRARA, sCAR, sARC, sCRA, sRAC, sARRA, sRAAR]
  linarith [K_comm a a (i - j), C_swap' a a (j - i) (i - j) (by ring), K_comm a a (j - i), C_swap' a a (i - j) (j - i) (by ring), K_comm a a (i + j), C_swap' a a (-i - j) (i + j) (by ring), K_comm a a (-i - j), C_swap' a a (i + j) (-i - j) (by ring), K_comm a b (i - j), C_swap' a b (j - i) (i - j) (by ring), K_comm a b (j - i), C_swap' a b (i - j) (j - i) (by ring), K_comm a b (i + j), C_swap' a b (-i - j) (i + j) (by ring), K_comm a b (-i - j), C_swap' a b (i + j) (-i - j) (by ring), K_comm a d (i - j), C_swap' a d (j - i) (i - j) (by ring), K_comm a d (j - i), C_swap' a d (i - j) (j - i) (by ring), K_comm a d (i + j), C_swap' a d (-i - j) (i + j) (by ring), K_comm a d (-i - j), C_swap' a d (i + j) (-i - j) (by ring), K_comm b a (i - j), C_swap' b a (j - i) (i - j) (by ring), K_comm b a (j - i), C_swap' b a (i - j) (j - i) (by ring), K_comm b a (i + j), C_swap' b a (-i - j) (i + j) (by ring), K_comm b a (-i - j), C_swap' b a (i + j) (-i - j) (by ring), K_comm b b (i - j), C_swap' b b (j - i) (i - j) (by ring), K_comm b b (j - i), C_swap' b b (i - j) (j - i) (by ring), K_comm b b (i + j), C_swap' b b (-i - j) (i + j) (by ring), K_comm b b (-i - j), C_swap' b b (i + j) (-i - j) (by ring), K_comm b d (i - j), C_swap' b d (j - i) (i - j) (by ring), K_comm b d (j - i), C_swap' b d (i - j) (j - i) (by ring), K_comm b d (i + j), C_swap' b d (-i - j) (i + j) (by ring), K_comm b d (-i - j), C_swap' b d (i + j) (-i - j) (by ring), K_comm d a (i - j), C_swap' d a (j - i) (i - j) (by ring), K_comm d a (j - i), C_swap' d a (i - j) (j - i) (by ring), K_comm d a (i + j), C_swap' d a (-i - j) (i + j) (by ring), K_comm d a (-i - j), C_swap' d a (i + j) (-i - j) (by ring), K_comm d b (i - j), C_swap' d b (j - i) (i - j) (by ring), K_comm d b (j - i), C_swap' d b (i - j) (j - i) (by ring), K_comm d b (i + j), C_swap' d b (-i - j) (i + j) (by ring), K_comm d b (-i - j), C_swap' d b (i + j) (-i - j) (by ring), K_comm d d (i - j), C_swap' d d (j - i) (i - j) (by ring), K_comm d d (j - i), C_swap' d d (i - j) (j - i) (by ring), K_comm d d (i + j), C_swap' d d (-i - j) (i + j) (by ring), K_comm d d (-i - j), C_swap' d d (i + j) (-i - j) (by ring)]

lemma e03 : (propus a b d * (propus a b d).transpose) (0, i) (3, j) = 0 := by
  rw [entry_expand]
  simp only [propus, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib, sCC, sARAR, sRARA, sCAR, sARC, sCRA, sRAC, sARRA, sRAAR]
  linarith [K_comm a a (i - j), C_swap' a a (j - i) (i - j) (by ring), K_comm a a (j - i), C_swap' a a (i - j) (j - i) (by ring), K_comm a a (i + j), C_swap' a a (-i - j) (i + j) (by ring), K_comm a a (-i - j), C_swap' a a (i + j) (-i - j) (by ring), K_comm a b (i - j), C_swap' a b (j - i) (i - j) (by ring), K_comm a b (j - i), C_swap' a b (i - j) (j - i) (by ring), K_comm a b (i + j), C_swap' a b (-i - j) (i + j) (by ring), K_comm a b (-i - j), C_swap' a b (i + j) (-i - j) (by ring), K_comm a d (i - j), C_swap' a d (j - i) (i - j) (by ring), K_comm a d (j - i), C_swap' a d (i - j) (j - i) (by ring), K_comm a d (i + j), C_swap' a d (-i - j) (i + j) (by ring), K_comm a d (-i - j), C_swap' a d (i + j) (-i - j) (by ring), K_comm b a (i - j), C_swap' b a (j - i) (i - j) (by ring), K_comm b a (j - i), C_swap' b a (i - j) (j - i) (by ring), K_comm b a (i + j), C_swap' b a (-i - j) (i + j) (by ring), K_comm b a (-i - j), C_swap' b a (i + j) (-i - j) (by ring), K_comm b b (i - j), C_swap' b b (j - i) (i - j) (by ring), K_comm b b (j - i), C_swap' b b (i - j) (j - i) (by ring), K_comm b b (i + j), C_swap' b b (-i - j) (i + j) (by ring), K_comm b b (-i - j), C_swap' b b (i + j) (-i - j) (by ring), K_comm b d (i - j), C_swap' b d (j - i) (i - j) (by ring), K_comm b d (j - i), C_swap' b d (i - j) (j - i) (by ring), K_comm b d (i + j), C_swap' b d (-i - j) (i + j) (by ring), K_comm b d (-i - j), C_swap' b d (i + j) (-i - j) (by ring), K_comm d a (i - j), C_swap' d a (j - i) (i - j) (by ring), K_comm d a (j - i), C_swap' d a (i - j) (j - i) (by ring), K_comm d a (i + j), C_swap' d a (-i - j) (i + j) (by ring), K_comm d a (-i - j), C_swap' d a (i + j) (-i - j) (by ring), K_comm d b (i - j), C_swap' d b (j - i) (i - j) (by ring), K_comm d b (j - i), C_swap' d b (i - j) (j - i) (by ring), K_comm d b (i + j), C_swap' d b (-i - j) (i + j) (by ring), K_comm d b (-i - j), C_swap' d b (i + j) (-i - j) (by ring), K_comm d d (i - j), C_swap' d d (j - i) (i - j) (by ring), K_comm d d (j - i), C_swap' d d (i - j) (j - i) (by ring), K_comm d d (i + j), C_swap' d d (-i - j) (i + j) (by ring), K_comm d d (-i - j), C_swap' d d (i + j) (-i - j) (by ring)]

lemma e10 : (propus a b d * (propus a b d).transpose) (1, i) (0, j) = 0 := by
  rw [entry_expand]
  simp only [propus, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib, sCC, sARAR, sRARA, sCAR, sARC, sCRA, sRAC, sARRA, sRAAR]
  linarith [K_comm a a (i - j), C_swap' a a (j - i) (i - j) (by ring), K_comm a a (j - i), C_swap' a a (i - j) (j - i) (by ring), K_comm a a (i + j), C_swap' a a (-i - j) (i + j) (by ring), K_comm a a (-i - j), C_swap' a a (i + j) (-i - j) (by ring), K_comm a b (i - j), C_swap' a b (j - i) (i - j) (by ring), K_comm a b (j - i), C_swap' a b (i - j) (j - i) (by ring), K_comm a b (i + j), C_swap' a b (-i - j) (i + j) (by ring), K_comm a b (-i - j), C_swap' a b (i + j) (-i - j) (by ring), K_comm a d (i - j), C_swap' a d (j - i) (i - j) (by ring), K_comm a d (j - i), C_swap' a d (i - j) (j - i) (by ring), K_comm a d (i + j), C_swap' a d (-i - j) (i + j) (by ring), K_comm a d (-i - j), C_swap' a d (i + j) (-i - j) (by ring), K_comm b a (i - j), C_swap' b a (j - i) (i - j) (by ring), K_comm b a (j - i), C_swap' b a (i - j) (j - i) (by ring), K_comm b a (i + j), C_swap' b a (-i - j) (i + j) (by ring), K_comm b a (-i - j), C_swap' b a (i + j) (-i - j) (by ring), K_comm b b (i - j), C_swap' b b (j - i) (i - j) (by ring), K_comm b b (j - i), C_swap' b b (i - j) (j - i) (by ring), K_comm b b (i + j), C_swap' b b (-i - j) (i + j) (by ring), K_comm b b (-i - j), C_swap' b b (i + j) (-i - j) (by ring), K_comm b d (i - j), C_swap' b d (j - i) (i - j) (by ring), K_comm b d (j - i), C_swap' b d (i - j) (j - i) (by ring), K_comm b d (i + j), C_swap' b d (-i - j) (i + j) (by ring), K_comm b d (-i - j), C_swap' b d (i + j) (-i - j) (by ring), K_comm d a (i - j), C_swap' d a (j - i) (i - j) (by ring), K_comm d a (j - i), C_swap' d a (i - j) (j - i) (by ring), K_comm d a (i + j), C_swap' d a (-i - j) (i + j) (by ring), K_comm d a (-i - j), C_swap' d a (i + j) (-i - j) (by ring), K_comm d b (i - j), C_swap' d b (j - i) (i - j) (by ring), K_comm d b (j - i), C_swap' d b (i - j) (j - i) (by ring), K_comm d b (i + j), C_swap' d b (-i - j) (i + j) (by ring), K_comm d b (-i - j), C_swap' d b (i + j) (-i - j) (by ring), K_comm d d (i - j), C_swap' d d (j - i) (i - j) (by ring), K_comm d d (j - i), C_swap' d d (i - j) (j - i) (by ring), K_comm d d (i + j), C_swap' d d (-i - j) (i + j) (by ring), K_comm d d (-i - j), C_swap' d d (i + j) (-i - j) (by ring)]

lemma e12 : (propus a b d * (propus a b d).transpose) (1, i) (2, j) = 0 := by
  rw [entry_expand]
  simp only [propus, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib, sCC, sARAR, sRARA, sCAR, sARC, sCRA, sRAC, sARRA, sRAAR]
  linarith [K_comm a a (i - j), C_swap' a a (j - i) (i - j) (by ring), K_comm a a (j - i), C_swap' a a (i - j) (j - i) (by ring), K_comm a a (i + j), C_swap' a a (-i - j) (i + j) (by ring), K_comm a a (-i - j), C_swap' a a (i + j) (-i - j) (by ring), K_comm a b (i - j), C_swap' a b (j - i) (i - j) (by ring), K_comm a b (j - i), C_swap' a b (i - j) (j - i) (by ring), K_comm a b (i + j), C_swap' a b (-i - j) (i + j) (by ring), K_comm a b (-i - j), C_swap' a b (i + j) (-i - j) (by ring), K_comm a d (i - j), C_swap' a d (j - i) (i - j) (by ring), K_comm a d (j - i), C_swap' a d (i - j) (j - i) (by ring), K_comm a d (i + j), C_swap' a d (-i - j) (i + j) (by ring), K_comm a d (-i - j), C_swap' a d (i + j) (-i - j) (by ring), K_comm b a (i - j), C_swap' b a (j - i) (i - j) (by ring), K_comm b a (j - i), C_swap' b a (i - j) (j - i) (by ring), K_comm b a (i + j), C_swap' b a (-i - j) (i + j) (by ring), K_comm b a (-i - j), C_swap' b a (i + j) (-i - j) (by ring), K_comm b b (i - j), C_swap' b b (j - i) (i - j) (by ring), K_comm b b (j - i), C_swap' b b (i - j) (j - i) (by ring), K_comm b b (i + j), C_swap' b b (-i - j) (i + j) (by ring), K_comm b b (-i - j), C_swap' b b (i + j) (-i - j) (by ring), K_comm b d (i - j), C_swap' b d (j - i) (i - j) (by ring), K_comm b d (j - i), C_swap' b d (i - j) (j - i) (by ring), K_comm b d (i + j), C_swap' b d (-i - j) (i + j) (by ring), K_comm b d (-i - j), C_swap' b d (i + j) (-i - j) (by ring), K_comm d a (i - j), C_swap' d a (j - i) (i - j) (by ring), K_comm d a (j - i), C_swap' d a (i - j) (j - i) (by ring), K_comm d a (i + j), C_swap' d a (-i - j) (i + j) (by ring), K_comm d a (-i - j), C_swap' d a (i + j) (-i - j) (by ring), K_comm d b (i - j), C_swap' d b (j - i) (i - j) (by ring), K_comm d b (j - i), C_swap' d b (i - j) (j - i) (by ring), K_comm d b (i + j), C_swap' d b (-i - j) (i + j) (by ring), K_comm d b (-i - j), C_swap' d b (i + j) (-i - j) (by ring), K_comm d d (i - j), C_swap' d d (j - i) (i - j) (by ring), K_comm d d (j - i), C_swap' d d (i - j) (j - i) (by ring), K_comm d d (i + j), C_swap' d d (-i - j) (i + j) (by ring), K_comm d d (-i - j), C_swap' d d (i + j) (-i - j) (by ring)]

lemma e13 : (propus a b d * (propus a b d).transpose) (1, i) (3, j) = 0 := by
  rw [entry_expand]
  simp only [propus, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib, sCC, sARAR, sRARA, sCAR, sARC, sCRA, sRAC, sARRA, sRAAR]
  linarith [K_comm a a (i - j), C_swap' a a (j - i) (i - j) (by ring), K_comm a a (j - i), C_swap' a a (i - j) (j - i) (by ring), K_comm a a (i + j), C_swap' a a (-i - j) (i + j) (by ring), K_comm a a (-i - j), C_swap' a a (i + j) (-i - j) (by ring), K_comm a b (i - j), C_swap' a b (j - i) (i - j) (by ring), K_comm a b (j - i), C_swap' a b (i - j) (j - i) (by ring), K_comm a b (i + j), C_swap' a b (-i - j) (i + j) (by ring), K_comm a b (-i - j), C_swap' a b (i + j) (-i - j) (by ring), K_comm a d (i - j), C_swap' a d (j - i) (i - j) (by ring), K_comm a d (j - i), C_swap' a d (i - j) (j - i) (by ring), K_comm a d (i + j), C_swap' a d (-i - j) (i + j) (by ring), K_comm a d (-i - j), C_swap' a d (i + j) (-i - j) (by ring), K_comm b a (i - j), C_swap' b a (j - i) (i - j) (by ring), K_comm b a (j - i), C_swap' b a (i - j) (j - i) (by ring), K_comm b a (i + j), C_swap' b a (-i - j) (i + j) (by ring), K_comm b a (-i - j), C_swap' b a (i + j) (-i - j) (by ring), K_comm b b (i - j), C_swap' b b (j - i) (i - j) (by ring), K_comm b b (j - i), C_swap' b b (i - j) (j - i) (by ring), K_comm b b (i + j), C_swap' b b (-i - j) (i + j) (by ring), K_comm b b (-i - j), C_swap' b b (i + j) (-i - j) (by ring), K_comm b d (i - j), C_swap' b d (j - i) (i - j) (by ring), K_comm b d (j - i), C_swap' b d (i - j) (j - i) (by ring), K_comm b d (i + j), C_swap' b d (-i - j) (i + j) (by ring), K_comm b d (-i - j), C_swap' b d (i + j) (-i - j) (by ring), K_comm d a (i - j), C_swap' d a (j - i) (i - j) (by ring), K_comm d a (j - i), C_swap' d a (i - j) (j - i) (by ring), K_comm d a (i + j), C_swap' d a (-i - j) (i + j) (by ring), K_comm d a (-i - j), C_swap' d a (i + j) (-i - j) (by ring), K_comm d b (i - j), C_swap' d b (j - i) (i - j) (by ring), K_comm d b (j - i), C_swap' d b (i - j) (j - i) (by ring), K_comm d b (i + j), C_swap' d b (-i - j) (i + j) (by ring), K_comm d b (-i - j), C_swap' d b (i + j) (-i - j) (by ring), K_comm d d (i - j), C_swap' d d (j - i) (i - j) (by ring), K_comm d d (j - i), C_swap' d d (i - j) (j - i) (by ring), K_comm d d (i + j), C_swap' d d (-i - j) (i + j) (by ring), K_comm d d (-i - j), C_swap' d d (i + j) (-i - j) (by ring)]

lemma e20 : (propus a b d * (propus a b d).transpose) (2, i) (0, j) = 0 := by
  rw [entry_expand]
  simp only [propus, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib, sCC, sARAR, sRARA, sCAR, sARC, sCRA, sRAC, sARRA, sRAAR]
  linarith [K_comm a a (i - j), C_swap' a a (j - i) (i - j) (by ring), K_comm a a (j - i), C_swap' a a (i - j) (j - i) (by ring), K_comm a a (i + j), C_swap' a a (-i - j) (i + j) (by ring), K_comm a a (-i - j), C_swap' a a (i + j) (-i - j) (by ring), K_comm a b (i - j), C_swap' a b (j - i) (i - j) (by ring), K_comm a b (j - i), C_swap' a b (i - j) (j - i) (by ring), K_comm a b (i + j), C_swap' a b (-i - j) (i + j) (by ring), K_comm a b (-i - j), C_swap' a b (i + j) (-i - j) (by ring), K_comm a d (i - j), C_swap' a d (j - i) (i - j) (by ring), K_comm a d (j - i), C_swap' a d (i - j) (j - i) (by ring), K_comm a d (i + j), C_swap' a d (-i - j) (i + j) (by ring), K_comm a d (-i - j), C_swap' a d (i + j) (-i - j) (by ring), K_comm b a (i - j), C_swap' b a (j - i) (i - j) (by ring), K_comm b a (j - i), C_swap' b a (i - j) (j - i) (by ring), K_comm b a (i + j), C_swap' b a (-i - j) (i + j) (by ring), K_comm b a (-i - j), C_swap' b a (i + j) (-i - j) (by ring), K_comm b b (i - j), C_swap' b b (j - i) (i - j) (by ring), K_comm b b (j - i), C_swap' b b (i - j) (j - i) (by ring), K_comm b b (i + j), C_swap' b b (-i - j) (i + j) (by ring), K_comm b b (-i - j), C_swap' b b (i + j) (-i - j) (by ring), K_comm b d (i - j), C_swap' b d (j - i) (i - j) (by ring), K_comm b d (j - i), C_swap' b d (i - j) (j - i) (by ring), K_comm b d (i + j), C_swap' b d (-i - j) (i + j) (by ring), K_comm b d (-i - j), C_swap' b d (i + j) (-i - j) (by ring), K_comm d a (i - j), C_swap' d a (j - i) (i - j) (by ring), K_comm d a (j - i), C_swap' d a (i - j) (j - i) (by ring), K_comm d a (i + j), C_swap' d a (-i - j) (i + j) (by ring), K_comm d a (-i - j), C_swap' d a (i + j) (-i - j) (by ring), K_comm d b (i - j), C_swap' d b (j - i) (i - j) (by ring), K_comm d b (j - i), C_swap' d b (i - j) (j - i) (by ring), K_comm d b (i + j), C_swap' d b (-i - j) (i + j) (by ring), K_comm d b (-i - j), C_swap' d b (i + j) (-i - j) (by ring), K_comm d d (i - j), C_swap' d d (j - i) (i - j) (by ring), K_comm d d (j - i), C_swap' d d (i - j) (j - i) (by ring), K_comm d d (i + j), C_swap' d d (-i - j) (i + j) (by ring), K_comm d d (-i - j), C_swap' d d (i + j) (-i - j) (by ring)]

lemma e21 : (propus a b d * (propus a b d).transpose) (2, i) (1, j) = 0 := by
  rw [entry_expand]
  simp only [propus, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib, sCC, sARAR, sRARA, sCAR, sARC, sCRA, sRAC, sARRA, sRAAR]
  linarith [K_comm a a (i - j), C_swap' a a (j - i) (i - j) (by ring), K_comm a a (j - i), C_swap' a a (i - j) (j - i) (by ring), K_comm a a (i + j), C_swap' a a (-i - j) (i + j) (by ring), K_comm a a (-i - j), C_swap' a a (i + j) (-i - j) (by ring), K_comm a b (i - j), C_swap' a b (j - i) (i - j) (by ring), K_comm a b (j - i), C_swap' a b (i - j) (j - i) (by ring), K_comm a b (i + j), C_swap' a b (-i - j) (i + j) (by ring), K_comm a b (-i - j), C_swap' a b (i + j) (-i - j) (by ring), K_comm a d (i - j), C_swap' a d (j - i) (i - j) (by ring), K_comm a d (j - i), C_swap' a d (i - j) (j - i) (by ring), K_comm a d (i + j), C_swap' a d (-i - j) (i + j) (by ring), K_comm a d (-i - j), C_swap' a d (i + j) (-i - j) (by ring), K_comm b a (i - j), C_swap' b a (j - i) (i - j) (by ring), K_comm b a (j - i), C_swap' b a (i - j) (j - i) (by ring), K_comm b a (i + j), C_swap' b a (-i - j) (i + j) (by ring), K_comm b a (-i - j), C_swap' b a (i + j) (-i - j) (by ring), K_comm b b (i - j), C_swap' b b (j - i) (i - j) (by ring), K_comm b b (j - i), C_swap' b b (i - j) (j - i) (by ring), K_comm b b (i + j), C_swap' b b (-i - j) (i + j) (by ring), K_comm b b (-i - j), C_swap' b b (i + j) (-i - j) (by ring), K_comm b d (i - j), C_swap' b d (j - i) (i - j) (by ring), K_comm b d (j - i), C_swap' b d (i - j) (j - i) (by ring), K_comm b d (i + j), C_swap' b d (-i - j) (i + j) (by ring), K_comm b d (-i - j), C_swap' b d (i + j) (-i - j) (by ring), K_comm d a (i - j), C_swap' d a (j - i) (i - j) (by ring), K_comm d a (j - i), C_swap' d a (i - j) (j - i) (by ring), K_comm d a (i + j), C_swap' d a (-i - j) (i + j) (by ring), K_comm d a (-i - j), C_swap' d a (i + j) (-i - j) (by ring), K_comm d b (i - j), C_swap' d b (j - i) (i - j) (by ring), K_comm d b (j - i), C_swap' d b (i - j) (j - i) (by ring), K_comm d b (i + j), C_swap' d b (-i - j) (i + j) (by ring), K_comm d b (-i - j), C_swap' d b (i + j) (-i - j) (by ring), K_comm d d (i - j), C_swap' d d (j - i) (i - j) (by ring), K_comm d d (j - i), C_swap' d d (i - j) (j - i) (by ring), K_comm d d (i + j), C_swap' d d (-i - j) (i + j) (by ring), K_comm d d (-i - j), C_swap' d d (i + j) (-i - j) (by ring)]

lemma e23 : (propus a b d * (propus a b d).transpose) (2, i) (3, j) = 0 := by
  rw [entry_expand]
  simp only [propus, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib, sCC, sARAR, sRARA, sCAR, sARC, sCRA, sRAC, sARRA, sRAAR]
  linarith [K_comm a a (i - j), C_swap' a a (j - i) (i - j) (by ring), K_comm a a (j - i), C_swap' a a (i - j) (j - i) (by ring), K_comm a a (i + j), C_swap' a a (-i - j) (i + j) (by ring), K_comm a a (-i - j), C_swap' a a (i + j) (-i - j) (by ring), K_comm a b (i - j), C_swap' a b (j - i) (i - j) (by ring), K_comm a b (j - i), C_swap' a b (i - j) (j - i) (by ring), K_comm a b (i + j), C_swap' a b (-i - j) (i + j) (by ring), K_comm a b (-i - j), C_swap' a b (i + j) (-i - j) (by ring), K_comm a d (i - j), C_swap' a d (j - i) (i - j) (by ring), K_comm a d (j - i), C_swap' a d (i - j) (j - i) (by ring), K_comm a d (i + j), C_swap' a d (-i - j) (i + j) (by ring), K_comm a d (-i - j), C_swap' a d (i + j) (-i - j) (by ring), K_comm b a (i - j), C_swap' b a (j - i) (i - j) (by ring), K_comm b a (j - i), C_swap' b a (i - j) (j - i) (by ring), K_comm b a (i + j), C_swap' b a (-i - j) (i + j) (by ring), K_comm b a (-i - j), C_swap' b a (i + j) (-i - j) (by ring), K_comm b b (i - j), C_swap' b b (j - i) (i - j) (by ring), K_comm b b (j - i), C_swap' b b (i - j) (j - i) (by ring), K_comm b b (i + j), C_swap' b b (-i - j) (i + j) (by ring), K_comm b b (-i - j), C_swap' b b (i + j) (-i - j) (by ring), K_comm b d (i - j), C_swap' b d (j - i) (i - j) (by ring), K_comm b d (j - i), C_swap' b d (i - j) (j - i) (by ring), K_comm b d (i + j), C_swap' b d (-i - j) (i + j) (by ring), K_comm b d (-i - j), C_swap' b d (i + j) (-i - j) (by ring), K_comm d a (i - j), C_swap' d a (j - i) (i - j) (by ring), K_comm d a (j - i), C_swap' d a (i - j) (j - i) (by ring), K_comm d a (i + j), C_swap' d a (-i - j) (i + j) (by ring), K_comm d a (-i - j), C_swap' d a (i + j) (-i - j) (by ring), K_comm d b (i - j), C_swap' d b (j - i) (i - j) (by ring), K_comm d b (j - i), C_swap' d b (i - j) (j - i) (by ring), K_comm d b (i + j), C_swap' d b (-i - j) (i + j) (by ring), K_comm d b (-i - j), C_swap' d b (i + j) (-i - j) (by ring), K_comm d d (i - j), C_swap' d d (j - i) (i - j) (by ring), K_comm d d (j - i), C_swap' d d (i - j) (j - i) (by ring), K_comm d d (i + j), C_swap' d d (-i - j) (i + j) (by ring), K_comm d d (-i - j), C_swap' d d (i + j) (-i - j) (by ring)]

lemma e30 : (propus a b d * (propus a b d).transpose) (3, i) (0, j) = 0 := by
  rw [entry_expand]
  simp only [propus, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib, sCC, sARAR, sRARA, sCAR, sARC, sCRA, sRAC, sARRA, sRAAR]
  linarith [K_comm a a (i - j), C_swap' a a (j - i) (i - j) (by ring), K_comm a a (j - i), C_swap' a a (i - j) (j - i) (by ring), K_comm a a (i + j), C_swap' a a (-i - j) (i + j) (by ring), K_comm a a (-i - j), C_swap' a a (i + j) (-i - j) (by ring), K_comm a b (i - j), C_swap' a b (j - i) (i - j) (by ring), K_comm a b (j - i), C_swap' a b (i - j) (j - i) (by ring), K_comm a b (i + j), C_swap' a b (-i - j) (i + j) (by ring), K_comm a b (-i - j), C_swap' a b (i + j) (-i - j) (by ring), K_comm a d (i - j), C_swap' a d (j - i) (i - j) (by ring), K_comm a d (j - i), C_swap' a d (i - j) (j - i) (by ring), K_comm a d (i + j), C_swap' a d (-i - j) (i + j) (by ring), K_comm a d (-i - j), C_swap' a d (i + j) (-i - j) (by ring), K_comm b a (i - j), C_swap' b a (j - i) (i - j) (by ring), K_comm b a (j - i), C_swap' b a (i - j) (j - i) (by ring), K_comm b a (i + j), C_swap' b a (-i - j) (i + j) (by ring), K_comm b a (-i - j), C_swap' b a (i + j) (-i - j) (by ring), K_comm b b (i - j), C_swap' b b (j - i) (i - j) (by ring), K_comm b b (j - i), C_swap' b b (i - j) (j - i) (by ring), K_comm b b (i + j), C_swap' b b (-i - j) (i + j) (by ring), K_comm b b (-i - j), C_swap' b b (i + j) (-i - j) (by ring), K_comm b d (i - j), C_swap' b d (j - i) (i - j) (by ring), K_comm b d (j - i), C_swap' b d (i - j) (j - i) (by ring), K_comm b d (i + j), C_swap' b d (-i - j) (i + j) (by ring), K_comm b d (-i - j), C_swap' b d (i + j) (-i - j) (by ring), K_comm d a (i - j), C_swap' d a (j - i) (i - j) (by ring), K_comm d a (j - i), C_swap' d a (i - j) (j - i) (by ring), K_comm d a (i + j), C_swap' d a (-i - j) (i + j) (by ring), K_comm d a (-i - j), C_swap' d a (i + j) (-i - j) (by ring), K_comm d b (i - j), C_swap' d b (j - i) (i - j) (by ring), K_comm d b (j - i), C_swap' d b (i - j) (j - i) (by ring), K_comm d b (i + j), C_swap' d b (-i - j) (i + j) (by ring), K_comm d b (-i - j), C_swap' d b (i + j) (-i - j) (by ring), K_comm d d (i - j), C_swap' d d (j - i) (i - j) (by ring), K_comm d d (j - i), C_swap' d d (i - j) (j - i) (by ring), K_comm d d (i + j), C_swap' d d (-i - j) (i + j) (by ring), K_comm d d (-i - j), C_swap' d d (i + j) (-i - j) (by ring)]

lemma e31 : (propus a b d * (propus a b d).transpose) (3, i) (1, j) = 0 := by
  rw [entry_expand]
  simp only [propus, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib, sCC, sARAR, sRARA, sCAR, sARC, sCRA, sRAC, sARRA, sRAAR]
  linarith [K_comm a a (i - j), C_swap' a a (j - i) (i - j) (by ring), K_comm a a (j - i), C_swap' a a (i - j) (j - i) (by ring), K_comm a a (i + j), C_swap' a a (-i - j) (i + j) (by ring), K_comm a a (-i - j), C_swap' a a (i + j) (-i - j) (by ring), K_comm a b (i - j), C_swap' a b (j - i) (i - j) (by ring), K_comm a b (j - i), C_swap' a b (i - j) (j - i) (by ring), K_comm a b (i + j), C_swap' a b (-i - j) (i + j) (by ring), K_comm a b (-i - j), C_swap' a b (i + j) (-i - j) (by ring), K_comm a d (i - j), C_swap' a d (j - i) (i - j) (by ring), K_comm a d (j - i), C_swap' a d (i - j) (j - i) (by ring), K_comm a d (i + j), C_swap' a d (-i - j) (i + j) (by ring), K_comm a d (-i - j), C_swap' a d (i + j) (-i - j) (by ring), K_comm b a (i - j), C_swap' b a (j - i) (i - j) (by ring), K_comm b a (j - i), C_swap' b a (i - j) (j - i) (by ring), K_comm b a (i + j), C_swap' b a (-i - j) (i + j) (by ring), K_comm b a (-i - j), C_swap' b a (i + j) (-i - j) (by ring), K_comm b b (i - j), C_swap' b b (j - i) (i - j) (by ring), K_comm b b (j - i), C_swap' b b (i - j) (j - i) (by ring), K_comm b b (i + j), C_swap' b b (-i - j) (i + j) (by ring), K_comm b b (-i - j), C_swap' b b (i + j) (-i - j) (by ring), K_comm b d (i - j), C_swap' b d (j - i) (i - j) (by ring), K_comm b d (j - i), C_swap' b d (i - j) (j - i) (by ring), K_comm b d (i + j), C_swap' b d (-i - j) (i + j) (by ring), K_comm b d (-i - j), C_swap' b d (i + j) (-i - j) (by ring), K_comm d a (i - j), C_swap' d a (j - i) (i - j) (by ring), K_comm d a (j - i), C_swap' d a (i - j) (j - i) (by ring), K_comm d a (i + j), C_swap' d a (-i - j) (i + j) (by ring), K_comm d a (-i - j), C_swap' d a (i + j) (-i - j) (by ring), K_comm d b (i - j), C_swap' d b (j - i) (i - j) (by ring), K_comm d b (j - i), C_swap' d b (i - j) (j - i) (by ring), K_comm d b (i + j), C_swap' d b (-i - j) (i + j) (by ring), K_comm d b (-i - j), C_swap' d b (i + j) (-i - j) (by ring), K_comm d d (i - j), C_swap' d d (j - i) (i - j) (by ring), K_comm d d (j - i), C_swap' d d (i - j) (j - i) (by ring), K_comm d d (i + j), C_swap' d d (-i - j) (i + j) (by ring), K_comm d d (-i - j), C_swap' d d (i + j) (-i - j) (by ring)]

lemma e32 : (propus a b d * (propus a b d).transpose) (3, i) (2, j) = 0 := by
  rw [entry_expand]
  simp only [propus, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib, sCC, sARAR, sRARA, sCAR, sARC, sCRA, sRAC, sARRA, sRAAR]
  linarith [K_comm a a (i - j), C_swap' a a (j - i) (i - j) (by ring), K_comm a a (j - i), C_swap' a a (i - j) (j - i) (by ring), K_comm a a (i + j), C_swap' a a (-i - j) (i + j) (by ring), K_comm a a (-i - j), C_swap' a a (i + j) (-i - j) (by ring), K_comm a b (i - j), C_swap' a b (j - i) (i - j) (by ring), K_comm a b (j - i), C_swap' a b (i - j) (j - i) (by ring), K_comm a b (i + j), C_swap' a b (-i - j) (i + j) (by ring), K_comm a b (-i - j), C_swap' a b (i + j) (-i - j) (by ring), K_comm a d (i - j), C_swap' a d (j - i) (i - j) (by ring), K_comm a d (j - i), C_swap' a d (i - j) (j - i) (by ring), K_comm a d (i + j), C_swap' a d (-i - j) (i + j) (by ring), K_comm a d (-i - j), C_swap' a d (i + j) (-i - j) (by ring), K_comm b a (i - j), C_swap' b a (j - i) (i - j) (by ring), K_comm b a (j - i), C_swap' b a (i - j) (j - i) (by ring), K_comm b a (i + j), C_swap' b a (-i - j) (i + j) (by ring), K_comm b a (-i - j), C_swap' b a (i + j) (-i - j) (by ring), K_comm b b (i - j), C_swap' b b (j - i) (i - j) (by ring), K_comm b b (j - i), C_swap' b b (i - j) (j - i) (by ring), K_comm b b (i + j), C_swap' b b (-i - j) (i + j) (by ring), K_comm b b (-i - j), C_swap' b b (i + j) (-i - j) (by ring), K_comm b d (i - j), C_swap' b d (j - i) (i - j) (by ring), K_comm b d (j - i), C_swap' b d (i - j) (j - i) (by ring), K_comm b d (i + j), C_swap' b d (-i - j) (i + j) (by ring), K_comm b d (-i - j), C_swap' b d (i + j) (-i - j) (by ring), K_comm d a (i - j), C_swap' d a (j - i) (i - j) (by ring), K_comm d a (j - i), C_swap' d a (i - j) (j - i) (by ring), K_comm d a (i + j), C_swap' d a (-i - j) (i + j) (by ring), K_comm d a (-i - j), C_swap' d a (i + j) (-i - j) (by ring), K_comm d b (i - j), C_swap' d b (j - i) (i - j) (by ring), K_comm d b (j - i), C_swap' d b (i - j) (j - i) (by ring), K_comm d b (i + j), C_swap' d b (-i - j) (i + j) (by ring), K_comm d b (-i - j), C_swap' d b (i + j) (-i - j) (by ring), K_comm d d (i - j), C_swap' d d (j - i) (i - j) (by ring), K_comm d d (j - i), C_swap' d d (i - j) (j - i) (by ring), K_comm d d (i + j), C_swap' d d (-i - j) (i + j) (by ring), K_comm d d (-i - j), C_swap' d d (i + j) (-i - j) (by ring)]

variable (hdiag : ∀ t : ZMod v, C a a t + 2 * C b b t + C d d t = if t = 0 then 4 * (v : ℤ) else 0)
include hdiag

lemma e00 : (propus a b d * (propus a b d).transpose) (0, i) (0, j) = if i = j then 4 * (v : ℤ) else 0 := by
  rw [entry_expand]
  simp only [propus, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib, sCC, sARAR, sRARA, sCAR, sARC, sCRA, sRAC, sARRA, sRAAR]
  by_cases hij : i = j
  · subst hij
    have h := hdiag 0
    simp only [sub_self, add_neg_cancel, if_true, neg_add_cancel] at h ⊢
    linarith [h, C_swap' a a 0 0 (by simp), C_swap' b b 0 0 (by simp), C_swap' d d 0 0 (by simp)]
  · have hne : i - j ≠ 0 := sub_ne_zero.mpr hij
    have h := hdiag (i - j)
    rw [if_neg hne] at h
    rw [if_neg hij]
    linarith [h, C_swap' a a (i - j) (j - i) (by ring), C_swap' b b (i - j) (j - i) (by ring), C_swap' d d (i - j) (j - i) (by ring)]

lemma e11 : (propus a b d * (propus a b d).transpose) (1, i) (1, j) = if i = j then 4 * (v : ℤ) else 0 := by
  rw [entry_expand]
  simp only [propus, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib, sCC, sARAR, sRARA, sCAR, sARC, sCRA, sRAC, sARRA, sRAAR]
  by_cases hij : i = j
  · subst hij
    have h := hdiag 0
    simp only [sub_self, add_neg_cancel, if_true, neg_add_cancel] at h ⊢
    linarith [h, C_swap' a a 0 0 (by simp), C_swap' b b 0 0 (by simp), C_swap' d d 0 0 (by simp)]
  · have hne : i - j ≠ 0 := sub_ne_zero.mpr hij
    have h := hdiag (i - j)
    rw [if_neg hne] at h
    rw [if_neg hij]
    linarith [h, C_swap' a a (i - j) (j - i) (by ring), C_swap' b b (i - j) (j - i) (by ring), C_swap' d d (i - j) (j - i) (by ring)]

lemma e22 : (propus a b d * (propus a b d).transpose) (2, i) (2, j) = if i = j then 4 * (v : ℤ) else 0 := by
  rw [entry_expand]
  simp only [propus, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib, sCC, sARAR, sRARA, sCAR, sARC, sCRA, sRAC, sARRA, sRAAR]
  by_cases hij : i = j
  · subst hij
    have h := hdiag 0
    simp only [sub_self, add_neg_cancel, if_true, neg_add_cancel] at h ⊢
    linarith [h, C_swap' a a 0 0 (by simp), C_swap' b b 0 0 (by simp), C_swap' d d 0 0 (by simp)]
  · have hne : i - j ≠ 0 := sub_ne_zero.mpr hij
    have h := hdiag (i - j)
    rw [if_neg hne] at h
    rw [if_neg hij]
    linarith [h, C_swap' a a (i - j) (j - i) (by ring), C_swap' b b (i - j) (j - i) (by ring), C_swap' d d (i - j) (j - i) (by ring)]

lemma e33 : (propus a b d * (propus a b d).transpose) (3, i) (3, j) = if i = j then 4 * (v : ℤ) else 0 := by
  rw [entry_expand]
  simp only [propus, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib, sCC, sARAR, sRARA, sCAR, sARC, sCRA, sRAC, sARRA, sRAAR]
  by_cases hij : i = j
  · subst hij
    have h := hdiag 0
    simp only [sub_self, add_neg_cancel, if_true, neg_add_cancel] at h ⊢
    linarith [h, C_swap' a a 0 0 (by simp), C_swap' b b 0 0 (by simp), C_swap' d d 0 0 (by simp)]
  · have hne : i - j ≠ 0 := sub_ne_zero.mpr hij
    have h := hdiag (i - j)
    rw [if_neg hne] at h
    rw [if_neg hij]
    linarith [h, C_swap' a a (i - j) (j - i) (by ring), C_swap' b b (i - j) (j - i) (by ring), C_swap' d d (i - j) (j - i) (by ring)]

end blocks

theorem propus_mul_transpose (a b d : ZMod v → ℤ)
    (ha1 : ∀ u, a u = 1 ∨ a u = -1) (hb1 : ∀ u, b u = 1 ∨ b u = -1) (hd1 : ∀ u, d u = 1 ∨ d u = -1)
    (hpaf : ∀ t : ZMod v, t ≠ 0 → C a a t + 2 * C b b t + C d d t = 0) :
    propus a b d * (propus a b d).transpose = (4 * (v : ℤ)) • (1 : Matrix (Fin 4 × ZMod v) (Fin 4 × ZMod v) ℤ) := by
  have hdiag : ∀ t : ZMod v, C a a t + 2 * C b b t + C d d t = if t = 0 then 4 * (v : ℤ) else 0 := by
    intro t
    split_ifs with h
    · subst h; rw [C_self_zero a ha1, C_self_zero b hb1, C_self_zero d hd1]; ring
    · exact hpaf t h
  ext ⟨p, i⟩ ⟨q, j⟩
  rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  fin_cases p <;> fin_cases q <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
  all_goals first
    | (rw [e00 a b d i j hdiag]; by_cases h : i = j <;> simp [h])
    | (rw [e11 a b d i j hdiag]; by_cases h : i = j <;> simp [h])
    | (rw [e22 a b d i j hdiag]; by_cases h : i = j <;> simp [h])
    | (rw [e33 a b d i j hdiag]; by_cases h : i = j <;> simp [h])
    | (rw [e01]; simp) | (rw [e02]; simp) | (rw [e03]; simp) | (rw [e10]; simp) | (rw [e12]; simp)
    | (rw [e13]; simp) | (rw [e20]; simp) | (rw [e21]; simp) | (rw [e23]; simp) | (rw [e30]; simp)
    | (rw [e31]; simp) | (rw [e32]; simp)

theorem propus_transpose (a b d : ZMod v → ℤ) (ha : ∀ u, a (-u) = a u) :
    (propus a b d).transpose = propus a b d := by
  ext ⟨p, i⟩ ⟨q, j⟩
  rw [Matrix.transpose_apply]
  fin_cases p <;> fin_cases q <;> simp only [propus] <;>
  first
    | rfl
    | (rw [show i - j = -(j - i) by ring, ha])
    | (rw [show j - i = -(i - j) by ring, ha])
    | (rw [show -j - i = -i - j by ring])
    | (rw [show j + i = i + j by ring])

theorem propus_entries (a b d : ZMod v → ℤ)
    (ha1 : ∀ u, a u = 1 ∨ a u = -1) (hb1 : ∀ u, b u = 1 ∨ b u = -1) (hd1 : ∀ u, d u = 1 ∨ d u = -1)
    (P Q : Fin 4 × ZMod v) : propus a b d P Q = 1 ∨ propus a b d P Q = -1 := by
  obtain ⟨p, i⟩ := P; obtain ⟨q, j⟩ := Q
  have na : ∀ u, -a u = 1 ∨ -a u = -1 := fun u => by rcases ha1 u with h | h <;> simp [h]
  have nb : ∀ u, -b u = 1 ∨ -b u = -1 := fun u => by rcases hb1 u with h | h <;> simp [h]
  have nd : ∀ u, -d u = 1 ∨ -d u = -1 := fun u => by rcases hd1 u with h | h <;> simp [h]
  fin_cases p <;> fin_cases q <;> simp only [propus] <;>
    first | exact ha1 _ | exact hb1 _ | exact hd1 _ | exact na _ | exact nb _ | exact nd _

end Propus

/-! ## Part 2: an explicit propus difference family in Z_133.

X1 (symmetric) = {0, 1, 2, 3, 4, 5, 11, 12, 19, 20, 22, 24, 26, 28, 29, 33, 36, 38, 40, 41, 42, 44, 46, 48, 51, 52, 53, 55, 57, 60, 63, 70, 73, 76, 78, 80, 81, 82, 85, 87, 89, 91, 92, 93, 95, 97, 100, 104, 105, 107, 109, 111, 113, 114, 121, 122, 128, 129, 130, 131, 132}
X2 = X3 = {0, 2, 4, 5, 14, 16, 17, 21, 22, 28, 29, 30, 35, 36, 39, 40, 41, 42, 43, 44, 45, 48, 51, 52, 53, 54, 55, 56, 58, 59, 62, 63, 64, 68, 70, 71, 73, 74, 79, 80, 82, 83, 84, 85, 89, 90, 91, 96, 98, 100, 102, 104, 105, 106, 109, 112, 115, 116, 117, 119, 125, 126, 129, 130}
X4 = {1, 2, 6, 11, 12, 16, 17, 19, 20, 22, 23, 26, 29, 35, 38, 40, 41, 43, 46, 48, 51, 52, 53, 54, 56, 57, 59, 61, 62, 66, 70, 71, 74, 76, 79, 84, 87, 89, 90, 91, 95, 105, 107, 109, 112, 113, 114, 116, 117, 119, 120, 121, 122, 123, 126, 129, 132}
Parameters (133; 61, 64, 64, 57; 113).  Encoded below as bitmasks (bit u set iff u ∈ X). -/

namespace Sym532
open Propus

def mA : ℕ := 10556763366080868712124069046882359842879
def mB : ℕ := 2170261461792587175097721996842952245301
def mD : ℕ := 6231042658474337582372523691468885006406

/-- the ±1 sequences: -1 on the block, +1 elsewhere -/
def sA : ZMod 133 → ℤ := fun u => if Nat.testBit mA u.val then -1 else 1
def sB : ZMod 133 → ℤ := fun u => if Nat.testBit mB u.val then -1 else 1
def sD : ZMod 133 → ℤ := fun u => if Nat.testBit mD u.val then -1 else 1

lemma pm (m : ℕ) (u : ZMod 133) : (if Nat.testBit m u.val then (-1 : ℤ) else 1) = 1 ∨
    (if Nat.testBit m u.val then (-1 : ℤ) else 1) = -1 := by
  split_ifs <;> simp

set_option maxRecDepth 100000 in
/-- kernel-checked periodic autocorrelation identity PAF_a + 2 PAF_b + PAF_d = 0 off zero -/
theorem paf_identity : ∀ t : ZMod 133, t ≠ 0 → C sA sA t + 2 * C sB sB t + C sD sD t = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sA_symm : ∀ u : ZMod 133, sA (-u) = sA u := by
  decide +kernel

/-- The main theorem: a symmetric Hadamard matrix of order 532 exists. -/
theorem symmetric_hadamard_532 :
    ∃ H : Matrix (Fin 532) (Fin 532) ℤ,
      (∀ i j, H i j = 1 ∨ H i j = -1) ∧ H.transpose = H ∧
      H * H.transpose = (532 : ℤ) • (1 : Matrix (Fin 532) (Fin 532) ℤ) := by
  let e : Fin 4 × ZMod 133 ≃ Fin 532 := finProdFinEquiv
  let M := propus sA sB sD
  have hA : ∀ u, sA u = 1 ∨ sA u = -1 := fun u => pm mA u
  have hB : ∀ u, sB u = 1 ∨ sB u = -1 := fun u => pm mB u
  have hD : ∀ u, sD u = 1 ∨ sD u = -1 := fun u => pm mD u
  have hT : M.transpose = M := propus_transpose sA sB sD sA_symm
  have hM : M * M.transpose = (4 * ((133 : ℕ) : ℤ)) • (1 : Matrix (Fin 4 × ZMod 133) (Fin 4 × ZMod 133) ℤ) :=
    propus_mul_transpose sA sB sD hA hB hD paf_identity
  refine ⟨Matrix.reindex e e M, ?_, ?_, ?_⟩
  · intro i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    exact propus_entries sA sB sD hA hB hD _ _
  · rw [Matrix.transpose_reindex, hT]
  · rw [Matrix.transpose_reindex, hT]
    have h1 : Matrix.reindex e e M * Matrix.reindex e e M = Matrix.reindex e e (M * M) := by
      simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    rw [h1, show M * M = M * M.transpose by rw [hT], hM]
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply,
      EmbeddingLike.apply_eq_iff_eq, smul_eq_mul]
    norm_num

end Sym532


/-! ## Part 3: an explicit propus difference family in Z_183.

X1 (symmetric) = {0, 4, 6, 7, 15, 17, 18, 19, 21, 23, 24, 28, 29, 33, 35, 37, 39, 40, 45, 46, 47, 48, 49, 50, 53, 54, 55, 56, 59, 63, 66, 69, 71, 72, 74, 77, 79, 83, 84, 86, 91, 92, 97, 99, 100, 104, 106, 109, 111, 112, 114, 117, 120, 124, 127, 128, 129, 130, 133, 134, 135, 136, 137, 138, 143, 144, 146, 148, 150, 154, 155, 159, 160, 162, 164, 165, 166, 168, 176, 177, 179}
X2 = X3 = {0, 4, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17, 19, 20, 21, 22, 23, 29, 31, 35, 36, 38, 39, 40, 43, 45, 46, 47, 48, 49, 50, 53, 54, 55, 59, 62, 65, 66, 67, 71, 75, 76, 79, 80, 81, 82, 86, 89, 92, 95, 97, 98, 100, 104, 106, 109, 110, 115, 117, 119, 120, 123, 124, 126, 127, 128, 131, 134, 135, 136, 138, 139, 141, 143, 144, 146, 151, 155, 156, 157, 158, 164, 165, 168, 171, 176, 178, 179, 180, 181}
X4 = {0, 1, 2, 3, 4, 5, 6, 9, 10, 15, 19, 21, 23, 25, 27, 31, 34, 46, 47, 49, 50, 52, 53, 54, 58, 59, 60, 61, 64, 68, 70, 73, 78, 81, 86, 88, 90, 96, 97, 100, 101, 102, 103, 104, 106, 107, 109, 116, 117, 118, 120, 121, 122, 123, 127, 128, 132, 134, 135, 136, 138, 139, 140, 142, 143, 144, 146, 151, 153, 155, 156, 157, 161, 163, 164, 165, 167, 169, 170, 174, 176, 179, 180}
Parameters (183; 81, 91, 91, 83; 163).  Encoded below as bitmasks (bit u set iff u ∈ X). -/

namespace Sym732
open Propus

def mA : ℕ := 1054136625622133230883559322991699971475371213473087697
def mB : ℕ := 5846077389462234277958905794061145584891602296154877905
def mD : ℕ := 2420986565355251613476856529399935428361535989943404159

def sA : ZMod 183 → ℤ := fun u => if Nat.testBit mA u.val then -1 else 1
def sB : ZMod 183 → ℤ := fun u => if Nat.testBit mB u.val then -1 else 1
def sD : ZMod 183 → ℤ := fun u => if Nat.testBit mD u.val then -1 else 1

lemma pm (m : ℕ) (u : ZMod 183) : (if Nat.testBit m u.val then (-1 : ℤ) else 1) = 1 ∨
    (if Nat.testBit m u.val then (-1 : ℤ) else 1) = -1 := by
  split_ifs <;> simp

set_option maxRecDepth 100000 in
theorem paf_identity : ∀ t : ZMod 183, t ≠ 0 → C sA sA t + 2 * C sB sB t + C sD sD t = 0 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem sA_symm : ∀ u : ZMod 183, sA (-u) = sA u := by
  decide +kernel

/-- A symmetric Hadamard matrix of order 732 exists. -/
theorem symmetric_hadamard_732 :
    ∃ H : Matrix (Fin 732) (Fin 732) ℤ,
      (∀ i j, H i j = 1 ∨ H i j = -1) ∧ H.transpose = H ∧
      H * H.transpose = (732 : ℤ) • (1 : Matrix (Fin 732) (Fin 732) ℤ) := by
  let e : Fin 4 × ZMod 183 ≃ Fin 732 := finProdFinEquiv
  let M := propus sA sB sD
  have hA : ∀ u, sA u = 1 ∨ sA u = -1 := fun u => pm mA u
  have hB : ∀ u, sB u = 1 ∨ sB u = -1 := fun u => pm mB u
  have hD : ∀ u, sD u = 1 ∨ sD u = -1 := fun u => pm mD u
  have hT : M.transpose = M := propus_transpose sA sB sD sA_symm
  have hM : M * M.transpose = (4 * ((183 : ℕ) : ℤ)) • (1 : Matrix (Fin 4 × ZMod 183) (Fin 4 × ZMod 183) ℤ) :=
    propus_mul_transpose sA sB sD hA hB hD paf_identity
  refine ⟨Matrix.reindex e e M, ?_, ?_, ?_⟩
  · intro i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
    exact propus_entries sA sB sD hA hB hD _ _
  · rw [Matrix.transpose_reindex, hT]
  · rw [Matrix.transpose_reindex, hT]
    have h1 : Matrix.reindex e e M * Matrix.reindex e e M = Matrix.reindex e e (M * M) := by
      simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    rw [h1, show M * M = M * M.transpose by rw [hT], hM]
    ext i j
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply,
      EmbeddingLike.apply_eq_iff_eq, smul_eq_mul]
    norm_num

end Sym732

#print axioms Sym532.symmetric_hadamard_532
#print axioms Sym732.symmetric_hadamard_732
#print axioms Propus.propus_mul_transpose
