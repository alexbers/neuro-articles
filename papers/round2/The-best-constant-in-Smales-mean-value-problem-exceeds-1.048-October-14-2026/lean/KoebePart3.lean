
/-! ## The concrete witness -/

namespace SmaleKoebe

open Complex

def cbq : GQ := gconj cq
def abq : GQ := gconj aq
def oneq : GQ := (1, 0)
def E0q : GQ := gsub (gadd oneq (gmul cbq w0q)) (gmul (gof rq) (gadd w0q cq))
def z0q : GQ := gmul (gmul (gmul (gof rq) (gadd w0q cq)) (gadd oneq (gmul cbq w0q))) (ginv (gmul E0q E0q))
def K1q : GQ := gmul (gof rq) (gsub oneq (gmul cq cbq))
def K2q : GQ := gsub oneq (gmul aq abq)
def Sl : Poly := [gadd oneq (gmul (gof rq) cq), gadd cbq (gof rq)]
def El : Poly := [gsub oneq (gmul (gof rq) cq), gsub cbq (gof rq)]
def wal : Poly := [gsub (0, 0) aq, oneq]
def oal : Poly := [oneq, gsub (0, 0) abq]
def wcl : Poly := [cq, oneq]
def ocl : Poly := [oneq, cbq]
/-- the cubic `Psym` with exact Gaussian-rational coefficients -/
def Plist : Poly :=
  addL (scaleL K1q (mulL Sl (mulL wal oal)))
    (scaleL K2q (addL (scaleL (gof rq) (mulL (mulL wcl ocl) El)) (negL (scaleL z0q (mulL El (mulL El El))))))

/-! complex constants and the witness functions -/
noncomputable def rC : ℂ := ((rq : ℝ) : ℂ)
noncomputable def cC : ℂ := toC cq
noncomputable def aC : ℂ := toC aq
noncomputable def w0C : ℂ := toC w0q
/-- `Φ(w) = r (w + c)(1 + c̄ w) / ((1 + c̄ w) − r (w + c))²`, a rounded Koebe map -/
noncomputable def Φ (w : ℂ) : ℂ := Φf rC cC ((starRingEnd ℂ) cC) w
noncomputable def Φ' (w : ℂ) : ℂ := Φd rC cC ((starRingEnd ℂ) cC) w
/-- the Blaschke factor `B(w) = (w − a)/(1 − ā w)` -/
noncomputable def B (w : ℂ) : ℂ := Bf aC ((starRingEnd ℂ) aC) w
/-- `H(w) = (Φ(w) − Φ(w₀)) B(w) / B(w₀)`, i.e. `F ∘ Φ` for the continuum witness `F` -/
noncomputable def H (w : ℂ) : ℂ := Hf rC cC ((starRingEnd ℂ) cC) aC ((starRingEnd ℂ) aC) (Φ w0C) (B w0C) w
noncomputable def H' (w : ℂ) : ℂ := Hd rC cC ((starRingEnd ℂ) cC) aC ((starRingEnd ℂ) aC) (Φ w0C) (B w0C) w

lemma toC_one : toC oneq = 1 := by simp [toC, oneq]
lemma toC_zero2 : toC ((0, 0) : GQ) = 0 := by simp [toC]
lemma rC_eq : rC = toC (gof rq) := by simp [rC, toC, gof]

lemma z0q_eq : toC z0q = Φ w0C := by
  simp only [z0q, E0q, Φ, Φf, Ef, toC_mul, toC_add, toC_sub, toC_inv, toC_one, cbq, toC_conj, ← rC_eq]
  simp only [cC, w0C]
  rw [div_eq_mul_inv]
  ring

lemma Plist_eval (w : ℂ) :
    evalC Plist w = Psym rC cC ((starRingEnd ℂ) cC) aC ((starRingEnd ℂ) aC) (Φ w0C) w := by
  simp only [Plist, evalC_addL, evalC_scaleL, evalC_mulL, evalC_negL, Sl, El, wal, oal, wcl, ocl, evalC,
    K1q, K2q, toC_mul, toC_add, toC_sub, toC_one, toC_zero2, cbq, abq, toC_conj, ← rC_eq, ← z0q_eq]
  simp only [Psym, Sf, Ef, cC, aC]
  ring

/-! numeric side conditions, checked by kernel evaluation -/
lemma rq_pos : (0 : ℚ) < rq := by decide +kernel
lemma rq_lt_one : rq < 1 := by decide +kernel
lemma cq_small : gnormSq cq < 1 := by decide +kernel
lemma aq_small : gnormSq aq < 1 := by decide +kernel
lemma w0q_small : gnormSq w0q < 1 := by decide +kernel
lemma w0_ne_a : 0 < gnormSq (gsub w0q aq) := by decide +kernel
lemma margin_check : gnormSq (gsub w0q aq) * m0 ^ 2 < gnormSq (gsub oneq (gmul abq w0q)) := by decide +kernel
lemma cert_check : check Plist certTree 0 0 1 = true := by decide +kernel

lemma norm_lt_one_of (z : GQ) (h : gnormSq z < 1) : ‖toC z‖ < 1 := by
  have h1 : ‖toC z‖ ^ 2 < 1 := by
    rw [← Complex.normSq_eq_norm_sq, normSq_toC]; exact_mod_cast h
  nlinarith [norm_nonneg (toC z)]

lemma hc : ‖cC‖ < 1 := norm_lt_one_of cq cq_small
lemma ha : ‖aC‖ < 1 := norm_lt_one_of aq aq_small
lemma hw0 : ‖w0C‖ < 1 := norm_lt_one_of w0q w0q_small
lemma hr0 : (0 : ℝ) < rq := by exact_mod_cast rq_pos
lemma hr1 : (rq : ℝ) < 1 := by exact_mod_cast rq_lt_one

lemma Sf_ne_zero' (w : ℂ) (hw : ‖w‖ ≤ 1) : Sf rC cC ((starRingEnd ℂ) cC) w ≠ 0 := by
  unfold Sf rC
  intro h
  have hpos : 0 < ‖1 + (starRingEnd ℂ) cC * w‖ := norm_pos_iff.mpr (one_add_ne_zero cC w hc hw)
  have e : 1 + (starRingEnd ℂ) cC * w = -(((rq : ℝ) : ℂ) * (w + cC)) := by linear_combination h
  have := congrArg norm e
  rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0] at this
  have hle := norm_add_le_norm_one_add cC w hc hw
  have h4 : (rq : ℝ) * ‖w + cC‖ ≤ (rq : ℝ) * ‖1 + (starRingEnd ℂ) cC * w‖ :=
    mul_le_mul_of_nonneg_left hle hr0.le
  rw [← this] at h4
  nlinarith [hr1]

lemma Ef_ne_zero' (w : ℂ) (hw : ‖w‖ ≤ 1) : Ef rC cC ((starRingEnd ℂ) cC) w ≠ 0 :=
  Ef_ne_zero (rq : ℝ) cC w hr0.le hr1 hc hw

lemma B0_ne_zero : B w0C ≠ 0 := by
  unfold B Bf
  have h1 : w0C - aC ≠ 0 := by
    intro h
    have : toC (gsub w0q aq) = 0 := by rw [toC_sub]; exact h
    have h2 := congrArg Complex.normSq this
    rw [normSq_toC, map_zero] at h2
    have := w0_ne_a
    have : (0:ℝ) < (gnormSq (gsub w0q aq) : ℝ) := by exact_mod_cast this
    linarith
  exact div_ne_zero h1 (one_sub_ne_zero aC w0C ha hw0.le)

/-- **Main certified statement.** The rounded Koebe map `Φ` is injective with non-vanishing derivative
on the closed unit disc; `H = F ∘ Φ` has non-vanishing derivative on the closed unit disc (i.e. the
continuum witness `F` has no critical point on `D̄ = Φ(𝔻̄)`); on `∂D` we have `|F(z)| = m |z − z₀|`
with `m = 1/|B(w₀)| > m₀`; and `F(z₀) = 0`, `F'(z₀) = 1` (`H(w₀) = 0`, `H'(w₀) = Φ'(w₀)`). -/
theorem witness :
    Set.InjOn Φ (Metric.closedBall 0 1) ∧
    (∀ w : ℂ, ‖w‖ ≤ 1 → HasDerivAt Φ (Φ' w) w ∧ Φ' w ≠ 0) ∧
    (∀ w : ℂ, ‖w‖ ≤ 1 → HasDerivAt H (H' w) w ∧ H' w ≠ 0) ∧
    (∀ w : ℂ, ‖w‖ = 1 → ‖H w‖ = ‖Φ w - Φ w0C‖ / ‖B w0C‖) ∧
    ‖w0C‖ < 1 ∧ H w0C = 0 ∧ H' w0C = Φ' w0C ∧ ((m0 : ℝ) < 1 / ‖B w0C‖) := by
  refine ⟨?_, ?_, ?_, ?_, hw0, ?_, ?_, ?_⟩
  · exact Φf_injOn (rq : ℝ) cC hr0 hr1 hc
  · intro w hw
    refine ⟨hasDerivAt_Φf rC cC _ w (Ef_ne_zero' w hw), ?_⟩
    unfold Φ' Φd
    have hcc : 1 - cC * (starRingEnd ℂ) cC ≠ 0 := by
      rw [Complex.mul_conj]
      intro h
      have : Complex.normSq cC = 1 := by exact_mod_cast (by linear_combination -h : (Complex.normSq cC : ℂ) = 1)
      rw [Complex.normSq_eq_norm_sq] at this
      nlinarith [hc, norm_nonneg cC]
    have hr' : rC ≠ 0 := by unfold rC; exact_mod_cast hr0.ne'
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hr' hcc) (Sf_ne_zero' w hw)) (pow_ne_zero 3 (Ef_ne_zero' w hw))
  · intro w hw
    have hE := Ef_ne_zero' w hw
    have hBw := one_sub_ne_zero aC w ha hw
    refine ⟨hasDerivAt_Hf _ _ _ _ _ _ _ w hE hBw, ?_⟩
    intro h0
    have hid := Hd_identity rC cC ((starRingEnd ℂ) cC) aC ((starRingEnd ℂ) aC) (Φ w0C) (B w0C) w hE hBw B0_ne_zero
    have hP : evalC Plist w ≠ 0 := zero_free_of_check Plist certTree cert_check w hw
    rw [Plist_eval] at hP
    apply hP
    rw [← hid]
    unfold H' at h0
    rw [h0, zero_mul]
  · intro w hw
    unfold H Hf
    rw [norm_div, norm_mul]
    have := norm_Bf_eq_one aC w ha hw
    unfold B at this ⊢
    rw [this, mul_one]
    rfl
  · unfold H Hf
    rw [show Φf rC cC ((starRingEnd ℂ) cC) w0C - Φ w0C = 0 by unfold Φ; ring]
    simp
  · unfold H' Hd Φ'
    have hB0 := B0_ne_zero
    unfold B at hB0
    rw [show Φf rC cC ((starRingEnd ℂ) cC) w0C - Φ w0C = 0 by unfold Φ; ring, zero_mul, add_zero]
    unfold B
    field_simp
  · have hB0 := B0_ne_zero
    have hsq : ‖B w0C‖ ^ 2 = (gnormSq (gsub w0q aq) : ℝ) / (gnormSq (gsub oneq (gmul abq w0q)) : ℝ) := by
      unfold B Bf
      rw [norm_div, div_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
      have e1 : w0C - aC = toC (gsub w0q aq) := by rw [toC_sub]; rfl
      have e2 : 1 - (starRingEnd ℂ) aC * w0C = toC (gsub oneq (gmul abq w0q)) := by
        rw [toC_sub, toC_mul, toC_one, abq, toC_conj]; rfl
      rw [e1, e2, normSq_toC, normSq_toC]
    have hden : (0:ℝ) < (gnormSq (gsub oneq (gmul abq w0q)) : ℝ) := by
      have := margin_check
      have h0 : 0 ≤ gnormSq (gsub w0q aq) * m0 ^ 2 := by
        have := add_nonneg (mul_self_nonneg (gsub w0q aq).1) (mul_self_nonneg (gsub w0q aq).2)
        exact mul_nonneg this (sq_nonneg _)
      exact_mod_cast lt_of_le_of_lt h0 this
    have hmc : ((gnormSq (gsub w0q aq) : ℚ) : ℝ) * (m0 : ℝ) ^ 2 < (gnormSq (gsub oneq (gmul abq w0q)) : ℝ) := by
      exact_mod_cast margin_check
    have hBpos : 0 < ‖B w0C‖ := norm_pos_iff.mpr hB0
    rw [lt_div_iff₀ hBpos]
    have h2 : ((m0 : ℝ) * ‖B w0C‖) ^ 2 < 1 := by
      rw [mul_pow, hsq]
      rw [mul_div_assoc', div_lt_one hden]
      linarith
    nlinarith [sq_nonneg ((m0:ℝ) * ‖B w0C‖), norm_nonneg (B w0C)]

end SmaleKoebe

#print axioms SmaleKoebe.witness
