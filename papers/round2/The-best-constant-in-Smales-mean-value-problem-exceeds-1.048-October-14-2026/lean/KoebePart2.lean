
/-! ## The Koebe-type witness: symbolic part -/

namespace SmaleKoebe

open Complex

section Sym

variable (r c cb a ab z0 B0 : ℂ)

def Ef (w : ℂ) : ℂ := (1 + cb * w) - r * (w + c)
def Sf (w : ℂ) : ℂ := (1 + cb * w) + r * (w + c)
noncomputable def Φf (w : ℂ) : ℂ := r * (w + c) * (1 + cb * w) / (Ef r c cb w) ^ 2
noncomputable def Φd (w : ℂ) : ℂ := r * (1 - c * cb) * Sf r c cb w / (Ef r c cb w) ^ 3
noncomputable def Bf (w : ℂ) : ℂ := (w - a) / (1 - ab * w)
noncomputable def Bd (w : ℂ) : ℂ := (1 - a * ab) / (1 - ab * w) ^ 2
noncomputable def Hf (w : ℂ) : ℂ := (Φf r c cb w - z0) * Bf a ab w / B0
noncomputable def Hd (w : ℂ) : ℂ := (Φd r c cb w * Bf a ab w + (Φf r c cb w - z0) * Bd a ab w) / B0
def Psym (w : ℂ) : ℂ :=
  r * (1 - c * cb) * Sf r c cb w * (w - a) * (1 - ab * w) +
    (1 - a * ab) * (r * (w + c) * (1 + cb * w) * Ef r c cb w - z0 * (Ef r c cb w) ^ 3)

lemma hasDerivAt_Φf (w : ℂ) (hE : Ef r c cb w ≠ 0) :
    HasDerivAt (Φf r c cb) (Φd r c cb w) w := by
  have h1 : HasDerivAt (fun w : ℂ => r * (w + c)) (r * 1) w :=
    ((hasDerivAt_id' w).add_const c).const_mul r
  have h2 : HasDerivAt (fun w : ℂ => 1 + cb * w) (cb * 1) w :=
    ((hasDerivAt_id' w).const_mul cb).const_add 1
  have hN := h1.mul h2
  have h3 : HasDerivAt (fun w : ℂ => Ef r c cb w) (cb * 1 - r * 1) w :=
    (((hasDerivAt_id' w).const_mul cb).const_add 1).sub (((hasDerivAt_id' w).add_const c).const_mul r)
  have hD := h3.pow 2
  have hq := hN.div hD (pow_ne_zero 2 hE)
  unfold Φf
  refine hq.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.pow_apply]
  unfold Φd Sf
  field_simp
  unfold Ef
  push_cast
  ring

lemma hasDerivAt_Bf (w : ℂ) (hB : 1 - ab * w ≠ 0) : HasDerivAt (Bf a ab) (Bd a ab w) w := by
  have h1 : HasDerivAt (fun w : ℂ => w - a) 1 w := (hasDerivAt_id' w).sub_const a
  have h2 : HasDerivAt (fun w : ℂ => 1 - ab * w) (-(ab * 1)) w := by
    have := ((hasDerivAt_id' w).const_mul ab).const_sub 1
    exact this
  have hq := h1.div h2 hB
  unfold Bf
  refine hq.congr_deriv ?_
  unfold Bd
  field_simp
  ring

lemma hasDerivAt_Hf (w : ℂ) (hE : Ef r c cb w ≠ 0) (hB : 1 - ab * w ≠ 0) :
    HasDerivAt (Hf r c cb a ab z0 B0) (Hd r c cb a ab z0 B0 w) w := by
  have h := ((hasDerivAt_Φf r c cb w hE).sub_const z0).mul (hasDerivAt_Bf a ab w hB)
  have h2 := h.div_const B0
  unfold Hf Hd
  exact h2

lemma Hd_identity (w : ℂ) (hE : Ef r c cb w ≠ 0) (hB : 1 - ab * w ≠ 0) (hB0 : B0 ≠ 0) :
    Hd r c cb a ab z0 B0 w * ((Ef r c cb w) ^ 3 * (1 - ab * w) ^ 2 * B0) = Psym r c cb a ab z0 w := by
  unfold Hd Φd Φf Bf Bd Psym
  set E := Ef r c cb w with hEdef
  set S := Sf r c cb w
  have hB' : 1 - w * ab ≠ 0 := by rwa [mul_comm] at hB
  have hE3 : E ^ 3 ≠ 0 := pow_ne_zero 3 hE
  have hE2 : E ^ 2 ≠ 0 := pow_ne_zero 2 hE
  have hB2 : (1 - ab * w) ^ 2 ≠ 0 := pow_ne_zero 2 hB
  field_simp


end Sym

/-! ### Norm facts -/

lemma normSq_identity (c w : ℂ) :
    Complex.normSq (1 + (starRingEnd ℂ) c * w) - Complex.normSq (w + c) =
      (1 - Complex.normSq w) * (1 - Complex.normSq c) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

lemma norm_add_le_norm_one_add (c w : ℂ) (hc : ‖c‖ < 1) (hw : ‖w‖ ≤ 1) :
    ‖w + c‖ ≤ ‖1 + (starRingEnd ℂ) c * w‖ := by
  have h := normSq_identity c w
  have h1 : 0 ≤ (1 - Complex.normSq w) * (1 - Complex.normSq c) := by
    apply mul_nonneg
    · rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
    · rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg c]
  have h2 : ‖w + c‖ ^ 2 ≤ ‖1 + (starRingEnd ℂ) c * w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]; linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp h2

lemma one_add_ne_zero (c w : ℂ) (hc : ‖c‖ < 1) (hw : ‖w‖ ≤ 1) : 1 + (starRingEnd ℂ) c * w ≠ 0 := by
  intro h
  have : ‖(starRingEnd ℂ) c * w‖ = 1 := by
    have e : (starRingEnd ℂ) c * w = -1 := by linear_combination h
    rw [e]; simp
  rw [norm_mul, Complex.norm_conj] at this
  have : ‖c‖ * ‖w‖ < 1 := by
    calc ‖c‖ * ‖w‖ ≤ ‖c‖ * 1 := by gcongr
      _ < 1 := by linarith
  linarith

lemma Ef_ne_zero (r : ℝ) (c w : ℂ) (hr0 : 0 ≤ r) (hr : r < 1) (hc : ‖c‖ < 1) (hw : ‖w‖ ≤ 1) :
    Ef (r : ℂ) c ((starRingEnd ℂ) c) w ≠ 0 := by
  unfold Ef
  intro h
  have hpos : 0 < ‖1 + (starRingEnd ℂ) c * w‖ := norm_pos_iff.mpr (one_add_ne_zero c w hc hw)
  have e : 1 + (starRingEnd ℂ) c * w = (r : ℂ) * (w + c) := by linear_combination h
  have := congrArg norm e
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] at this
  have hle := norm_add_le_norm_one_add c w hc hw
  have h4 : r * ‖w + c‖ ≤ r * ‖1 + (starRingEnd ℂ) c * w‖ := mul_le_mul_of_nonneg_left hle hr0
  rw [← this] at h4
  nlinarith

lemma one_sub_ne_zero (a w : ℂ) (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1) : 1 - (starRingEnd ℂ) a * w ≠ 0 := by
  intro h
  have : ‖(starRingEnd ℂ) a * w‖ = 1 := by
    have e : (starRingEnd ℂ) a * w = 1 := by linear_combination -h
    rw [e]; simp
  rw [norm_mul, Complex.norm_conj] at this
  have : ‖a‖ * ‖w‖ < 1 := by
    calc ‖a‖ * ‖w‖ ≤ ‖a‖ * 1 := by gcongr
      _ < 1 := by linarith
  linarith

lemma norm_Bf_eq_one (a w : ℂ) (ha : ‖a‖ < 1) (hw : ‖w‖ = 1) :
    ‖Bf a ((starRingEnd ℂ) a) w‖ = 1 := by
  have hden := one_sub_ne_zero a w ha hw.le
  have hsq : Complex.normSq (1 - (starRingEnd ℂ) a * w) = Complex.normSq (w - a) := by
    have hw2 : w.re * w.re + w.im * w.im = 1 := by
      have := Complex.normSq_eq_norm_sq w
      rw [hw, one_pow, Complex.normSq_apply] at this
      exact this
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
    linear_combination (-(1 - (a.re * a.re + a.im * a.im))) * hw2
  have hn : ‖1 - (starRingEnd ℂ) a * w‖ = ‖w - a‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (1 - (starRingEnd ℂ) a * w)), ← Real.sqrt_sq (norm_nonneg (w - a)),
      ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, hsq]
  unfold Bf
  rw [norm_div, hn, div_self]
  rw [← hn]; exact norm_ne_zero_iff.mpr hden

/-- injectivity of the Koebe-type map on the closed unit disc -/
lemma Φf_injOn (r : ℝ) (c : ℂ) (hr0 : 0 < r) (hr : r < 1) (hc : ‖c‖ < 1) :
    Set.InjOn (Φf (r : ℂ) c ((starRingEnd ℂ) c)) (Metric.closedBall 0 1) := by
  intro w1 hw1 w2 hw2 heq
  simp only [Metric.mem_closedBall, dist_zero_right] at hw1 hw2
  set cb := (starRingEnd ℂ) c
  have hA1 := one_add_ne_zero c w1 hc hw1
  have hA2 := one_add_ne_zero c w2 hc hw2
  have hE1 := Ef_ne_zero r c w1 hr0.le hr hc hw1
  have hE2 := Ef_ne_zero r c w2 hr0.le hr hc hw2
  -- u_i = r (w_i + c)/(1 + cb w_i), |u_i| < 1
  set u1 := (r : ℂ) * (w1 + c) / (1 + cb * w1) with hu1
  set u2 := (r : ℂ) * (w2 + c) / (1 + cb * w2) with hu2
  have hu_lt : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖(r : ℂ) * (w + c) / (1 + cb * w)‖ < 1 := by
    intro w hw
    have hA := one_add_ne_zero c w hc hw
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
      div_lt_one (norm_pos_iff.mpr hA)]
    have hle := norm_add_le_norm_one_add c w hc hw
    have hpos := norm_pos_iff.mpr hA
    nlinarith
  have h1 : ‖u1‖ < 1 := hu_lt w1 hw1
  have h2 : ‖u2‖ < 1 := hu_lt w2 hw2
  -- Φ = u/(1-u)^2
  have hΦ : ∀ w : ℂ, 1 + cb * w ≠ 0 → Ef (r:ℂ) c cb w ≠ 0 →
      Φf (r:ℂ) c cb w = ((r : ℂ) * (w + c) / (1 + cb * w)) / (1 - (r : ℂ) * (w + c) / (1 + cb * w)) ^ 2 := by
    intro w hA hE
    unfold Φf
    have hA' : 1 + w * cb ≠ 0 := by rwa [mul_comm] at hA
    have : 1 - (r : ℂ) * (w + c) / (1 + cb * w) = Ef (r:ℂ) c cb w / (1 + cb * w) := by
      unfold Ef; field_simp
    rw [this]
    field_simp
  rw [hΦ w1 hA1 hE1, hΦ w2 hA2 hE2] at heq
  rw [← hu1, ← hu2] at heq
  have hne1 : 1 - u1 ≠ 0 := by
    intro h; have : u1 = 1 := by linear_combination -h
    rw [this] at h1; simp at h1
  have hne2 : 1 - u2 ≠ 0 := by
    intro h; have : u2 = 1 := by linear_combination -h
    rw [this] at h2; simp at h2
  have hprod : (u1 - u2) * (1 - u1 * u2) = 0 := by
    field_simp at heq
    linear_combination heq
  have hu12 : 1 - u1 * u2 ≠ 0 := by
    intro h
    have : ‖u1 * u2‖ = 1 := by
      have e : u1 * u2 = 1 := by linear_combination -h
      rw [e]; simp
    rw [norm_mul] at this
    nlinarith [norm_nonneg u1, norm_nonneg u2]
  have hu : u1 = u2 := by
    rcases mul_eq_zero.mp hprod with h | h
    · linear_combination h
    · exact absurd h hu12
  rw [hu1, hu2] at hu
  have hA1' : 1 + cb * w1 ≠ 0 := hA1
  have hA2' : 1 + cb * w2 ≠ 0 := hA2
  rw [div_eq_div_iff hA1' hA2'] at hu
  have hcc : 1 - c * cb ≠ 0 := by
    intro h
    have : c * cb = 1 := by linear_combination -h
    have h3 : ‖c * cb‖ = 1 := by rw [this]; simp
    rw [norm_mul, Complex.norm_conj] at h3
    nlinarith [norm_nonneg c]
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have : (r : ℂ) * (1 - c * cb) * (w1 - w2) = 0 := by linear_combination hu
  rcases mul_eq_zero.mp this with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hr'
    · exact absurd h' hcc
  · linear_combination h

end SmaleKoebe
