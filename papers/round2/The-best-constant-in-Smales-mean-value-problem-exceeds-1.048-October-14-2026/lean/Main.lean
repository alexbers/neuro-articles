import Mathlib

/-!
# A Lean-certified continuum witness for Smale's mean value problem

All data are Gaussian rationals.  For `0 < r < 1`, `|c| < 1` put
`Φ(w) = r (w + c)(1 + c̄ w) / ((1 + c̄ w) − r (w + c))²` (= `k(u)`, `k(u) = u/(1−u)²` the Koebe function,
`u = r (w + c)/(1 + c̄ w)`), `B(w) = (w − a)/(1 − ā w)`, `H(w) = (Φ(w) − Φ(w₀)) B(w) / B(w₀)`.
The main theorem `witness` shows: `Φ` is injective on the closed unit disc, `H` is differentiable
with non-vanishing derivative on the closed unit disc, `|H| = m |Φ − Φ(w₀)|` on the unit circle with
`m = 1/|B(w₀)| > m₀`, and `H(w₀) = 0`, `H'(w₀) = Φ'(w₀)`.
-/

namespace SmaleKoebe

open Complex

/-! ## Gaussian rationals -/

abbrev GQ := ℚ × ℚ

def gadd (a b : GQ) : GQ := (a.1 + b.1, a.2 + b.2)
def gsub (a b : GQ) : GQ := (a.1 - b.1, a.2 - b.2)
def gmul (a b : GQ) : GQ := (a.1 * b.1 - a.2 * b.2, a.1 * b.2 + a.2 * b.1)
def gconj (a : GQ) : GQ := (a.1, -a.2)
def gnormSq (a : GQ) : ℚ := a.1 * a.1 + a.2 * a.2
def ginv (a : GQ) : GQ := (a.1 / gnormSq a, -a.2 / gnormSq a)
def gabs1 (a : GQ) : ℚ := |a.1| + |a.2|
def gof (q : ℚ) : GQ := (q, 0)

noncomputable def toC (a : GQ) : ℂ := (a.1 : ℂ) + (a.2 : ℂ) * I

@[simp] lemma toC_re (a : GQ) : (toC a).re = a.1 := by simp [toC]
@[simp] lemma toC_im (a : GQ) : (toC a).im = a.2 := by simp [toC]

lemma toC_add (a b : GQ) : toC (gadd a b) = toC a + toC b := by
  simp only [toC, gadd]; push_cast; ring
lemma toC_sub (a b : GQ) : toC (gsub a b) = toC a - toC b := by
  simp only [toC, gsub]; push_cast; ring
lemma toC_mul (a b : GQ) : toC (gmul a b) = toC a * toC b := by
  simp only [toC, gmul]; push_cast; ring_nf; rw [I_sq]; ring
lemma toC_conj (a : GQ) : toC (gconj a) = (starRingEnd ℂ) (toC a) := by
  apply Complex.ext <;> simp [toC, gconj]
lemma toC_gof (q : ℚ) : toC (gof q) = (q : ℂ) := by simp [toC, gof]
lemma normSq_toC (a : GQ) : Complex.normSq (toC a) = (gnormSq a : ℝ) := by
  simp [Complex.normSq_apply, gnormSq]
lemma toC_inv (a : GQ) : toC (ginv a) = (toC a)⁻¹ := by
  apply Complex.ext
  · simp [ginv, Complex.inv_re, normSq_toC, gnormSq]
  · simp [ginv, Complex.inv_im, normSq_toC, gnormSq]
lemma norm_le_gabs1 (a : GQ) : ‖toC a‖ ≤ (gabs1 a : ℝ) := by
  have h := Complex.norm_le_abs_re_add_abs_im (toC a)
  simp only [toC_re, toC_im] at h
  simpa [gabs1] using h

/-! ## Polynomials as coefficient lists (lowest degree first) -/

abbrev Poly := List GQ

noncomputable def evalC : Poly → ℂ → ℂ
  | [], _ => 0
  | a :: l, w => toC a + w * evalC l w

def addL : Poly → Poly → Poly
  | [], q => q
  | a :: p, [] => a :: p
  | a :: p, b :: q => gadd a b :: addL p q

def scaleL (c : GQ) (p : Poly) : Poly := p.map (gmul c)

def mulL : Poly → Poly → Poly
  | [], _ => []
  | a :: p, q => addL (scaleL a q) ((0, 0) :: mulL p q)

def negL (p : Poly) : Poly := scaleL (-1, 0) p

lemma evalC_addL : ∀ (p q : Poly) (w : ℂ), evalC (addL p q) w = evalC p w + evalC q w
  | [], q, w => by simp [addL, evalC]
  | a :: p, [], w => by simp [addL, evalC]
  | a :: p, b :: q, w => by
      simp only [addL, evalC, toC_add, evalC_addL p q w]; ring

lemma evalC_scaleL (c : GQ) : ∀ (p : Poly) (w : ℂ), evalC (scaleL c p) w = toC c * evalC p w
  | [], w => by simp [scaleL, evalC]
  | a :: p, w => by
      have := evalC_scaleL c p w
      simp only [scaleL, List.map_cons, evalC, toC_mul] at this ⊢
      rw [this]; ring

lemma toC_zero' : toC ((0, 0) : GQ) = 0 := by simp [toC]

lemma evalC_mulL : ∀ (p q : Poly) (w : ℂ), evalC (mulL p q) w = evalC p w * evalC q w
  | [], q, w => by simp [mulL, evalC]
  | a :: p, q, w => by
      simp only [mulL, evalC_addL, evalC_scaleL, evalC, toC_zero', evalC_mulL p q w]; ring

lemma evalC_negL (p : Poly) (w : ℂ) : evalC (negL p) w = -evalC p w := by
  simp [negL, evalC_scaleL, toC]

/-! ## Taylor shift and the quadtree zero-exclusion certificate -/

def shiftL (z : GQ) : Poly → Poly
  | [] => []
  | a :: l => addL [a] (mulL [z, (1, 0)] (shiftL z l))

lemma evalC_shiftL (z : GQ) : ∀ (l : Poly) (δ : ℂ), evalC (shiftL z l) δ = evalC l (toC z + δ)
  | [], δ => by simp [shiftL, evalC]
  | a :: l, δ => by
      simp only [shiftL, evalC_addL, evalC_mulL, evalC_shiftL z l δ, evalC]
      simp [toC]

/-- `Σ_{k≥0} |t_k|₁ d^{k+1}` -/
def tb : Poly → ℚ → ℚ
  | [], _ => 0
  | t :: l, d => d * (gabs1 t + tb l d)

lemma tb_nonneg : ∀ (l : Poly) (d : ℚ), 0 ≤ d → 0 ≤ tb l d
  | [], d, _ => by simp [tb]
  | t :: l, d, hd => by
      simp only [tb]
      have := tb_nonneg l d hd
      have : 0 ≤ gabs1 t := by simp only [gabs1]; positivity
      positivity

lemma norm_mul_evalC_le : ∀ (l : Poly) (δ : ℂ) (d : ℚ), 0 ≤ d → ‖δ‖ ≤ d →
    ‖δ * evalC l δ‖ ≤ (tb l d : ℝ)
  | [], δ, d, _, _ => by simp [evalC, tb]
  | t :: l, δ, d, hd, hδ => by
      have ih := norm_mul_evalC_le l δ d hd hδ
      simp only [evalC, tb]
      push_cast
      calc ‖δ * (toC t + δ * evalC l δ)‖ = ‖δ‖ * ‖toC t + δ * evalC l δ‖ := norm_mul _ _
        _ ≤ (d : ℝ) * ((gabs1 t : ℝ) + (tb l d : ℝ)) := by
            gcongr
            · exact (norm_add_le _ _).trans (add_le_add (norm_le_gabs1 t) ih)

def outside (cx cy h : ℚ) : Bool :=
  decide (1 < max (|cx| - h) 0 ^ 2 + max (|cy| - h) 0 ^ 2)

def safe (P : Poly) (cx cy h : ℚ) : Bool :=
  match shiftL (cx, cy) P with
  | [] => false
  | t0 :: rest => decide (tb rest (3 * h / 2) ^ 2 < gnormSq t0)

inductive QTree
  | leaf : QTree
  | node : QTree → QTree → QTree → QTree → QTree

def check (P : Poly) : QTree → ℚ → ℚ → ℚ → Bool
  | .leaf, cx, cy, h => outside cx cy h || safe P cx cy h
  | .node a b c d, cx, cy, h =>
      check P a (cx - h/2) (cy - h/2) (h/2) && check P b (cx + h/2) (cy - h/2) (h/2) &&
      check P c (cx - h/2) (cy + h/2) (h/2) && check P d (cx + h/2) (cy + h/2) (h/2)

lemma outside_sound {cx cy h : ℚ} (ho : outside cx cy h = true) (w : ℂ)
    (hx : |w.re - cx| ≤ h) (hy : |w.im - cy| ≤ h) : 1 < ‖w‖ := by
  simp only [outside, decide_eq_true_eq] at ho
  have hx' : (max (|(cx:ℝ)| - h) 0) ≤ |w.re| := by
    apply max_le _ (abs_nonneg _)
    have h1 := abs_sub_abs_le_abs_sub (cx:ℝ) w.re
    rw [abs_sub_comm (cx:ℝ) w.re] at h1
    have : |(cx:ℝ)| - |w.re| ≤ h := le_trans h1 (by exact_mod_cast hx)
    linarith
  have hy' : (max (|(cy:ℝ)| - h) 0) ≤ |w.im| := by
    apply max_le _ (abs_nonneg _)
    have h1 := abs_sub_abs_le_abs_sub (cy:ℝ) w.im
    rw [abs_sub_comm (cy:ℝ) w.im] at h1
    have : |(cy:ℝ)| - |w.im| ≤ h := le_trans h1 (by exact_mod_cast hy)
    linarith
  have key : (1:ℝ) < max (|(cx:ℝ)| - h) 0 ^ 2 + max (|(cy:ℝ)| - h) 0 ^ 2 := by
    have e : ((max (|cx| - h) 0 ^ 2 + max (|cy| - h) 0 ^ 2 : ℚ) : ℝ) =
        max (|(cx:ℝ)| - h) 0 ^ 2 + max (|(cy:ℝ)| - h) 0 ^ 2 := by push_cast; rfl
    exact_mod_cast (show ((1:ℚ):ℝ) < ((max (|cx| - h) 0 ^ 2 + max (|cy| - h) 0 ^ 2 : ℚ) : ℝ)
      from by exact_mod_cast ho).trans_eq e
  have hm1 : 0 ≤ max (|(cx:ℝ)| - h) 0 := le_max_right _ _
  have hm2 : 0 ≤ max (|(cy:ℝ)| - h) 0 := le_max_right _ _
  have hsq : 1 < ‖w‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have e1 : w.re * w.re = |w.re| ^ 2 := by rw [sq_abs]; ring
    have e2 : w.im * w.im = |w.im| ^ 2 := by rw [sq_abs]; ring
    rw [e1, e2]
    nlinarith [pow_le_pow_left₀ hm1 hx' 2, pow_le_pow_left₀ hm2 hy' 2]
  nlinarith [norm_nonneg w]

lemma safe_sound (P : Poly) {cx cy h : ℚ} (hh : 0 ≤ h) (hs : safe P cx cy h = true) (w : ℂ)
    (hx : |w.re - cx| ≤ h) (hy : |w.im - cy| ≤ h) : evalC P w ≠ 0 := by
  set z : GQ := (cx, cy) with hz
  set δ : ℂ := w - toC z with hδ
  have hw : w = toC z + δ := by rw [hδ]; ring
  have hδre : |δ.re| ≤ h := by simp [hδ, z, toC]; exact_mod_cast hx
  have hδim : |δ.im| ≤ h := by simp [hδ, z, toC]; exact_mod_cast hy
  have hδn : ‖δ‖ ≤ ((3 * h / 2 : ℚ) : ℝ) := by
    have h2 : ‖δ‖ ^ 2 ≤ ((3 * h / 2 : ℚ) : ℝ) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have a1 : δ.re * δ.re ≤ (h:ℝ) ^ 2 := by
        have := sq_abs δ.re; nlinarith [abs_nonneg δ.re]
      have a2 : δ.im * δ.im ≤ (h:ℝ) ^ 2 := by
        have := sq_abs δ.im; nlinarith [abs_nonneg δ.im]
      push_cast; nlinarith
    have hpos : (0:ℝ) ≤ ((3 * h / 2 : ℚ) : ℝ) := by push_cast; positivity
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hpos (by norm_num)).mp h2
  have hval : evalC P w = evalC (shiftL z P) δ := by rw [evalC_shiftL, ← hw]
  rw [hval]
  unfold safe at hs
  rcases hsh : shiftL z P with _ | ⟨t0, rest⟩
  · rw [hz] at hsh; rw [hsh] at hs; simp at hs
  · rw [hz] at hsh; rw [hsh] at hs
    simp only [decide_eq_true_eq] at hs
    simp only [evalC]
    intro h0
    have hd : (0:ℚ) ≤ 3 * h / 2 := by positivity
    have hb := norm_mul_evalC_le rest δ (3 * h / 2) hd hδn
    have e : toC t0 = -(δ * evalC rest δ) := by linear_combination h0
    have h1 : ‖toC t0‖ ≤ (tb rest (3 * h / 2) : ℝ) := by rw [e, norm_neg]; exact hb
    have h2 : ‖toC t0‖ ^ 2 ≤ (tb rest (3 * h / 2) : ℝ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hsq : ‖toC t0‖ ^ 2 = (gnormSq t0 : ℝ) := by
      rw [← Complex.normSq_eq_norm_sq, normSq_toC]
    have hlt : ((tb rest (3 * h / 2) : ℚ) : ℝ) ^ 2 < (gnormSq t0 : ℝ) := by exact_mod_cast hs
    linarith

theorem check_sound (P : Poly) : ∀ (t : QTree) (cx cy h : ℚ), 0 ≤ h → check P t cx cy h = true →
    ∀ w : ℂ, |w.re - cx| ≤ h → |w.im - cy| ≤ h → ‖w‖ ≤ 1 → evalC P w ≠ 0 := by
  intro t
  induction t with
  | leaf =>
    intro cx cy h hh hc w hx hy hw
    simp only [check, Bool.or_eq_true] at hc
    rcases hc with ho | hs
    · exact absurd hw (not_le.mpr (outside_sound ho w hx hy))
    · exact safe_sound P hh hs w hx hy
  | node a b c d iha ihb ihc ihd =>
    intro cx cy h hh hc w hx hy hw
    simp only [check, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨ha, hb⟩, hc'⟩, hd⟩ := hc
    have hh2 : (0:ℚ) ≤ h / 2 := by linarith
    have hx' := abs_le.mp hx
    have hy' := abs_le.mp hy
    by_cases hxs : w.re ≤ cx
    · by_cases hys : w.im ≤ cy
      · apply iha _ _ _ hh2 ha w _ _ hw
        · rw [abs_le]; push_cast; constructor <;> linarith
        · rw [abs_le]; push_cast; constructor <;> linarith
      · apply ihc _ _ _ hh2 hc' w _ _ hw
        · rw [abs_le]; push_cast; constructor <;> linarith
        · rw [abs_le]; push_cast; constructor <;> linarith
    · by_cases hys : w.im ≤ cy
      · apply ihb _ _ _ hh2 hb w _ _ hw
        · rw [abs_le]; push_cast; constructor <;> linarith
        · rw [abs_le]; push_cast; constructor <;> linarith
      · apply ihd _ _ _ hh2 hd w _ _ hw
        · rw [abs_le]; push_cast; constructor <;> linarith
        · rw [abs_le]; push_cast; constructor <;> linarith

theorem zero_free_of_check (P : Poly) (t : QTree) (h : check P t 0 0 1 = true) :
    ∀ w : ℂ, ‖w‖ ≤ 1 → evalC P w ≠ 0 := by
  intro w hw
  apply check_sound P t 0 0 1 (by norm_num) h w _ _ hw
  · have := Complex.abs_re_le_norm w; push_cast; simpa using this.trans hw
  · have := Complex.abs_im_le_norm w; push_cast; simpa using this.trans hw

end SmaleKoebe

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

namespace SmaleKoebe
def rq : ℚ := ((497498487 : ℚ)/500000000)
def cq : GQ := (((-105117631 : ℚ)/125000000), ((3016503 : ℚ)/1000000000))
def w0q : GQ := (((-149268011 : ℚ)/200000000), ((313274719 : ℚ)/1000000000))
def aq : GQ := (((-744989837 : ℚ)/1000000000), ((-504190327 : ℚ)/1000000000))
def m0 : ℚ := ((131 : ℚ)/125)
local notation "l" => QTree.leaf
local notation "n" => QTree.node
def certTree : QTree := (n (n (n l (n l l (n l l l l) l) (n l (n l l l l) l l) (n l l l l)) (n (n l l l l) l (n l l l l) (n l l l l)) (n (n l l (n l l (n l l l (n l l l l)) (n l l (n l l l l) l)) (n l l l l)) (n l l l l) (n (n (n (n l (n l l l (n l l l l)) l (n l (n (n l l l l) (n l l l l) (n l (n l l l l) l (n (n l l l l) l (n l l l (n l l l l)) (n l l (n l l l l) l))) (n (n l l l l) l (n l l (n l l l l) l) (n l l l l))) l (n (n l (n (n l (n (n l l (n l l l l) l) (n l l l l) (n l l l l) (n l l l l)) (n l (n l (n l l l l) l (n l l l l)) l (n l l l l)) (n (n l l l l) l (n l l l l) l)) (n (n l l l l) l (n l l l l) l) (n (n l l l l) (n l l l l) l l) (n l l l l)) (n l l l l) (n (n l l l l) (n l l l l) l l)) (n (n (n l l l l) l l l) l (n l l l l) l) (n l (n l l l l) l l) (n l l l l)))) (n (n l l (n l l l l) l) (n l l l l) (n (n l l (n l l l l) l) (n l l l l) (n (n l l l l) l l l) l) (n l l l l)) (n l (n (n l l l l) (n l l l l) l l) l (n l l l l)) (n (n (n l l l l) l l l) l (n l l l l) l)) (n (n l l l l) l (n l l l l) l) (n (n l l l l) (n l l l l) l l) (n l l l l)) (n (n l l l l) l l l) (n (n l l l l) (n l l l l) l l) (n l l l l)) (n (n l l l l) l (n l l l l) l)) (n (n l l l l) (n l l l l) (n l l l l) l)) (n (n l l l l) (n l l l l) (n l l l l) (n l l l l)) (n (n (n (n l l l l) (n l l l l) l l) (n l l l l) (n l l l l) (n l l l l)) (n (n l l l l) l l l) (n l l l l) (n l l l l)) (n (n l l l l) l (n l l l l) l))
end SmaleKoebe

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
