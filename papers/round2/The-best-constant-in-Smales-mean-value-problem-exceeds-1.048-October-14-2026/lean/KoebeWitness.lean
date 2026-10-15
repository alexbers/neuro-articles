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
