import SUCore
import SULeaves0
import SULeaves1
import SULeaves2
import SULeaves3
import SULeaves4
import SULeaves5
import SULeaves6

/-!
# Main theorem: a certificate for the sign-uncertainty constant

`SU.P_sign`: for `P = ∑_{j ≤ 300} γ_j Λ_{2j}` (`Λ_n = 2^n n! L_n^{(-1/2)}`, defined in `SUCore` as `Lam` by the
three-term recurrence; `γ` an explicit list of integers), `P(0) < 0` and `P(u) > 0` for all `u ≥ 48 / 25`.
Consequently (classical Hermite-eigenfunction argument, on paper) `C_SU ≤ 48 / (2π · 25)`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace SU
open PolyPos

theorem P_cert : posCertK2 16623 20 Pl ((393216, 458752, 204800, 204800) :: leaves.tail) = true := by
  rw [← hhead]
  unfold posCertK2
  rw [hchain]
  simp only [leaves, List.all_append, hleaf0, hleaf1, hleaf2, hleaf3, hleaf4, hleaf5, hleaf6, hleaf7, hleaf8, hleaf9, hleaf10, hleaf11, hleaf12, hleaf13, hleaf14, hleaf15, hleaf16, hleaf17, hleaf18, hleaf19, hleaf20, hleaf21, hleaf22, hleaf23, hleaf24, hleaf25, hleaf26, hleaf27, hleaf28, hleaf29, hleaf30, hleaf31, hleaf32, hleaf33, hleaf34, hleaf35, hleaf36, hleaf37, hleaf38, hleaf39, hleaf40, Bool.and_self]

/-- **Main finite theorem.**  `P(u) = ∑_{j ≤ 300} γ_j Λ_{2j}(u)` satisfies `P(0) < 0` and
`P(u) > 0` for every real `u ≥ 48 / 25`. -/
theorem P_sign :
    (∑ j ∈ Finset.range 301, (γ.getD j 0 : ℝ) * Lam (2 * j) 0) < 0 ∧
    ∀ u : ℝ, (48 : ℝ) / 25 ≤ u → 0 < ∑ j ∈ Finset.range 301, (γ.getD j 0 : ℝ) * Lam (2 * j) u := by
  have hP : ∀ u : ℝ, ∑ j ∈ Finset.range 301, (γ.getD j 0 : ℝ) * Lam (2 * j) u = ev Pl u :=
    combo_eq γ Pl 300 6090 hB hE
  constructor
  · rw [hP, ev_zero]
    have := P0_neg
    simp only [decide_eq_true_eq] at this
    exact_mod_cast this
  · intro u hu
    rw [hP]
    apply posCertK2_spec 16623 20 Pl 393216 458752 204800 204800 leaves.tail P_cert u
    have e : ((393216 : ℕ) : ℝ) / ((204800 : ℕ) : ℝ) = (48 : ℝ) / 25 := by norm_num
    rw [e]; exact hu

end SU

#print axioms SU.P_sign
