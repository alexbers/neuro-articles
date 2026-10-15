# [New certified upper bounds for the sign-uncertainty constant and the first autocorrelation constant](paper.pdf)

**Author:** Claude (AI model by Anthropic); run and submitted by Aleksandr Bersenev

*Produced autonomously by Claude (Opus 5.5) agents in Claude Code. Not an official Anthropic publication. Not peer reviewed.*

**Date:** October 14, 2026

## Citation

```bibtex
@misc{Claude:New-certified-upper-bounds-for-the-sign-uncertainty-constant-and-the-first-autocorrelation-constant-October-14-2026,
  author = {Claude and Bersenev, Aleksandr},
  note = {Claude: AI model by Anthropic; produced autonomously; run and submitted by A. Bersenev; not an official Anthropic publication},
  title = {{New certified upper bounds for the sign-uncertainty constant and the first autocorrelation constant}},
  howpublished = {Claude research preprint (unpublished, not peer reviewed)},
  year = {2026}
}
```

## Verification status

- **Lean-certified** (Lean 4.35.0 + Mathlib; all computations by `decide +kernel`; no `native_decide`,
  no `sorry`, no custom axioms):
  - `lean/su_modules/` (`SUCore.lean`, `SULeaves0–6.lean`, `SUMain.lean`; `lean/Main.lean` = `SUMain.lean`), theorem `SU.P_sign`: for the explicit P = Σ_{j≤300} γ_j Λ_{2j} (Λ_n = 2ⁿn!L_n^{(−1/2)}
    defined by its recurrence), P(0) < 0 and P(u) > 0 for all real u ≥ 48/25. Axioms
    `[propext, Classical.choice, Quot.sound]` (`lean/lean_output.txt`; 9 modules, each ≤ 28 GB and ≤ 2 min on the compute node).
  - `lean/C1.lean`, theorems `C₁_le` and `first_autocorrelation_upper_bound`: C₁ ≤ 1.5027434864131 with
    C₁ defined in Lean as an infimum over admissible functions (continuous statement, Mathlib
    measure theory). Axioms `[propext, Classical.choice, Quot.sound]` (`lean/lean_output_C1.txt`; 141 s, 5.9 GB).
- **Paper-only**: the classical Fourier-analytic reduction for C_SU (Hermite functions are Fourier
  eigenfunctions; Proposition 2.2), hence the final step "P_sign ⇒ C_SU ≤ 48/(50π) = 0.3055775…"; novelty (literature
  and leaderboard search as of October 14, 2026, re-checked October 15, 2026).
- **Script-checked independently**: `data/verify_su.py data` (re-derives P from γ, explicit exact expansion of
  every leaf polynomial, no Kronecker digits); `data/verify_c1.py` (exact int64 convolutions, no Kronecker).
- **Not certified**: the floating-point table of optimal radii r*(D) in Section 2.5 (only the final instance is certified).
- **Reproduce**: `lean/su_modules/build_modules.sh <Mathlib v4.35.0 project> lean/su_modules` and
  `lake env lean lean/C1.lean` inside a Mathlib (v4.35.0) project (a smaller single-file C_SU certificate,
  bound 0.307169, is `lean/SU_D140_singlefile.lean`); `python3 data/verify_su.py data`; `python3 data/verify_c1.py data/c1_heights.npy data/c1_certificate.json`.
