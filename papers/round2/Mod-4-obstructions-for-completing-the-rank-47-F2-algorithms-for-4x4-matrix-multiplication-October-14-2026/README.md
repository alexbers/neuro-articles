# [Mod-4 obstructions for completing the rank-47 F2 algorithms for 4x4 matrix multiplication](paper.pdf)

**Author:** Claude (AI model by Anthropic); run and submitted by Aleksandr Bersenev

*Produced autonomously by Claude (Opus 5.5) agents in Claude Code. Not an official Anthropic publication. Not peer reviewed.*

**Date:** October 14, 2026

## Citation

```bibtex
@misc{Claude:Mod-4-obstructions-for-completing-the-rank-47-F2-algorithms-for-4x4-matrix-multiplication-October-14-2026,
  author = {Claude and Bersenev, Aleksandr},
  note = {Claude: AI model by Anthropic; produced autonomously; run and submitted by A. Bersenev; not an official Anthropic publication},
  title = {{Mod-4 obstructions for completing the rank-47 F2 algorithms for 4x4 matrix multiplication}},
  howpublished = {Claude research preprint (unpublished, not peer reviewed)},
  year = {2026}
}
```

## Verification status
* **Lean-certified** (Lean 4.35.0 + Mathlib; `lean/Main.lean` with output `lean/lean_output.txt`, and
  `lean/MainKM47.lean` with output `lean/lean_output_KM47.txt`; both compile with exit code 0, about
  31 and 33 minutes, 13.2 GB):
  * `AT47.no_Z4_completion`: there are no lifts a_t ≡ u_t, b_t ≡ v_t, c_t ≡ w_t (mod 2) of the AlphaTensor
    F2 scheme and no x, M with Σ_t a_t⊗b_t⊗c_t + 2·(x⊗M) = T_{4,4,4} over ZMod 4.
  * `AT47.no_rank48`: no rank-48 decomposition of T_{4,4,4} over ZMod 4 whose first 47 terms reduce mod 2
    to the scheme and whose last term has a factor ≡ 0 (mod 2).
  * `KM47.no_Z4_completion` and `KM47.no_rank48`: the same for the Kauers–Moosbauer scheme.
  * The reduction to F2 linear algebra and the witness argument (`MM4.no_Z4_completion_of_facts`,
    `MM4.no_rank_succ_of_no_completion`) are fully proved in Lean.
* **Axioms** (`#print axioms`): `propext`, `Classical.choice`, `Quot.sound`, plus six auxiliary axioms
  `<NS>.F1_all/F2_all/F3_all/F4_all/F5a_all/F5b._native.native_decide.ax_1_1`, i.e. the certificate facts
  F1–F5b on the explicit witness functionals (1585 for AT47, 1581 for KM47) are evaluated with
  **`native_decide`** (the compiled evaluation is trusted). Fact F0 (the scheme data satisfy
  Σ u v w = T + 2R over ZMod 4) is checked by the kernel (`decide +kernel`); no `sorry`.
* **Independently checked (Python, not Lean):** both certificates (`data/verify_cert.py`,
  `data/verify_cert_output.txt`); exhaustive e=1 scans in all three modes (`data/step1x_scans_444.txt`).
* **Paper-only / computational:** extension of the corollary to Z, Z_2 and to symmetry images; the
  inequivalence and flip-graph rigidity of the two schemes and the Z/4 lift test of the 72,057 nearby rank-48 F2
  schemes (`data/rankprofile.py`, `data/plus48_closure.py`, `data/e0_closure.py`, outputs `data/rigidity_output.txt`,
  `data/e0_closure_output.txt`); the non-exhaustive rank-49/50 searches (`data/search49.py`);
  the ⟨4,5,5⟩ rank-73 scan; 2-adic gauge measurements.
* **Reproduce:** `~/claude_math/bin/leancheck B01 lean/Main.lean 30000` on the node (or
  `attempts2/bin/leanmath lean/Main.lean`); `python3 verify_cert.py data/at444_f2_r47.txt data/wit3_at47.json`;
  `python3 plus48_closure.py data/at444_f2_r47.txt out.txt` (scripts import `fmm.py`, included in `data/`;
  all generators and logs are in attempts2/B01-fmm-ranks).
