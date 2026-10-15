# [Settling small open cases of signed difference sets](paper.pdf)

**Author:** Claude (AI model by Anthropic); run and submitted by Aleksandr Bersenev

*Produced autonomously by Claude (Opus 5.5) agents in Claude Code. Not an official Anthropic publication. Not peer reviewed.*

**Date:** October 8, 2026

## Citation

```bibtex
@misc{Claude:Settling-small-open-cases-of-signed-difference-sets-October-8-2026,
  author = {Claude and Bersenev, Aleksandr},
  note = {Claude: AI model by Anthropic; produced autonomously; run and submitted by A. Bersenev; not an official Anthropic publication},
  title = {{Settling small open cases of signed difference sets}},
  howpublished = {Preprint (not peer reviewed), \url{https://github.com/alexbers/neuro-articles/tree/main/papers/round1/Settling-small-open-cases-of-signed-difference-sets-October-8-2026}},
  year = {2026}
}
```

## Verification status

- **Lean-certified** (`lean/Main.lean`, Lean 4.34.1 core only, no Mathlib; output in
  `lean/lean_output.txt`, whose last line `leanchk: wall=1221.58s maxrss=5790648kB exit=0` is the
  resource log of the wrapper that ran Lean; an independent re-run during review, same file
  (SHA-256 `5a0ae7262b372df772ae65fd294ae1ed4c69d47e2560a3c6cfc16b0873ce4e27`), gave exit 0,
  587 s wall, 5.78 GB max RSS and identical output):
  - `no_SDS_9_8_1_Z3xZ3 : ¬ ∃ D : Nat → Int, IsSDS [3,3] 8 1 D`. This checks all 3⁹
    coefficient vectors with no symmetry reduction. Axioms: `[propext, Quot.sound]`.
  - 45 existence theorems `sds_<v>_<k>_<λ>_G<moduli> : ∃ D : Nat → Int, IsSDS ms k λ D`, one for
    every certificate in the appendix table. Axioms: `[propext, Quot.sound]`.
  - 23 sanity lemmas `model_G<moduli> : GroupModelOK ms`, showing that the mixed-radix model is
    the group ℤ_{m₁}×⋯×ℤ_{m_r}. Axioms: `[propext]`.
  - There is no `sorry`, no `native_decide` and no custom `axiom`.
- **Paper-only (human proofs):**
  - the short intersection-number proof of the (9,8,1) nonexistence;
  - the parity argument for (27,25,16);
  - the explanations of the 8 database corrections;
  - the eighth-order cyclotomic description of (25,12,1). Its certificate itself is
    Lean-checked.
- **Computer-only, not formally verified:** nonexistence for the 16 open cases with v ≤ 28 listed
  in Prop. 5.2. This comes from an exhaustive C search (`data/sds_ex.c`, log `data/ex_small.txt`,
  validation `data/validate_ex.txt`).
- **Novelty classification** (tiers a/b/c) is to our knowledge as of October 8, 2026. For the 11
  tier-b cases (order 64), an exhaustive search (`data/pds_z3.py`, cross-checked by `data/pds_ex.c`)
  shows that regular (64,21,8,6) and (64,18,2,6) partial difference sets exist only in Z_2^6,
  Z_2^2 x Z_4^2 and Z_8^2 among the abelian groups of order 64; hence 9 of the 11 tier-b cases
  cannot come from the PDS argument (Lemma 2.3), and the two (64,46,30) cases in Z_2^2 x Z_4^2 and
  Z_8^2 do (Prop. 4.5).
- **History:** all group-specific cases treated here (noncyclic abelian groups) entered the
  repository only in version 1.2 (April 24, 2026); versions 1.0 (Dec 2022) and 1.1 (Mar 2023)
  covered essentially only cyclic groups. Among the He–Chen–Ge constructions, v1.2 incorporates
  the Paley-type ones but not the (3^{2m+1}, 3^{2m}+1, 1) family ((243,82,1) in Z_3^5 is still
  listed as open).
- Reproduce:
  - Lean: `cd lean && lean Main.lean` with a Lean 4.34.1 toolchain (no project file, no Mathlib;
    10–20 minutes, about 6 GB of memory); compare with `lean/lean_output.txt`.
  - Certificates: `python3 data/verify_certificates.py`.
  - Hyperoval correction: `python3 data/hyperoval.py`.
  - PDS search for Prop. 4.5: `python3 data/pds_z3.py nls` and `python3 data/pds_z3.py ls`
    (needs the `z3-solver` package; seconds to a minute per group), or compile `data/pds_ex.c`.
  - Review: see `REVIEW-2026-10-08.md`.
  - PDF: `cd build && latexmk -pdf main.tex`. If the TeX install has no pdflatex format, first
    generate one locally with `TEXMFVAR=$PWD/texlocal/var fmtutil-user --byfmt pdflatex; updmap-user`.
