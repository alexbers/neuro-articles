# [A balanced 13-variable Boolean function with absolute indicator 112](paper.pdf)

**Author:** Claude (AI model by Anthropic); run and submitted by Aleksandr Bersenev

*Produced autonomously by Claude (Opus 5.5) agents in Claude Code. Not an official Anthropic publication. Not peer reviewed.*

**Date:** October 8, 2026

## Citation

```bibtex
@misc{Claude:A-balanced-13-variable-Boolean-function-with-absolute-indicator-112-October-8-2026,
  author = {Claude and Bersenev, Aleksandr},
  note = {Claude: AI model by Anthropic; produced autonomously; run and submitted by A. Bersenev; not an official Anthropic publication},
  title = {{A balanced 13-variable Boolean function with absolute indicator 112}},
  howpublished = {Claude research preprint (unpublished, not peer reviewed)},
  year = {2026}
}
```

## Verification status

- **Lean-certified** (`lean/Main.lean`, Lean 4.34.1, core only, no Mathlib, all computations by
  `decide +kernel`, no `native_decide`): theorems `A12.main`, `A12.main_statement`, `A12.zhang_zheng_fails_n13`
  — the function `f` with truth table `data/truth_table.hex` is balanced, has an ANF monomial of degree 3
  (so `deg f ≥ 3`), and `|r_f(d)| ≤ 112 < 128 = 2^⌊(13+1)/2⌋` for every `d ≠ 0`.
  Axioms (`lean/lean_output.txt`): `[propext, Classical.choice, Quot.sound]` for all three; 124 s, 2.4 GB.
- **Script-checked only** (`data/verify.py`, output in `data/verify_output.txt`): exact degree 11 (4485 ANF
  monomials), nonlinearity 3980, the distribution of `|r_f(d)|` (312 shifts attain 112),
  invariance under `AGL(1,13)` acting on coordinates.
- **Paper-only**: novelty (literature search as of October 8, 2026); the negative remarks on balanced
  nonlinearity records (Remark 5.1).
- **Reproduce**: Lean: `cd lean && lean Main.lean` (Lean 4.34.1 via elan, core only, no project/lakefile needed;
  about 2 min and 2.4 GB; the last line of `lean/lean_output.txt` was added by a small timing wrapper that is not
  distributed); `python3 data/verify.py data/truth_table.hex`; search: see `data/search/` and Section 3 of the paper.
- **Independent re-check** (review of October 8, 2026, `REVIEW-2026-10-08.md`): `lean Main.lean` reproduced the
  three axiom lines (exit 0, 124.1 s, 2.36 GB); all script-checked parameters were re-derived with independent
  code (weight 4096, Δ = 112 with 312 shifts, nonlinearity 3980, degree 11, 4485 monomials, 74 orbits);
  the search runs with seeds 77 and 41 were reproduced bit for bit; the novelty claim (no balanced
  13-variable function with Δ < 128 in the literature) was checked against the sources cited in the paper.
