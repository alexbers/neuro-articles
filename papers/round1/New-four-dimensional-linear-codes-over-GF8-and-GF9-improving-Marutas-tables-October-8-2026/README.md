# [New four-dimensional linear codes over GF(8) and GF(9) improving Maruta's tables](paper.pdf)

**Author:** Claude (AI model by Anthropic); run and submitted by Aleksandr Bersenev

*Produced autonomously by Claude (Opus 5.5) agents in Claude Code. Not an official Anthropic publication. Not peer reviewed.*

**Date:** October 8, 2026

## Citation

```bibtex
@misc{Claude:New-four-dimensional-linear-codes-over-GF8-and-GF9-improving-Marutas-tables-October-8-2026,
  author = {Claude and Bersenev, Aleksandr},
  note = {Claude: AI model by Anthropic; produced autonomously; run and submitted by A. Bersenev; not an official Anthropic publication},
  title = {{New four-dimensional linear codes over GF(8) and GF(9) improving Maruta's tables}},
  howpublished = {Claude research preprint (unpublished, not peer reviewed)},
  year = {2026}
}
```

## Verification status

* **Lean-certified** (`lean/Main.lean`, Lean 4.34.1, core only, no Mathlib; output in
  `lean/lean_output.txt`, 436 s, 3.9 GB):
  * `Q9.main9`: 149 conjuncts `∃ L, IsCode L n d` (one per improved entry of the `q = 9` table);
  * `Q8.main8`: 42 conjuncts (the `q = 8` table);
  * `Q9.GF9_is_field`, `Q8.GF8_is_field`: the coefficient structures are fields;
  * the soundness theorem `isCode_of_certify` and the puncturing theorem `isCode_drop` are fully proved;
    the 32 base-code certificates `C_n_d_cert` are evaluated by the kernel (`decide +kernel`).
  * Axioms: `main9`, `main8` use only `[propext, Classical.choice, Quot.sound]`; `GF9_is_field` uses
    `[propext]`; `GF8_is_field` uses none. No `sorry`, no `native_decide`.
* **Independent computation:** `data/verify.py` enumerates all `q^4 − 1` nonzero codewords of each code
  in `data/codes/` (exact weight distribution). An independent re-implementation also checked all codes.
* **Paper-only / cited, not re-proved:** the lower bounds `n_8(4,d) ≥ g_8(4,d)+1` (Kanazawa–Maruta 2011,
  Thm 1.1(4)) and `n_9(4,d) ≥ g_9(4,d)+1` for `d = 512, 513` (Kumegawa–Okazaki–Maruta 2017, Thm 1.7(4)).
  The 29 exact values in Corollary 2.5 combine these bounds with our certified codes. That each pair
  `(n,d)` improves Maruta's online table is a comparison with the table as of 2026-10-08. Novelty is
  "to our knowledge".
* **Reproduce:** `cd lean && lean Main.lean` with the Lean 4.34.1 toolchain, core library only (≈ 7 min on a
  dedicated core, up to about twice that on a loaded machine; ≈ 3.9 GB), and
  `python3 data/verify.py data/codes/<file>` for each code. Hashes: `data/SHA256SUMS`.

## Review

An independent review (in Russian) with the verification protocol, the list of corrections and the
prior-art analysis is in `REVIEW-2026-10-08.md`.
