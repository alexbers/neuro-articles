# [An improved upper bound for binary covering codes of length 20 and covering radius 3](paper.pdf)

**Author:** Claude (AI model by Anthropic); run and submitted by Aleksandr Bersenev

*Produced autonomously by Claude (Opus 5.5) agents in Claude Code. Not an official Anthropic publication. Not peer reviewed.*

**Date:** October 14, 2026

## Citation

```bibtex
@misc{Claude:An-improved-upper-bound-for-binary-covering-codes-of-length-20-and-covering-radius-3-October-14-2026,
  author = {Claude and Bersenev, Aleksandr},
  note = {Claude: AI model by Anthropic; produced autonomously; run and submitted by A. Bersenev; not an official Anthropic publication},
  title = {{An improved upper bound for binary covering codes of length 20 and covering radius 3}},
  howpublished = {Claude research preprint (unpublished, not peer reviewed)},
  year = {2026}
}
```

## Verification status
- **Lean-certified** (Lean 4.35.0 + Mathlib, `lean/Main.lean`, output `lean/lean_output.txt`):
  - `KTwentyThree.main : ∃ C : Finset (Fin 20 → Fin 2), C.card ≤ 1984 ∧ ∀ x, ∃ c ∈ C, hammingDist x c ≤ 3`
    (i.e. K(20,3) ≤ 1984; previous table bound 2048);
  - `KTwentyThree.codeB`: the auxiliary length-14 code has ≤ 248 words and covering radius ≤ 2
    (its normality is the lemma `B_norm`).
  - `#print axioms`: `[propext, Classical.choice, Quot.sound]` for both. No `sorry`, no `native_decide`;
    finite checks by `decide +kernel`. Check time ≈ 105–150 s, ≈ 12 GB RAM.
- **Paper-only**: the novelty claim (based on Kéri's tables and a literature search, "to our knowledge");
  the description of the search that found the code; the negative results on the football pool problem.
- **Reproduce**: `~/claude_math/bin/leancheck <ID> lean/Main.lean` on the node, or
  `attempts2/bin/leanmath lean/Main.lean` locally (needs Mathlib; `leanchk` core-only is not sufficient).
  Independent brute force: `gcc -O3 -o verify_cov data/verify_cov.c && ./verify_cov 20 3 data/C_n20_R3_M1984.txt`.
- Data: `data/C_n20_R3_M1984.txt` (the 1984 codewords, bit i = coordinate i), `data/B_n14_R2_M248.txt`
  (the normal 248-word code), `data/B_syndromes_S62.txt` (parity-check columns and the 62 syndromes).
