# [Proof of Sun's conjecture on coprime adjacent sums (OEIS A228886)](paper.pdf)

**Author:** Claude (AI model by Anthropic); run and submitted by Aleksandr Bersenev

*Produced autonomously by Claude (Opus 5.5) agents in Claude Code. Not an official Anthropic publication. Not peer reviewed.*

**Date:** October 8, 2026

## Citation

```bibtex
@misc{Claude:Proof-of-Suns-conjecture-on-coprime-adjacent-sums-OEIS-A228886-October-8-2026,
  author = {Claude and Bersenev, Aleksandr},
  note = {Claude: AI model by Anthropic; produced autonomously; run and submitted by A. Bersenev; not an official Anthropic publication},
  title = {{Proof of Sun's conjecture on coprime adjacent sums (OEIS A228886)}},
  howpublished = {Claude research preprint (unpublished, not peer reviewed)},
  year = {2026}
}
```

The conjecture is due to Zhi-Wei Sun (OEIS A228886, Sep 2013; arXiv:1309.1679, Conjecture 3.9).
Sun also proved the odd case (Remark 3.9(ii) of arXiv:1309.1679). The even case and the companion
conjecture with moduli 2n±1 are new to our knowledge as of October 8, 2026. One source could not be
checked: Sun's 2021 Chinese-language book of conjectures.

## Verification status

**Lean-certified.** The proofs use Lean 4.34.1 with the core library only: no Mathlib, no `sorry`,
no `native_decide`. They are in `lean/Main.lean`.

- `A228886.sun_conjecture`: for n ≥ 1,
  `(∃ l, SunCycle n (n - 1) (n + 1) l) ↔ (n ≠ 2 ∧ n ≠ 4)`.
- `A228886.sun_companion`: for n ≥ 1,
  `(∃ l, SunCycle n (2 * n - 1) (2 * n + 1) l) ↔ n ≠ 2`.
- `#print axioms` reports `[propext, Classical.choice, Quot.sound]` for both theorems; see
  `lean/lean_output.txt`.
- The check takes about 480 s of wall time and about 1.6 GB of memory. Re-checked independently on
  October 8, 2026 with a fresh Lean 4.34.1 install: exit 0, 449 s, 1.56 GB, identical output.

**Paper-only.** Nothing; every mathematical claim of the paper is covered by the Lean file. The
following are not formal statements and are not covered:

- the literature or novelty assessment;
- the remark on how the construction was found;
- the exhaustive-search remark for n = 8.

**Reproduce:**

- With Lean 4.34.1 installed (for example through `elan`), run `lean lean/Main.lean` from this
  directory. The expected output (the `#eval` lines and the two `#print axioms` lines) is in
  `lean/lean_output.txt`.
- For the independent numerical check, run `python3 data/verify_constructions.py 3000`. It checks
  all constructions for n ≤ 3000 and recomputes A228886(1..11) by brute force.

The search scripts that found the constructions lived in the working directory
`attempts/A03-a228886-coprime-circle/`; that directory is not part of this package.
