# [The best constant in Smale's mean value problem exceeds 1.048](paper.pdf)

**Author:** Claude (AI model by Anthropic); run and submitted by Aleksandr Bersenev

*Produced autonomously by Claude (Opus 5.5) agents in Claude Code. Not an official Anthropic publication. Not peer reviewed.*

**Date:** October 14, 2026

## Citation

```bibtex
@misc{Claude:The-best-constant-in-Smales-mean-value-problem-exceeds-1.048-October-14-2026,
  author = {Claude and Bersenev, Aleksandr},
  note = {Claude: AI model by Anthropic; produced autonomously; run and submitted by A. Bersenev; not an official Anthropic publication},
  title = {{The best constant in Smale's mean value problem exceeds 1.048}},
  howpublished = {Preprint (not peer reviewed), \url{https://github.com/alexbers/neuro-articles/tree/main/papers/round2/The-best-constant-in-Smales-mean-value-problem-exceeds-1.048-October-14-2026}},
  year = {2026}
}
```

## Verification status
* **Lean 4.35.0 + Mathlib v4.35.0 (formal):** `lean/Main.lean`, theorem `SmaleKoebe.witness`
  (Theorem 2.2 of the paper): the rounded Koebe map `Φ` is injective with `Φ' ≠ 0` on the closed unit
  disc, `H = F∘Φ` has `H' ≠ 0` on the closed unit disc, `|H| = |Φ − Φ(w₀)|/|B(w₀)|` on the unit circle,
  `H(w₀) = 0`, `H'(w₀) = Φ'(w₀)`, `|w₀| < 1` and `1/|B(w₀)| > 131/125 = 1.048`.
  `#print axioms`: `[propext, Classical.choice, Quot.sound]`; no `sorry`, no `native_decide`; finite
  computations (exact cubic, 561-node quadtree, rational side conditions) by kernel `decide +kernel`.
  Output: `lean/lean_output.txt` (node 37 s, local 120 s, ~8 GB). Reproduce:
  `lake env lean lean/Main.lean` inside a Mathlib v4.35.0 project
  (`Main.lean` = `KoebeWitness.lean + KoebePart2.lean + data/koebe_witness_data.lean + KoebePart3.lean`).
* **Paper proofs only:** realisation lemma (Lemma 3.1: Runge + Fekete lemniscates) and monotonicity
  `K_d ≤ K_{d+1}` (Lemma 3.2). The main theorem `lim K_d ≥ 1.048` therefore rests on the Lean-certified
  witness plus these two standard-analysis lemmas.
* **Ball arithmetic (rigorous, not Lean):** two independent witnesses in other geometries,
  margins `[1.0416157180171132949… ± 7.3e-34]` (`data/design_TS1.json`) and
  `[1.0373104912259030897… ± 7.3e-34]` (`data/design_Z2.json`), certified by `code/verify_cont.py`
  (python-flint 0.9.0 / Arb); negative control rejected (`data/verify_negative_control.txt`).
* **Exact margin (rational arithmetic, not Lean):** Lean certifies `m > 1.048`; the sharper
  `1.048069073225 < m < 1.048069073226` is an exact rational comparison of `m² = |1−āw₀|²/|w₀−a|²`.
* **Independent referee check:** `data/check_witness.py` (exact rationals + mpmath; run with
  `python3 data/check_witness.py`) recomputes `z₀`, the cubic `P` and its zeros, the margin, the
  univalence radius (1.000433) and replays the Lean quadtree certificate; all checks pass. Referee
  verdict: CORRECT; independent Lean re-run passed (32 s, standard axioms).
* **Credit:** the qualitative failure of Smale's conjecture in all large degrees already follows from
  GPT-6 Astra's Lean disproof (https://github.com/tadamcz/mean-value-problem) plus monotonicity
  (Lemma 3.2); Steps 4–5 of Lemma 3.1 follow their `eventually_allBadWitness_perturbation`. New here:
  the fjord witness with margin bounded away from 1 and the explicit bound 1.048.
