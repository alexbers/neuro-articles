# [A new lower bound for the cap set capacity](paper.pdf)

**Author:** Claude (AI model by Anthropic); run and submitted by Aleksandr Bersenev

*Produced autonomously by Claude (Opus 5.5) agents in Claude Code. Not an official Anthropic publication. Not peer reviewed.*

**Date:** October 14, 2026

## Citation

```bibtex
@misc{Claude:A-new-lower-bound-for-the-cap-set-capacity-October-14-2026,
  author = {Claude and Bersenev, Aleksandr},
  note = {Claude: AI model by Anthropic; produced autonomously; run and submitted by A. Bersenev; not an official Anthropic publication},
  title = {{A new lower bound for the cap set capacity}},
  howpublished = {Preprint (not peer reviewed), \url{https://github.com/alexbers/neuro-articles/tree/main/papers/round2/A-new-lower-bound-for-the-cap-set-capacity-October-14-2026}},
  year = {2026}
}
```

## Verification status
* **Lean-certified** (`lean/Main.lean`, Lean 4.35.0 + Mathlib; output in `lean/lean_output.txt`):
  `main_cap_648` — there is a cap set `A ⊆ F_3^648` with `|A| > (2220334/1000000)^648`;
  `main_capacity` — for every `k ≥ 1` a cap set in `F_3^(648k)` of size `> (2220334/1000000)^(648k)`;
  `admissible_new` — the new set is admissible.  Edel's extended-product lemma, Edel's recursive lemma
  (for Ĩ(4,3)), the mixed-weight counting formula, the type-level reduction and the soundness of the
  bitset checker are proved in Lean.
* **Axioms:** `propext`, `Classical.choice`, `Quot.sound`, plus the auxiliary axioms of
  **`native_decide`** for the finite checks on the explicit rows (`rows_chkP`, `rows_chkT`, `rows_nodup`)
  and the explicit Calderbank–Fishburn collection (`cf_checks`, `CF_card`).  The final integer inequality
  is kernel-checked (`decide +kernel`).
* **Paper-only:** monotonicity of r_3 in n / existence of the limit C (standard); the literature
  status ("best previously known").
* **Reproduce:** `~/claude_math/bin/leancheck B05 lean/Main.lean` on the node, or
  `attempts2/bin/leanmath lean/Main.lean` locally (~4 min, ~8.5 GB); independent check
  `python3 verify_rows.py data/rows.txt 4` (script in attempts2/B05-capsets/src).
