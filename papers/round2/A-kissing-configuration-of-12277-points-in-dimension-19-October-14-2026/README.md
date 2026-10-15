# [A kissing configuration of 12 277 points in dimension 19](paper.pdf)

**Author:** Claude (AI model by Anthropic); run and submitted by Aleksandr Bersenev

*Produced autonomously by Claude (Opus 5.5) agents in Claude Code. Not an official Anthropic publication. Not peer reviewed.*

**Date:** October 14, 2026

## Citation

```bibtex
@misc{Claude:A-kissing-configuration-of-12277-points-in-dimension-19-October-14-2026,
  author = {Claude and Bersenev, Aleksandr},
  note = {Claude: AI model by Anthropic; produced autonomously; run and submitted by A. Bersenev; not an official Anthropic publication},
  title = {{A kissing configuration of 12277 points in dimension 19}},
  howpublished = {Claude research preprint (unpublished, not peer reviewed)},
  year = {2026}
}
```

## Verification status

- **Lean-certified** (core Lean 4.35, no Mathlib; 33 modules in `lean/mods2/`, compiled in order by `lean/mods2/run_mods.sh`, all with exit code 0; the same content as one file is `lean/Main.lean`; the log is in `lean/lean_output.txt`):
  - `K19.kissing19 : ∃ L : List (List Int), L.length = 12277 ∧ L.Nodup ∧ (∀ v ∈ L, v.length = 20 ∧ tsumT v = 0 ∧ 0 < dot v v) ∧ L.Pairwise Compat`.
    Here `tsumT v = v₀+v₃+v₆+v₈`, i.e. the vectors lie in a 19-dimensional hyperplane of ℝ²⁰, and
    `Compat x y ⇔ ⟨x,y⟩ ≤ 0 ∨ 4⟨x,y⟩² ≤ ⟨x,x⟩⟨y,y⟩`, i.e. the angle is at least 60°.
  - Axioms: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `axiom`, `admit` or `native_decide`.
    The finite checks use `decide +kernel`.
  - Not formalised: the standard facts that a hyperplane of ℝ²⁰ is isometric to ℝ¹⁹ and that
    normalising vectors with pairwise angles ≥ 60° gives a kissing configuration.
- **Independent exact checks:** `data/verify19.py` and `data/check2.py`, two different exact
  integer programs, check all pairs of `data/RECORD12277.txt` (20 coordinates) and of
  `data/RECORD12277_R19.txt` (19 coordinates).
- **Paper-only:** novelty (to our knowledge, as of 2026-10-15) and the numerical negative evidence of
  Section 5.
- **Reproduce:** `python3 data/check2.py data/RECORD12277_R19.txt` (about 25 s);
  `lean/mods2/run_mods.sh` on the node (about 50 min on 3 cores; the peak memory per module is at most 7 GB). Checking the one-file `lean/Main.lean` in a single process is also possible but needs much more memory.
