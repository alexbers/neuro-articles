# [New best-known configurations for Heilbronn's triangle problem in a triangle with 23 and 35 points](paper.pdf)

**Author:** Claude (AI model by Anthropic); run and submitted by Aleksandr Bersenev

*Produced autonomously by Claude (Opus 5.5) agents in Claude Code. Not an official Anthropic publication. Not peer reviewed.*

**Date:** October 14, 2026

## Citation

```bibtex
@misc{Claude:New-best-known-configurations-for-Heilbronns-triangle-problem-in-a-triangle-with-23-and-35-points-October-14-2026,
  author = {Claude and Bersenev, Aleksandr},
  note = {Claude: AI model by Anthropic; produced autonomously; run and submitted by A. Bersenev; not an official Anthropic publication},
  title = {{New best-known configurations for Heilbronn's triangle problem in a triangle with 23 and 35 points}},
  howpublished = {Preprint (not peer reviewed), \url{https://github.com/alexbers/neuro-articles/tree/main/papers/round2/New-best-known-configurations-for-Heilbronns-triangle-problem-in-a-triangle-with-23-and-35-points-October-14-2026}},
  year = {2026}
}
```

## Verification status

- **Lean-certified** (core Lean 4 only, no Mathlib; no `sorry`/`axiom`/`native_decide`; all finite checks by
  `decide +kernel` through a Boolean checker with a proved soundness lemma), `lean/Main.lean`:
  - `Triangle35.main`: 35 explicit rational points in the triangle (0,0),(1,0),(0,1) such that every triangle
    they span has 2·area ≥ 42542724/10^10, i.e. H△(35) ≥ 0.0042542724;
  - `Triangle23.main`: 23 points, 2·area ≥ 9279055/10^9, i.e. H△(23) ≥ 0.009279055.
  - `#print axioms` for both: `[propext, Classical.choice, Quot.sound]` (`lean/lean_output.txt`; Lean 4.34.1
    ≈ 42 s, Lean 4.35.0 ≈ 83 s, ≈ 2.7 GB). A negative control with a bound slightly above the exact value
    is rejected.
- **Paper-only:** that these values beat the previous records (0.0041984701667575 and 0.0092756410755168,
  N. Sudermann-Merx, October 2026) is a statement about the public table https://math.tejstead.com/heilbronn
  as checked on 2026-10-14 and 2026-10-15 03:00 (+05); affine invariance (standard); the descriptions of the
  tie structure and of the search. No optimality is claimed.
- **Superseded:** the n = 36 improvement found on 2026-10-14 (0.0038740) was overtaken the same day by a
  new record 0.0039985 (N. Sudermann-Merx) and is not claimed.
- **Data:** `data/triangle_n23_record.txt`, `data/triangle_n35_record.txt` (30-digit decimal coordinates,
  exact value in the header), the previous records `data/previous_record_*`, and the independent exact
  checker `data/verify.py`.
- **Reproduce:** `python3 data/verify.py data/triangle_n35_record.txt`; `lean lean/Main.lean`
  (Lean 4.34.1 or 4.35.0, core only; expected output = the two `#print axioms` lines).
- **Build:** `cd build && pdflatex main.tex` (twice); the pdflatex format/font maps were generated with
  `fmtutil-user`/`updmap-user` into a temporary folder inside `build/` (TEXMFVAR/TEXMFCONFIG), deleted afterwards.
