# [New lower bounds for hypergraph Ramsey numbers from affine-invariant colourings](paper.pdf)

**Author:** Claude (AI model by Anthropic); run and submitted by Aleksandr Bersenev

*Produced autonomously by Claude (Opus 5.5) agents in Claude Code. Not an official Anthropic publication. Not peer reviewed.*

**Date:** October 14, 2026

## Citation

```bibtex
@misc{Claude:New-lower-bounds-for-hypergraph-Ramsey-numbers-from-affine-invariant-colourings-October-14-2026,
  author = {Claude and Bersenev, Aleksandr},
  note = {Claude: AI model by Anthropic; produced autonomously; run and submitted by A. Bersenev; not an official Anthropic publication},
  title = {{New lower bounds for hypergraph Ramsey numbers from affine-invariant colourings}},
  howpublished = {Preprint (not peer reviewed), \url{https://github.com/alexbers/neuro-articles/tree/main/papers/round2/New-lower-bounds-for-hypergraph-Ramsey-numbers-from-affine-invariant-colourings-October-14-2026}},
  year = {2026}
}
```

## Verification status

- **Lean-certified** (`lean/Main.lean`, Lean 4.35.0, core library only, no Mathlib; all finite checks by
  `decide +kernel`, **no `native_decide`**): `R453.main` (R(4,5;3) ≥ 38), `R453f.main` (the same, re-checked
  without using any symmetry), `R553.main` (R(5,5;3) ≥ 98), `R463.main` (R(4,6;3) ≥ 68), `R554.main`
  (R(5,5;4) ≥ 38), `R564.main` (R(5,6;4) ≥ 98, colouring of GF(97)). Axioms for every theorem
  (`lean/lean_output.txt`, exit 0): `[propext, Quot.sound]`. Also included: `lean/Main79.lean` (same file with the
  GF(79) instance of R564, i.e. R(5,6;4) ≥ 80; `lean/lean_output_Main79.txt`) and `lean/R564_q97.lean`
  (the GF(97) certificate alone; `lean/lean_output_R564_q97.txt`), both checked with the same axioms.
- **Lean-certified with Mathlib** (`lean/MainFinset.lean`, `lean/lean_output_finset.txt`): `R453.main_finset`,
  `R553.main_finset` — the same bounds stated with `Finset (Fin N)`; axioms `[propext, Classical.choice, Quot.sound]`.
- **Script-checked only** (`data/verify.c`, `data/verify4.c`): R(5,6;4) ≥ 104 (AGL(1,101)- and AGL(1,103)-invariant
  colourings); R(5,5;3) ≥ 90 (GF(89), superseded).
- **Paper-only**: novelty (DS1 revision #18 of April 24, 2026, and web/GitHub/arXiv search on October 14, 2026);
  the corollary R(5,5,5;3) ≥ 9410 via the product construction quoted in DS1.
- **Reproduce**: `cd lean && lean Main.lean` (Lean 4.35.0 via elan, no lakefile needed; 4595 s CPU on one core, 13.7 GB);
  colourings: `data/*_red.txt.gz` and `data/describe_*.txt`; search: `data/gens.py`, `data/ginv.c`,
  `data/ginv4.c` + kissat (Section 2 of the paper); independent checks: `data/verify.c`, `data/verify4.c`,
  `data/pycheck.py`.
