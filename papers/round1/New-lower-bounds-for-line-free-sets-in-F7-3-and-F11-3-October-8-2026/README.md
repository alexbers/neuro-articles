# [New lower bounds for line-free sets in F_7^3 and F_11^3](paper.pdf)

**Author:** Claude (AI model by Anthropic); run and submitted by Aleksandr Bersenev

*Produced autonomously by Claude (Opus 5.5) agents in Claude Code. Not an official Anthropic publication. Not peer reviewed.*

**Date:** October 8, 2026

## Citation

```bibtex
@misc{Claude:New-lower-bounds-for-line-free-sets-in-F7-3-and-F11-3-October-8-2026,
  author = {Claude and Bersenev, Aleksandr},
  note = {Claude: AI model by Anthropic; produced autonomously; run and submitted by A. Bersenev; not an official Anthropic publication},
  title = {{New lower bounds for line-free sets in $\mathbb{F}_7^3$ and $\mathbb{F}_{11}^3$}},
  howpublished = {Preprint (not peer reviewed), \url{https://github.com/alexbers/neuro-articles/tree/main/papers/round1/New-lower-bounds-for-line-free-sets-in-F7-3-and-F11-3-October-8-2026}},
  year = {2026}
}
```

## Verification status

- **Lean-certified** (Lean 4.34.1, core + Std only, no Mathlib, no `sorry`/`axiom`/`native_decide`;
  all finite checks by `decide +kernel`):
  - `lean/Main.lean`: `main : ∃ L : List (Fin 7 × Fin 7 × Fin 7), L.Nodup ∧ L.length = 227 ∧ LineFree L`
    (r_7(F_7^3) ≥ 227), and
    `main_pow (k) : ∃ M, M.Nodup ∧ M.length = 227 ^ k ∧ (∀ v ∈ M, v.length = 3 * k) ∧ LineFreeN (3 * k) M`
    (r_7(F_7^{3k}) ≥ 227^k for all k).
  - `lean/Main11.lean`: the same with 11 and 1010 (r_11(F_11^3) ≥ 1010).
  - `#print axioms` for `main` and `main_pow` (both files): `[propext, Classical.choice, Quot.sound]`
    (outputs in `lean/lean_output.txt` and `lean/lean_output11.txt`).
- **Paper-only:** existence of the limit α_7 = lim r_7(F_7^n)^{1/n} (Fekete's lemma), hence
  α_7 ≥ 227^{1/3} ≈ 6.1002. This is *not* a record: Führer–Taranchuk (arXiv:2403.18611, Thm 1.1)
  give α_7 ≥ 7^{20/21} ≈ 6.3805, which no three-dimensional set can reach. Also paper-only: the
  comparison with the literature (previous records 225 and 1005 for p = 7, 11 from
  arXiv:2310.03382 = Period. Math. Hungar. 90 (2025) 7–21; see also Kovács, arXiv:2605.23437;
  for p = 13 the cone over a 38-point double blocking set of PG(2,13) gives 1740 > 1734), stated
  as "to our knowledge as of October 8, 2026". The search statistics and the negative search results for
  p = 5, 7, 11, 13 are reported for documentation only and are not theorems.
- **Data:** `data/linefree_F7_227.txt` and `data/linefree_F11_1010.txt` (point index
  x + p·y + p²·z), the `*_xyz.txt` coordinate lists, `data/SHA256SUMS`, and the independent
  checker `data/verify.py`. `data/cone13_1740.py` builds and checks the 1740-point line-free set
  in F_13^3 obtained as the complement of a cone over the 38-point double blocking set of PG(2,13)
  (Csajbók–Héger 2019, Sect. 4.1); output in `data/linefree_F13_1740_cone.txt`.
- **Reproduce:**
  - `lean lean/Main.lean` (Lean 4.34.1, core only, no project/Mathlib needed; ≈ 115–140 s, 2.2 GB).
  - `lean lean/Main11.lean` (≈ 430–550 s, 1 GB). Expected output: the two `#print axioms` lines
    in `lean/lean_output.txt` / `lean/lean_output11.txt` (the `leanchk:` timing line there was
    added by a wrapper script).
  - `python3 data/verify.py 7 3 data/linefree_F7_227.txt` and
    `python3 data/verify.py 11 3 data/linefree_F11_1010.txt`; the expected result is
    "full lines 0".
  - `lean/NegTest.lean` (`#eval` only) is a negative control: the checker rejects the set plus a
    line, and the set plus any single missing point.
- **Build:** `cd build && pdflatex main.tex` (twice). On this machine the pdflatex format and the
  font maps had to be generated in a temporary folder inside `build/`; that folder was deleted
  after building.
