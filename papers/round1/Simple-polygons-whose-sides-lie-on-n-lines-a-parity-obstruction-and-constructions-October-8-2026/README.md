# [Simple polygons whose sides lie on n lines: a parity obstruction and constructions](paper.pdf)

**Author:** Claude (AI model by Anthropic); run and submitted by Aleksandr Bersenev

*Produced autonomously by Claude (Opus 5.5) agents in Claude Code. Not an official Anthropic publication. Not peer reviewed.*

**Date:** October 8, 2026

## Citation

```bibtex
@misc{Claude:Simple-polygons-whose-sides-lie-on-n-lines-a-parity-obstruction-and-constructions-October-8-2026,
  author = {Claude and Bersenev, Aleksandr},
  note = {Claude: AI model by Anthropic; produced autonomously; run and submitted by A. Bersenev; not an official Anthropic publication},
  title = {{Simple polygons whose sides lie on n lines: a parity obstruction and constructions}},
  howpublished = {Claude research preprint (unpublished, not peer reviewed)},
  year = {2026}
}
```

Source of the problem: MathOverflow question 513798 by Johnathan Will
(https://mathoverflow.net/questions/513798, https://mathoverflow.net/users/596423). The 24-gon on
8 lines and the remark that 18 sides are reachable with 7 lines are from comments by DSM
(https://mathoverflow.net/users/12613).

## Results

Let M(n) be the largest number of sides of a simple polygon whose sides lie on n lines; trivially
M(n) ≤ n⌊(n−1)/2⌋. For odd n = 2r+1:

- **Parity theorem.** In every simple arrangement of n lines or pseudolines, the "alternating
  2-factor" G (on each line, join the 1st and 2nd, 3rd and 4th, … intersection points) has a number of
  components ≡ r(r+1)/2 = (n²−1)/8 (mod 2). The proof is elementary (a sweep argument plus an explicit
  potential function on permutations).
- **Reduction.** A simple C(n,2)-gon on n lines must be G itself (so G must be connected); any other
  simple polygon on n lines has at most C(n,2) − 3 sides.
- **Corollary.** M(n) ≤ C(n,2) − 3 for n ≡ ±1 (mod 8); in particular M(7) ≤ 18 and M(9) ≤ 33, so the
  conjectured equality fails for n = 7, 9, 15, 17, ….
- **Constructions.** M(7) = 18, M(9) = 33, M(11) = 55, M(13) = 78.

## Verification status

- **Lean-certified** (Lean 4.34.1, core only, no Mathlib, `decide +kernel`, no `sorry`/`native_decide`).
  These theorems in `lean/Main.lean` construct simple polygons whose sides lie on the given lines:

  | theorem | polygon |
  |---|---|
  | `mo513798_n7` | 18 sides on 7 lines |
  | `mo513798_n9` | 33 sides on 9 lines |
  | `mo513798_n11` | 55 sides on 11 lines (main) |
  | `mo513798_n13` | 78 sides on 13 lines |

  `#print axioms` gives `[propext]` for each of them (see `lean/lean_output.txt`).
- **Paper proof only, not formally verified:**
  - the reduction of a C(n,2)-gon to the alternating 2-factor;
  - the parity theorem (#components ≡ (n²−1)/8 mod 2);
  - the resulting upper bounds `M(n) ≤ C(n,2) − 3` for n ≡ ±1 (mod 8), including `M(7) ≤ 18` and
    `M(9) ≤ 33`.

  These are supported by exhaustive computation over all simple pseudoline arrangements (commutation
  classes of reduced words of the longest permutation) for n ≤ 9 — for n = 7 and n = 9 the graph G is
  never a single cycle — and by random tests up to n = 23. See `scripts/README.md`.
- **Reproduce:** `lean lean/Main.lean` (the file has no imports; about 50 s and 2 GB) prints the four
  `#print axioms` lines. `python3 scripts/verify_constructions.py` rechecks the four polygons in exact
  rational arithmetic without Lean. The certificate data (integer lines and the cyclic order of
  vertices) is in `data/polyN.json`.

## Review

An independent review (in Russian; proofs re-read, Lean re-run, all constructions and the exhaustive
computations for n ≤ 9 reproduced with separate code, literature checked) is in `REVIEW-2026-10-08.md`.
