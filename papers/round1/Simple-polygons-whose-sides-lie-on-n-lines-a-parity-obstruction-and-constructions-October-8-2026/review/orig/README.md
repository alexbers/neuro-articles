# [Simple polygons whose sides lie on n lines: a parity obstruction and constructions](paper.pdf)

**Author:** Claude (Anthropic)

**Date:** October 8, 2026

## Citation

```bibtex
@misc{Claude:Simple-polygons-whose-sides-lie-on-n-lines-a-parity-obstruction-and-constructions-October-8-2026,
  author = {{Claude}},
  title = {{Simple polygons whose sides lie on n lines: a parity obstruction and constructions}},
  howpublished = {Claude research preprint (unpublished, not peer reviewed)},
  year = {2026}
}
```

Source of the problem: MathOverflow question 513798 by Johnathan Will
(https://mathoverflow.net/questions/513798, https://mathoverflow.net/users/596423). The 24-gon on
8 lines and the remark that 18 sides are reachable with 7 lines are from comments by DSM
(https://mathoverflow.net/users/12613).

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
  - the parity theorem (#components ≡ (n²−1)/8 mod 2; its proof uses the Matsumoto–Tits theorem);
  - the resulting upper bounds `M(n) ≤ C(n,2) − 3` for n ≡ ±1 (mod 8), including `M(7) ≤ 18` and
    `M(9) ≤ 33`.

  These are supported by exhaustive computation over all pseudoline arrangements for n ≤ 9, and by
  random tests up to n = 19.
- **Reproduce:** from `attempts/`, run `bin/leanchk papers/<this directory>/lean/Main.lean`; the
  check takes about 40–60 s and about 2 GB. The certificate data (integer lines and the cyclic order
  of vertices) is in `data/polyN.json`. The search and verification scripts are in
  `attempts/A09-polygon-lines/scripts/`.
