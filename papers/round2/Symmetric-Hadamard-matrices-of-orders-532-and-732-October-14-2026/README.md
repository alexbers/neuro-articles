# [Symmetric Hadamard matrices of orders 532 and 732](paper.pdf)

**Author:** Claude (AI model by Anthropic); run and submitted by Aleksandr Bersenev

*Produced autonomously by Claude (Opus 5.5) agents in Claude Code. Not an official Anthropic publication. Not peer reviewed.*

**Date:** October 14, 2026

## Citation

```bibtex
@misc{Claude:Symmetric-Hadamard-matrices-of-orders-532-and-732-October-14-2026,
  author = {Claude and Bersenev, Aleksandr},
  note = {Claude: AI model by Anthropic; produced autonomously; run and submitted by A. Bersenev; not an official Anthropic publication},
  title = {{Symmetric Hadamard matrices of orders 532 and 732}},
  howpublished = {Preprint (not peer reviewed), \url{https://github.com/alexbers/neuro-articles/tree/main/papers/round2/Symmetric-Hadamard-matrices-of-orders-532-and-732-October-14-2026}},
  year = {2026}
}
```

## Verification status

- **Lean-certified** (`lean/Main.lean`, Lean 4.35.0 + Mathlib, full output in `lean/lean_output.txt`):
  - `Sym532.symmetric_hadamard_532 : ∃ H : Matrix (Fin 532) (Fin 532) ℤ, (∀ i j, H i j = 1 ∨ H i j = -1) ∧ H.transpose = H ∧ H * H.transpose = (532 : ℤ) • 1`
  - `Sym732.symmetric_hadamard_732` (same statement with 732).
  - `Propus.propus_mul_transpose`, `Propus.propus_transpose`, `Propus.propus_entries` (the propus construction for arbitrary v).
  - Axioms: `propext`, `Classical.choice`, `Quot.sound` only. The autocorrelation identities on ℤ/133 and ℤ/183
    are checked by `decide +kernel` (kernel evaluation; no `native_decide`). No `sorry`/`axiom`/`admit`.
    Node run: `leancheck: wall=170.99s maxrss=10746956kB exit=0`.
- **Independent numeric check:** `data/verify.py` rebuilds the matrices from the data files and checks
  H = Hᵀ, HHᵀ = 4v I exactly (all 72 families for v = 133, all 432 families for v = 183).
- **Paper-only / computational:** novelty (literature search), the counts of families, and all statements
  about v = 65 (exhaustive searches with the programs in the agent directory `attempts2/B03-hadamard/src`).
- **Reproduce:** `~/claude_math/bin/leancheck B03 lean/Main.lean` on the node, or
  `attempts2/bin/leanmath lean/Main.lean` locally (≈3–5 min, ≈11 GB RAM);
  `gcc -O3 -pthread -o gbig data/gbig.c -lm && ./gbig 133 61 64 57 1 22 0 26` (v = 133, seconds);
  `gcc -O3 -o cpq2 data/cpq2.c -lm && ./cpq2 183 3 61 34 81 91 83 20` (v = 183, ~7 min, ~7 GB).
