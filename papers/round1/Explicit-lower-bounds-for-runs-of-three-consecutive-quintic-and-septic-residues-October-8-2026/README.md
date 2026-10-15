# [Explicit lower bounds for runs of three consecutive quintic and septic residues](paper.pdf)

**Author:** Claude (AI model by Anthropic); run and submitted by Aleksandr Bersenev

*Produced autonomously by Claude (Opus 5.5) agents in Claude Code. Not an official Anthropic publication. Not peer reviewed.*

**Date:** October 8, 2026

## Citation

```bibtex
@misc{Claude:Explicit-lower-bounds-for-runs-of-three-consecutive-quintic-and-septic-residues-October-8-2026,
  author = {Claude and Bersenev, Aleksandr},
  note = {Claude: AI model by Anthropic; produced autonomously; run and submitted by A. Bersenev; not an official Anthropic publication},
  title = {{Explicit lower bounds for runs of three consecutive quintic and septic residues}},
  howpublished = {Claude research preprint (unpublished, not peer reviewed)},
  year = {2026}
}
```

Problem: Erdős Problem #436 (https://www.erdosproblems.com/436), after D. H. Lehmer and E. Lehmer
(Proc. AMS 13, 1962). Λ(k,3) = limsup over primes p of the least r such that r, r+1, r+2 are k-th power
residues mod p. Λ(3,3) = 23532 (Lehmer–Lehmer–Mills–Selfridge, Math. Comp. 16, 1962). Whether Λ(k,3)
is finite for odd k ≥ 5 is open.

## Results

The prime assignments are g₅ (values mod 5) and g₇ (values mod 7); both send every prime to 1 except:
- g₅: 2, 5, 7, 11, 13, 17, 23, 31, 73, 1373, 2053, 2621, 4523 ↦ 0; 347, 409, 617, 1033, 2089, 2099,
  2437, 3907, 7057, 12917 ↦ 2; 21407, 49613 ↦ 3;
- g₇: 2, 47, 163 ↦ 0.

From these:
- **Λ(5,3) ≥ 99 999 999 and Λ(7,3) ≥ 9 999 999.** This combines the Lean-certified core with the
  Kummer–Chebotarev realisability lemma, which is proved in the paper.
- **Λ(5,3) ≥ 313 714 024 and Λ(7,3) ≥ 180 317 500.** These are computational only: the first zero triples
  of the two assignments, verified by two independent C programs.

Previously only trivial bounds were available: every run of three residues starts with a pair, so
Λ(5,3) ≥ Λ(5,2) = 7888 and Λ(7,3) ≥ Λ(7,2) = 1 649 375 (and Λ(k,3) ≥ Λ(k,2) > 5^k for odd k ≥ 5,
Brillhart–Lehmer–Lehmer 1964). To our knowledge, as of October 8, 2026, these are the first bounds on
Λ(5,3) and Λ(7,3) that go beyond those trivial consequences of the pair results.
**Finiteness of Λ(5,3) and Λ(7,3) remains open.**

## Verification status

- **Lean-certified** (Lean 4.34.1, core only, no Mathlib, no `sorry`):
  - `no_three_consecutive_quintic_residues` in `lean/Main.lean`, with L = 10^8. Any f that is completely
    additive mod 5 on [1, L] and agrees with g₅ on the primes has no r with r+2 ≤ L and
    f(r) ≡ f(r+1) ≡ f(r+2) ≡ 0.
  - `no_three_consecutive_septic_residues` in `lean/Main7.lean`: the same for mod 7, g₇ and L = 10^7.
  - `#print axioms` for both: `[propext, Classical.choice, Quot.sound,
    bigCheck_true._native.native_decide.ax_1_1]`.
  - **`native_decide` is used once per file**, for the closed Boolean `bigCheck`. That term sieves a table
    of L+1 bytes and checks it: complete additivity on prime-gated pairs, agreement with g on primes, and
    no zero triple.
  - All reasoning from `bigCheck = true` to the theorem is kernel-checked. The trusted base is therefore
    the Lean kernel *plus* the compiler/IR interpreter invoked by `native_decide` (`Lean.ofReduceBool`);
    the two C checkers in `scripts/` independently confirm the same table-level facts.
  - The runs are in `lean/lean_output*.txt`:
    - `Main.lean`: 4940 s wall, 725 MB (authors' run: plain `lean Main.lean` under a timing/memory
      wrapper).
    - `Main7.lean`: 165 s, 540 MB (same, with `-j 2`).
    - Independent re-check by the reviewer (October 8, 2026, Lean 4.34.1 core, plain `lean` from
      `lean/`, shared 14-core machine): `Main7.lean` exit 0, 288 s, 530 MB; `Main.lean` exit 0, 3727 s (1 h 02 min), 715 MB;
      `NegOpt.lean` exit 1 (`native_decide` reports `bigCheck = true` is false, as intended; 1.8 s); `PosOpt.lean` exit 0 (1.6 s). `#print axioms` output identical to
      `lean/lean_output*.txt`. Details in `REVIEW-2026-10-08.md`.
  - Controls in `lean/NegOpt.lean` and `lean/PosOpt.lean`: with g ≡ 1 the check is false at L = 15500
    and true at L = 15469.
- **Paper proof only, not formalised:**
  - the realisability lemma (Kummer theory over ℚ(ζ_k), with the independence and degree argument, plus
    Chebotarev) — a classical statement (Lehmer–Lehmer 1962, Lemma p. 104; Mills, *Characters with
    preassigned values*, 1963; Graham 1964), reproved here;
  - the passage from the Lean statement to Λ.
- **Computational only:**
  - the first zero triples 313 714 024 and 180 317 500 (`scripts/vchk.c` and `scripts/segchk.c`);
  - the local and exact searches (`scripts/ws2.c`, `scripts/lam.c`); note that the symmetry reduction
    in `lam.c` (first non-zero prime value may be taken to be 1) is complete only for prime k, so its
    UNSAT verdicts for k = 4 are plausibility checks, not proofs;
  - the side data (Λ(11,2) ≥ 6 082 047, Λ(13,2) ≥ 10^8 from the Ω-assignment; both are weaker than
    Λ(k,2) > 5^k of Brillhart–Lehmer–Lehmer 1964).
- **Reproduce:**
  - `cd lean && lean Main.lean` (about 82 min and 0.7 GB; `lean Main7.lean` takes 3–5 min). No
    `lakefile` or Mathlib is needed.
  - `cd scripts && ./reproduce.sh` for the C computations. The data is in `data/assignment_k*.txt`.
  - Building the PDF needed a pdflatex format: it was generated with `fmtutil-user`/`updmap-user`, with
    TEXMFVAR and TEXMFCONFIG pointing into a temporary folder inside `build/`. That folder was removed
    afterwards.
