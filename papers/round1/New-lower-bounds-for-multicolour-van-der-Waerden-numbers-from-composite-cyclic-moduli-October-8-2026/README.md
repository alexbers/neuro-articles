# [New lower bounds for multicolour van der Waerden numbers from composite cyclic moduli](paper.pdf)

**Author:** Claude (AI model by Anthropic); run and submitted by Aleksandr Bersenev

*Produced autonomously by Claude (Opus 5.5) agents in Claude Code. Not an official Anthropic publication. Not peer reviewed.*

**Date:** October 8, 2026

## Citation

```bibtex
@misc{Claude:New-lower-bounds-for-multicolour-van-der-Waerden-numbers-from-composite-cyclic-moduli-October-8-2026,
  author = {Claude and Bersenev, Aleksandr},
  note = {Claude: AI model by Anthropic; produced autonomously; run and submitted by A. Bersenev; not an official Anthropic publication},
  title = {{New lower bounds for multicolour van der Waerden numbers from composite cyclic moduli}},
  howpublished = {Claude research preprint (unpublished, not peer reviewed)},
  year = {2026}
}
```

## Verification status

**Lean-certified.** The file `lean/Main.lean` (Lean 4.34.1, core only, no Mathlib) proves 15
new lower bounds `VdWGt r k N`, meaning W(r,k) > N:

- `W4_6`, `W5_6`, `W6_6`
- `W4_8`, `W5_8`, `W6_8`
- `W4_9`, `W5_9`, `W6_9`
- `W5_10`, `W6_10`
- `W4_11`, `W5_11`, `W6_11`
- `W4_12`

It also certifies the known bounds `W2_6`–`W2_12` and `W4_10`.

Every theorem prints `[propext, Classical.choice, Quot.sound]`. There is no `sorryAx` and no
`native_decide`.

**Run.** `nice -n 10 lean -j1 Main.lean` finished with no errors or warnings in 2310 s wall time,
with peak RSS 3.6 GB; see `lean/lean_output.txt` (the paths `./runmon.sh` and
`attempts/toolchain/...` mentioned in that log belong to the authors' environment and are not part
of this directory). The authors' guarded wrapper script (`leanchk`, not included) could not be
used: under its `ulimit -v 16000000`, Lean aborted at start-up with "failed to create thread"; see
`lean/leanchk_attempt.txt`.

**Independent re-check (review, October 8, 2026).** `lean Main.lean` with Lean 4.34.1 (core only)
on the same file (sha256 `20251d5c…f4f`) reproduced `lean/lean_output.txt` verbatim: exit status 0, 1237 s wall time, peak RSS 3.5 GiB.
Log: `lean/lean_output_review.txt`.

**Paper-only.** Two things are not machine-checked:

- The novelty claim: "to our knowledge, as of October 8, 2026", based on the Wikipedia table and
  on Monroe, arXiv:1603.03301 and JCMCC 2025.
- The attribution of the cyclic certificates to their original authors.

**Data.** The cyclic colourings are in `data/`, with SHA-256 hashes in `data/SHA256SUMS`. The
original certificate files from Heule's repository are in `data/heule_certs/`.

**Reproduce.**

- Rerun the Lean check with `lean -j1 lean/Main.lean` (Lean 4.34.1, no Mathlib, no lakefile
  needed; about 40 min and 3.6 GB with `-j1`).
- The generator script for `Main.lean` and the C cross-check programs mentioned in the paper are
  not included in this directory; `lean/Main.lean` is self-contained and is the certificate. The
  cyclic colourings in `data/` can be checked independently with a few lines of code (one digit
  per element of Z/n; see Section 4 of the paper for the constructions).
