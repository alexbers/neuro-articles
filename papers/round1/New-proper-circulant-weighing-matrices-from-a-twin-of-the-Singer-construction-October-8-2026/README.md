# [New proper circulant weighing matrices from a twin of the Singer construction](paper.pdf)

**Author:** Claude (AI model by Anthropic); run and submitted by Aleksandr Bersenev

*Produced autonomously by Claude (Opus 5.5) agents in Claude Code. Not an official Anthropic publication. Not peer reviewed.*

**Date:** October 8, 2026

## Citation

```bibtex
@misc{Claude:New-proper-circulant-weighing-matrices-from-a-twin-of-the-Singer-construction-October-8-2026,
  author = {Claude and Bersenev, Aleksandr},
  note = {Claude: AI model by Anthropic; produced autonomously; run and submitted by A. Bersenev; not an official Anthropic publication},
  title = {{New proper circulant weighing matrices from a twin of the Singer construction}},
  howpublished = {Claude research preprint (unpublished, not peer reviewed)},
  year = {2026}
}
```

## Verification status

- **Lean-certified** (`lean/Main.lean`, Lean 4.34.1, core only, no Mathlib, `decide +kernel`):
  - `new_proper_circulant_weighing_matrices : MainStatement` — proper `CW(146,8²)`, `CW(266,11²)`,
    `CW(366,13²)`, `CW(504,12²)`, `CW(614,17²)`, `CW(762,19²)` exist (explicit witnesses).
  - `twin_singer_family_members` — the eight explicit twin-construction rows for
    q = 3, 5, 7, 9, 11, 13, 17, 19.
  - general lemma `paf_eq_pafIdx` (fast rotation-based autocorrelation = index-form definition).
  - `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound` (the `_proper` theorems only
    `propext`); no `sorryAx`, no `native_decide`. Full output in `lean/lean_output.txt`
    (491 s wall time, 2.1 GB maximum memory). Re-checked independently on October 8, 2026 with a
    fresh Lean 4.34.1 install: exit 0, 273 s, 2.0 GB, identical output.
- **Paper-only (proved in the text):** the doubling lemma, the same-support corollary with its
  properness criterion, the product lemma, the classical `W_0` being a CW, and the Fourier
  reformulation of the twin conjecture.
- **Computational evidence only (not proved):** the twin conjecture, and hence a proper
  `CW(2(q²+q+1), q²)` for every odd prime power q. It was checked for all 37 odd prime powers
  q ≤ 127 (`data/twin_family_check_q_le_127.log`) and, with an independent implementation written
  during the review of October 8, 2026 (`data/twin_check_gf.py`), for all 62 odd prime powers
  q ≤ 251 (`data/twin_family_check_q_le_251.log`). The search statistics in §5 are also
  computational only.
- **Novelty:** to our knowledge, as of October 8, 2026, measured against Gordon's repository and
  table (arXiv:2501.14924; site updated 2026-09-03), Arasu–Gordon–Zhang and Tan 2026. Krengel
  (SETA 2004) could not be checked.
- **Reproduce:** with Lean 4.34.1 installed (for example through `elan`), run `lean lean/Main.lean`
  from this directory; the expected output is `lean/lean_output.txt`. Independent data check:
  `python3 data/verify_certificates.py data/certificates.json`. Rebuild the twin rows from the
  definition: `cd data && python3 twin_singer.py certificates.json`.
- The full working directory (searches, scripts, logs) was `attempts/A15-cw-proper/`; it is not part
  of this package.
