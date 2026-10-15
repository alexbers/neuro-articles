# [An explicit 6-regular graph of girth 9 on 4368 vertices](paper.pdf)

**Author:** Claude (AI model by Anthropic); run and submitted by Aleksandr Bersenev

*Produced autonomously by Claude (Opus 5.5) agents in Claude Code. Not an official Anthropic publication. Not peer reviewed.*

**Date:** October 8, 2026

## Citation

```bibtex
@misc{Claude:An-explicit-6-regular-graph-of-girth-9-on-4368-vertices-October-8-2026,
  author = {Claude and Bersenev, Aleksandr},
  note = {Claude: AI model by Anthropic; produced autonomously; run and submitted by A. Bersenev; not an official Anthropic publication},
  title = {{An explicit 6-regular graph of girth 9 on 4368 vertices}},
  howpublished = {Claude research preprint (unpublished, not peer reviewed)},
  year = {2026}
}
```

## Verification status

**Lean-certified.** `lean/Main.lean` uses Lean 4.34.1, core library only, no Mathlib and no
`native_decide`. Its main theorem is `Cage.main`:

```lean
theorem main : ∃ adj : Fin 4368 → Fin 4368 → Bool,
    IsSimpleGraph adj ∧ IsRegular adj 6 ∧ HasGirth adj 9
```

`HasGirth adj 9` means a 9-cycle exists and every cycle has length ≥ 9. All definitions are in
Part A of the file. The supporting results are:
* the generic soundness lemma `no_short_cycle`;
* the matrix associativity lemma `mmul_assoc`;
* the kernel checks `dartsOK_ok`, `cc_0`–`cc_25`, `root_0`, `root_1` and `witnessV_isCycle`
  (all by `decide +kernel`).

Axioms (`lean/lean_output.txt`): `'Cage.main' depends on axioms: [propext, Classical.choice, Quot.sound]`.
The check takes 153.6 s wall time and peaks at 0.99 GB.

**Paper-only (not formalized):**
* the literature status, i.e. that the (6,9) cell of the cage tables was empty, to our knowledge as of
  2026-10-08 (explicit but much larger (6,9)-graphs follow from general constructions, e.g. Sauer's bound
  32768 and the Lubotzky–Phillips–Sarnak graph X^{5,29} on 12180 vertices);
* the implicit prior bound n(6,9) ≤ n(6,11) ≤ 7783, via Erdős–Sachs monotonicity and
  Exoo–Goedgebeur–Jooken–Stubbe–Van den Eede;
* the lower bound 938;
* connectivity and diameter 7;
* the girth-10 double cover on 8736 vertices;
* the description of the search and of the failed (6,10) attempts.

**Reproduce:**
* Lean: in `lean/`, run `lean Main.lean` with Lean 4.34.1 (toolchain `leanprover/lean4:v4.34.1`, core library
  only, no project or Mathlib needed). The expected output is the first line of `lean/lean_output.txt`.
  Independent re-check (2026-10-08, same toolchain): exit code 0, 109 s wall time, 0.99 GB peak RSS.
* Independent Python check, BFS from every vertex: in `data/`, run
  `python3 verify_lift.py S 13 voltages_SL2_13.txt`. Expected output is in `verify_lift_output.txt`.
* Data: `data/voltages_SL2_13.txt` (edge voltages as matrices `a b c d`) and `data/base_graph.txt`.
