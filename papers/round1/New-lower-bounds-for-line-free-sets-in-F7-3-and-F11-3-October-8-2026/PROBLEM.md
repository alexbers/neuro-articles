# PROBLEM (A10): large line-free sets in F_7^3 (and other small F_p^3)

## TARGET
Improve the best known lower bound for r_7(F_7^3), the largest size of a subset of
F_7^3 = (Z/7Z)^3 that contains no full affine line, by exhibiting an explicit larger set
(current record 225, Elsholtz, Führer, Füredi, Kovács, Pach, Simon, Velich 2023/2024).
Secondary targets: r_5(F_5^3) >= 70 (upper bound 73), and r_11(F_11^3) >= 1005,
r_13(F_13^3) >= 1734, which come from the general constructions (Thm 1.1 / Thm 1.7:
(p-1)^3 + (p-1)/2 for n = 3) of the same paper, with no computer search reported.

## DEFINITIONS
- For a prime p, F_p^n is the n-dimensional vector space over Z/pZ.
- An affine line is a set {a + t·d : t in F_p} with a, d in F_p^n and d != 0. It has
  exactly p points. Equivalently it is a p-term arithmetic progression
  a, a+d, ..., a+(p-1)d with nonzero common difference (in F_p^n every nontrivial
  p-term progression is a full line and vice versa).
- S ⊆ F_p^n is line-free (p-progression-free) if it contains no affine line.
- r_k(F_p^n) is the maximum size of a subset of F_p^n with no k-term progression with
  nonzero difference; for k = p this is the maximum size of a line-free set.
- alpha_p = lim_n r_p(F_p^n)^{1/n}; any line-free S ⊆ F_p^m gives alpha_p >= |S|^{1/m}
  (product construction).
- Complement view: B = F_p^3 \ S is a 2-blocking set of AG(3,p) (meets every line);
  a_2(3,p) = p^3 - r_p(F_p^3).

## STATUS AND SOURCES (checked 2026-10-08)
- C. Elsholtz, J. Führer, E. Füredi, B. Kovács, P. P. Pach, D. G. Simon, N. Velich,
  "Maximal line-free sets in F_p^n", arXiv:2310.03382 (v1 Oct 2023, v2 May 2024):
  r_7(F_7^3) >= 225 (algebraic construction, Thm 1.2 + special case p=7) and
  r_7(F_7^3) < 243 (Thm 1.6); r_5(F_5^3) >= 70 (branch and cut) and r_5(F_5^3) < 74
  (Thm 1.5); general p: (p-1)^3 + p - 2 sqrt(p) <= r_p(F_p^3) <= p^3 - 2p^2 - (sqrt2-1)p + 2.
  They deduce alpha_5 >= 4.121 and alpha_7 >= 6.082 from the 3-dimensional sets
  (Table 1: other constructions give only 4.090 and 6.066).
- B. Kovács, "A superlinear improvement on line-free sets in F_p^3", arXiv:2605.23437
  (May 2026, rev. Sep 2026): (p-1)^3 + p^{3/2}/8 - O(p); explicitly says "there have
  been no further improvements from either side" of Theorem 1.1; his construction is only
  better than the hypercube for p >= 17, so it does not touch p = 5, 7, 11, 13.
- Führer–Taranchuk, arXiv:2403.18611 (rev. Feb 2026) concerns asymptotic line-evasive sets;
  no small-p values. No 2024–2026 paper found that improves r_7(F_7^3) >= 225.
- Not in OpenAI's 2026 release (CONTENTS.md has nothing on line-free sets / cap sets).

## RESEARCH DIRECTION
Local search (tabu swap search with many short restarts) on the 5-uniform/7-uniform
"line hypergraph" of AG(3,p): minimize the number of fully contained lines among
k-subsets, increase k. Analyse plane distributions and automorphisms of the sets found;
try symmetric (orbit) searches and seeding from the algebraic 225-point set.
Certify the final set by an exhaustive line check in Lean (`decide +kernel`).

## PITFALLS
- Only lines with nonzero direction count; every one of the p^2(p^2+p+1) lines must be
  checked (all base points and all nonzero directions, not just normalized directions,
  unless the reduction is proved).
- "Distinct points" must be part of the statement (List.Nodup), otherwise duplicates
  could inflate the length.
- Arithmetic must be modulo p (Fin 7 arithmetic in Lean is modulo 7; check this).
- A lower bound by construction does not determine r_7(F_7^3); do not claim the exact value.
- Do not confuse k-term progressions for k < p (not lines) with lines.
- Asymptotic consequences (alpha_7) rely on the standard product construction, which is
  not formalised here; state them as corollaries of the literature, not as Lean results.

## CERTIFICATE
An explicit list of 226 (or more) points of F_7^3 (Main.lean, also `set_*.txt`), with a
Lean 4 proof (core only) of
`∃ L : List (Fin 7 × Fin 7 × Fin 7), L.Nodup ∧ L.length = N ∧
   ∀ a d, d ≠ (0,0,0) → ∃ t : Fin 7, a + t•d ∉ L`,
checked by `decide +kernel` (no `native_decide`), plus an independent Python check.
