# PROBLEM (B07): Heilbronn's triangle problem — best configurations for small n

## TARGET
Find, for some n ≤ 36 and some container K ∈ {unit square, triangle, convex region}, an explicit set of
n points whose smallest triangle is strictly larger than the best value currently known
(tables at https://math.tejstead.com/heilbronn, state of 2026-10-14 04:55 +05), and certify the
value in Lean 4 with exact rational arithmetic.

## DEFINITIONS
For a finite point set S ⊂ ℝ², let m(S) = min{area(abc) : a, b, c ∈ S distinct}.
* Square: H□(n) = sup{ m(S) : S ⊂ [0,1]², |S| = n }.
* Triangle: H△(n) = sup{ m(S)/area(T) : S ⊂ T, |S| = n } for a triangle T (affine invariant; we use
  T = conv{(0,0),(1,0),(0,1)}, so the normalised value is 2·m(S)).
* Convex: H◇(n) = sup{ m(S)/area(conv S) : |S| = n } (equivalently: the best convex container of area 1).
A "record" is a configuration S with normalised value strictly above the current table entry.

## STATUS AND SOURCES (checked 2026-10-14)
* Heilbronn (c. 1950); Goldberg 1972 (square configurations), Comellas–Yebra 2002 (SA, n ≤ 16),
  Yang–Zhang–Zeng, Dress–Yang–Zeng, Chen–Zeng (optimality for n ≤ 7/8 in several containers),
  E. Friedman's Packing Center tables (offline 2026), continued by T. Stead's site
  https://math.tejstead.com/heilbronn (n = 3…36, exact rational verifier, Atom feed of records).
* AlphaEvolve (2025) benchmark entries: triangle n = 11 (0.03653), convex n = 13 (0.03094), n = 14 (0.02784);
  Georgiev–Gómez-Serrano–Tao–Wagner, "Mathematical exploration and discovery at scale", arXiv:2511.02864.
* Very active in 2026: records for n = 17…36 were improved repeatedly in July–October 2026 by
  N. Sudermann-Merx, T. Stead, R. Chappell, Fable 5.1 (with S. Zhang), Claude Opus 5.5 (with M. Jan),
  C. Nemri (AlphaEvolve), R. Gardiner, M.-E. Coupvent des Graviers, I. Choi; latest record 2026-10-13
  (triangle n = 23). Optimality is proved only for small n (square n ≤ 9, triangle n ≤ 8, convex n ≤ 8 partly).
* OpenAI's release (CONTENTS.md item 191) concerns the asymptotic Heilbronn problem (n^{-2+c} lower bound),
  not small-n configurations. Not attempted in our round 1.

## RESEARCH DIRECTION
* Max–min structure: at a local optimum about 2n triangles tie; locally the problem is an LP in the
  displacements (orientations fixed) → trust-region sequential LP ("SLP") polishing.
* Global moves: ruin-and-recreate (remove k points, reinsert at maximal "holes"), shakes, soft-min
  (log-sum-exp) L-BFGS, vertical seeding from the n±1, n±2 records, symmetric orbit parametrisations
  (Cₖ, Dₖ subgroups of the container's symmetry group).
* Prioritise entries that look weak relative to neighbours (n²·H(n) trend).

## PITFALLS
* The tables move daily; re-check the live values immediately before claiming anything.
* Floating-point ties: the certificate must use the exact decimal literals (rounded toward the interior
  for the square/triangle constraints).
* Convex variant: the value must be normalised by the area of the convex hull of the points (not by an
  arbitrary container); the certificate must exhibit the hull and prove it contains all points.
* A configuration that merely re-finds the record basin (even with more digits) is not a new record.

## CERTIFICATE
Core Lean 4 file: explicit list of rational points, the domain constraints, and
∀ a b c, [a,b,c] <+ config → bound ≤ (normalised) area a b c, all checked by `decide +kernel`
through a Boolean checker with a proved soundness lemma; `#print axioms`.
