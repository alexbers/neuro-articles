# PROBLEM (B02): small classical hypergraph Ramsey numbers (DS1 §7.1)

## TARGET
Improve the lower bounds of the classical hypergraph Ramsey numbers listed in Radziszowski's survey,
§7.1: R(4,5;3) ≥ 35 (the smallest open case), R(5,5;3) ≥ 88, R(4,6;3) ≥ 63, R(4,4,4;3) ≥ 79,
R(5,5;4) ≥ 35, and the recurrence-based R(5,6;4) ≥ 67: find, for n at or above the bound, a red/blue
colouring of the r-subsets of an n-set with no red K_k^(r) and no blue K_l^(r) (proving R(k,l;r) ≥ n+1).
(Exact-value side target: R(K₄−t, K₅; 3) ∈ {14,15,16}.)
(Original assignment: two-colour Table Ia; see README §6 for that part.)

## DEFINITIONS
- R(k,l;3) is the least n such that every 2-colouring of the triples of an n-set contains a red K_k^(3)
  (k points, all C(k,3) triples red) or a blue K_l^(3). R(k,l,m;3) is the 3-colour analogue.
- K₄−t is the 3-graph with 4 vertices and 3 triples.
- A colouring of the triples of GF(q) (or Z_n) is G-invariant for a permutation group G if the colour of
  {x,y,z} equals the colour of {g x, g y, g z} for every g ∈ G. We use the affine groups
  G(q,k) = { x ↦ a x + b : b ∈ GF(q), a ∈ C_k } where C_k is the subgroup of order k of GF(q)^*.

## STATUS AND SOURCES (as of 2026-10-14)
- Radziszowski, *Small Ramsey Numbers*, Electron. J. Combin. Dynamic Survey DS1, revision #18
  (2026-04-24), §7.1(a): 35 ≤ R(4,5;3) [Dyb2], 63 ≤ R(4,6;3) [Dyb3], **88 ≤ R(5,5;3) [Dyb3]**,
  79 ≤ R(4,4,4;3) [Dyb3], 35 ≤ R(5,5;4) [Ex24]; 7.1(b): 14 ≤ R(K₄−t,K₅;3) ≤ 16 [Ex1][LidP].
  The bounds [Dyb3] (J. Dybizbański, 2018, addendum at https://inf.ug.edu.pl/ramsey) come from
  cyclic (shift-invariant) colourings found by SAT; before that R(5,5;3) ≥ 82 [BudHR1].
- GitHub project SeverinVisionary/hypergraph-ramsey-bounds (2026, unrefereed): R(4,4,4;3) ≥ 84,
  R(4,6;3) ≥ 64, R(5,5;4) ≥ 36 by group-invariant SAT; for R(5,5;3) its CELLS.md lists only n = 88
  (3 classes UNSAT, 12 timeouts); issue #3 (2026-09-14/16, self-reported, not reviewed) claims an
  n = 88 witness, i.e. R(5,5;3) ≥ 89.
- No published or posted bound R(5,5;3) ≥ 90 was found (web search 2026-10-14).

## RESEARCH DIRECTION
Cyclic colourings were exhausted/timed out around n ≈ 88. Imposing a larger symmetry group — the
affine group G(q,k) for a prime power q — reduces the number of SAT variables to the number of
G-orbits on triples (≈ q²/(6k)) and of clauses to the 5-sets through a fixed point, so much larger
q become feasible. Sweep q ≥ 89 and divisors k of q−1 from large (very symmetric, quick) to small.

## PITFALLS
- The SAT encoding must use all 5-sets through a fixed vertex (enough only because G is transitive).
- Verify every witness independently of the generator (full check or translation-invariance + all
  5-sets through 0), and in Lean.
- Check the 2026 non-survey literature (GitHub/arXiv) before claiming novelty.
- R(K₄−t,K₅;3): local search strongly suggests 14, but an UNSAT proof needs symmetry breaking; do not
  claim it without a proof.

## CERTIFICATE
An explicit colouring: `col x y z := testBit Fmask ((y-x)*89 + (z-x))` for x<y<z<89 (translation
invariant on Z_89), checked by the Lean kernel (`decide +kernel`) on all 5-sets containing 0, plus a
Lean proof that translation reduces every 5-set to one containing 0.
