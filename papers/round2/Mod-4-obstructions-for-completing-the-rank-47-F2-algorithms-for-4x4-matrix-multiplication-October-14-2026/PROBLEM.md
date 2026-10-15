# PROBLEM (B01): integral (all-ring) schemes for small matrix-multiplication tensors

## TARGET
Lower a best-known rank of a small matrix multiplication tensor <n,m,p> (n,m,p <= 8), or match a record
with a scheme over a more general coefficient ring than previously known. Concretely, the attacked
instances (all open as of 14 Oct 2026, see STATUS):

1. <4,4,4>: is there a rank-48 scheme with **integer** coefficients (valid over every ring, incl. Z/2^k)?
   Known: 48 over Q (Dumas-Pernet-Sedoglavic 2025, needs 1/2), 47 over F2 (AlphaTensor 2022), 49 over Z.
2. <4,5,5>: rank 75 over Z or Q (record 76, AlphaTensor 2022). Over F2, rank 74 (Arai-Ichikawa-Hukushima
   2024; Kauers-Wood 2025) and 73 (Arai et al. data) are known, but those F2 schemes do not Hensel-lift.
3. <3,3,6>: rank <= 41 with integer coefficients (record over Z: 42, Kauers-Moosbauer 2023, who explicitly
   ask whether 42 is optimal in arbitrary characteristic; Smirnov's 40 needs 1/2).
4. <2,4,5>: rank 32 over Z (AlphaEvolve 2025 needs 1/2; 33 = Hopcroft-Kerr 1971 over Z).

## DEFINITIONS
<n,m,p> = trilinear form T = sum_{i,j,k} A_ij B_jk C_ik.  A scheme of rank r over a ring K is
u_t in K^{nm}, v_t in K^{mp}, w_t in K^{np} (t=1..r) with sum_t u_t (x) v_t (x) w_t = T (Brent equations),
i.e. C_ik = sum_t w_t[i,k] (sum u_t[i',j] A_i'j)(sum v_t[j',k'] B_j'k') for all A,B (non-commutative).
"Over Z" = all coefficients integers: valid in every (possibly non-commutative) ring.

## STATUS AND SOURCES (checked 14 Oct 2026)
- FMM catalogue (https://fmm.univ-lille.fr/, front page): <4,4,4>:48 (DPS 2025, Q), <4,5,5>:76,
  <3,3,6>:40 (Smirnov 2013, Q), <2,4,5>:32 (AlphaEvolve 2025).
- Perminov, FastMatrixMultiplication (github, pushed 13 Oct 2026) status table: ZT/Z/Q ranks
  4x4x4: 49/49/48, 4x5x5: 76/76/76, 3x3x6: 42/42/40, 2x4x5: 33/33/32.
- Kauers-Moosbauer, arXiv:2306.00882: "(3,3,6) ... rank 40 is due to Smirnov and has coefficients in Z[1/2]
  ... We do not know whether our bound 42 is best-possible among all schemes that apply to arbitrary
  characteristic."
- Kauers-Wood, arXiv:2505.05896: "(4,5,5): we only found schemes of rank 74 over Z2 which cannot be lifted ...
  none of the schemes of rank 75 ... can be lifted, but some of rank 76 can."
- Dumas-Pernet-Sedoglavic arXiv:2506.13242, 2603.18699, 2609.12027: all rank-48 <4,4,4> schemes need 1/2.
- Cloudroom-math (github, 8 Oct 2026): AlphaTensor/KM F2 47s do not lift; Z/4 flip graphs did not reach 48.

## RESEARCH DIRECTION
(a) 2-adic gauge (Bruhat-Tits building) search: make a Q-scheme with 2-power denominators integral by a
    sandwich change of basis in GL(Z[1/2]); then "core" re-decomposition of the remaining non-integral terms.
(b) Defect lifting: an F2 scheme of rank r that does not Hensel-lift may still be the reduction of a 2-adic
    scheme of rank r+e having e terms divisible by 2. The first lifting step becomes a small nonlinear
    problem (rank-e tensor in an affine subspace) solvable by SAT with XOR clauses; later steps are linear.
(c) Symmetric (C3) flip graphs, F2/ZT flip graphs with pools, subset re-decomposition by SAT.

## PITFALLS
- F2 schemes that do not lift are common; Q-schemes found numerically often need 1/2 intrinsically.
- A 2-adic solution is not a rational one: final schemes must be verified exactly over Z or Q.
- Records must be compared with the live catalogue and Perminov's table (both change weekly).

## CERTIFICATE
Explicit scheme; Lean 4 file checking all Brent equations as an exact integer identity by kernel
computation (`decide`), with the main theorem stated as the polynomial identity for C = A*B.
