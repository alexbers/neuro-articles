# PROBLEM (B03): a symmetric Hadamard matrix of order 260

## TARGET
Construct a symmetric Hadamard matrix of order 260 = 4·65 (H = Hᵀ, H·Hᵀ = 260·I, entries ±1),
or, failing that, make certified structural progress on the only known route to it
(cyclic propus difference families in Z_65).

## DEFINITIONS
* Hadamard matrix of order n: n×n matrix with entries ±1 and H·Hᵀ = n·I. Symmetric: H = Hᵀ.
* For a ±1 sequence x of length v, PAF_x(s) = Σ_{i∈Z_v} x_i x_{i+s}.
* Goethals–Seidel (GS) difference family: subsets X_1..X_4 ⊆ Z_v, |X_i| = k_i, with
  Σ k_i − λ = v and every nonzero difference represented λ times in total; equivalently the
  ±1 sequences a_i (−1 on X_i) satisfy Σ_i PAF_{a_i}(s) = 0 for all s ≠ 0.
* Propus difference family (Seberry–Balonin 2017, Đoković et al.): a GS family with X_2 = X_3
  and X_1 (or X_4) symmetric (X = −X). Plugging the circulants into the propus array
      [ −A1   A2R   A3R   A4R ]
      [  A3R  RA4    A1  −RA2 ]
      [  A2R   A1  −RA4   RA3 ]
      [  A4R −RA3   RA2    A1 ]   (R = back-diagonal identity)
  gives a symmetric Hadamard matrix of order 4v.
* For v = 65 the propus parameter sets are exactly (65; 27,31,31,27; 51), (65; 31,27,27,31; 51),
  (65; 28,29,29,28; 49), (65; 29,28,28,29; 49) (sums of ±1 blocks (11,3,3,11), (3,11,11,3),
  (9,7,7,9), (7,9,9,7); 11²+2·3²+11² = 3²+2·11²+3² = 9²+2·7²+9² = 7²+2·9²+7² = 260).

## STATUS AND SOURCES (checked 2026-10-14)
* Craigen–Kharaghani, Handbook of Combinatorial Designs (2007), Table 1.52: v = 65 listed among odd
  v < 200 with no known symmetric Hadamard matrix of order 4v.
* Abuzin–Balonin–Đoković–Kotsireas (2019): "The smallest order 4v for which symmetric Hadamard
  matrices are not yet known is now 260."
* Đoković, "Some new symmetric Hadamard matrices" (arXiv:2101.05429, 2022): propus search done for all
  odd v ≤ 63; undecided list starts v = 65, 89, 93, ...
* Đoković, arXiv:2301.02751v3 (Nov 2024): "only three odd v < 100 for which no symmetric Hadamard
  matrix of order 4v is known: 65, 89, 93"; constructs v = 93. So 260 = 4·65 is the smallest open order.
* No 2025–2026 paper found resolving 260 (searched arXiv / web: Đoković 2508.17141 (Aug 2025) gives
  orders q(q+1); Valtonen 2608.06920 classifies orders ≤ 32; Cati–Pasechnik database 2411.18897
  does not cover symmetric matrices). The general Hadamard orders 668, 716, 892 were reportedly
  settled in 2026 (Epoch AI / MathWorld), which does not concern symmetric matrices.

## RESEARCH DIRECTION
1. Exhaust the multiplier-orbit ansatz (blocks unions of orbits of a subgroup H ≤ Z_65^*), the
   standard tool of Đoković et al. (v = 73, 93, 113, 127, 191 were all done this way).
2. Order-2 subgroups H = {1,14}, {1,51} give spaces too large for naive orbit search; use a
   big-table meet-in-the-middle (hash all candidate X_4, iterate over (X_1, X_2) pairs with PSD filter).
3. Exploit 65 = 5·13 (compression, Z_5 × Z_13 structure) and local search in the full space.

## PITFALLS
* Gaussian "expected number of solutions" heuristics are unreliable here: several orbit subspaces
  (e.g. H = ⟨16⟩ of order 3) have zero solutions although the heuristic predicts hundreds.
* Complementing a block changes the parameter set; always normalize k_i ≤ v/2.
* The symmetric block must be X_1 or X_4 (not the repeated block) for the propus array.
* A found family must be verified independently (PAF identity + the 260×260 matrix itself).

## CERTIFICATE
If found: the three blocks X_1 (symmetric), X_2 = X_3, X_4 as explicit subsets of Z_65, and a Lean
proof that (i) the PAF identity holds and (ii) the explicit 260×260 propus matrix H satisfies
H = Hᵀ and H·Hᵀ = 260·I (checked by `decide`-free kernel computation).
If not found: certified negative statements for the exhausted subspaces cannot be fully
kernel-checked within the time budget; they are reported as computational results only.

---
# PROBLEM 2 (switched to after the 260 search stalled; same table): a symmetric Hadamard matrix of order 532

## TARGET
Construct a symmetric Hadamard matrix of order 4v for some odd v on Đoković's list of undecided cases
(v = 89, 101, 107, 119, 133, 149, 153, 163, 167, 179, 183, 193 after 2024–2025 progress), using the
propus construction with multiplier-orbit blocks, searched exhaustively with fast MITM programs.

## STATUS AND SOURCES
* Đoković, arXiv:2101.05429 v2 (Jan 2022), §3: undecided v < 200: 65, 89, 93, 101, 107, 119, 133, 149, 153,
  163, 167, 179, 183, 189, 193. v = 93 settled in arXiv:2301.02751 (2024); v = 189 by arXiv:2508.17141
  (2025, orders q(q+1), q = 27). No later paper on v = 133 found (checked 2026-10-14).

## CERTIFICATE
Explicit blocks (bitmasks) + Lean proof of the general propus theorem + kernel-checked PAF identity;
main theorem: ∃ H : Matrix (Fin 532) (Fin 532) ℤ, ±1 entries, Hᵀ = H, H Hᵀ = 532 • 1.
