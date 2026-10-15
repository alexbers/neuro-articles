# PROBLEM (A15): new proper circulant weighing matrices for open entries of the CW tables

## TARGET

1. **Open table entries.** For parameter pairs `(n, k = s^2)` with `n < 1000`, `s <= 19`
   for which the existence of a *proper* circulant weighing matrix `CW(n, k)` is listed as
   unknown in the current tables, construct an explicit proper `CW(n, k)` (first row in
   `{0, +1, -1}^n`) and certify it.
   Tables: Gordon's La Jolla Circulant Weighing Matrix Repository (dataset v1.3, commit
   5b3d729, 2026-04-24, entries with `"status": "Open"`) and the curated table of all known
   proper `CW(n,k)` with `n < 1000`, `k <= 19^2` (Gordon, *Cyclic relative difference sets
   and circulant weighing matrices*, J. Algebr. Comb. 63 (2026), Table 7 = arXiv:2501.14924;
   reproduced verbatim on https://dmgordon.org/circulant-weighing-matrices/, site updated
   2026-09-03).
2. **Infinite family (stretch goal).** S. L. Ma (IMS/NUS workshop 2011, "Proper circulant
   weighing matrices of weight p^2", open problem 7): *apart from the classical construction
   of proper CW((p^2+p+1)w/2, p^2), w | p-1, w = 2 (mod 4), are there other (infinite)
   families of proper CW(v, p^2)?*  Arasu-Gordon-Zhang (Cryptogr. Commun. 2021) wrote that
   for `CW(q^3-1, q^2)`-type parameters "larger cases are currently out of reach"; Gordon
   (2025/26) lists `CW(26,3^2)`, `CW(62,5^2)`, `CW(114,7^2)`, `CW(182,9^2)` as *sporadic*
   (boxed) entries and lists no proper `CW(2(q^2+q+1), q^2)` for `q = 11, 13, 17, 19`.

## DEFINITIONS

* A *circulant weighing matrix* `CW(n,k)` is an `n x n` circulant matrix `W` with entries in
  `{0,1,-1}` and `W W^T = k I`. Equivalently its first row `a = (a_0,...,a_{n-1})` satisfies
  `PAF_a(d) := sum_{i<n} a_i a_{(i+d) mod n} = k` for `d = 0` and `= 0` for `0 < d < n`
  (perfect ternary sequence of period `n` and energy `k`). Necessarily `k = s^2`.
* `a` is *proper* if its support is not contained in a coset of a proper subgroup of `Z_n`,
  i.e. for every divisor `e > 1` of `n` the support meets at least two residue classes mod `e`.
  (Non-proper CWs are exactly the "lifts" `A(X^e)` of smaller CWs; the repository and
  Gordon's Table 7 record existence of *proper* CWs.)

## STATUS AND SOURCES (checked 2026-10-08)

* La Jolla CW repository JSON (v1.3, 2026-04-24): `CW(146,8)`, `CW(266,11)`, `CW(366,13)`,
  `CW(504,12)`, `CW(614,17)`, `CW(762,19)` all have `"status": "Open"` (second parameter is `s`).
* Gordon 2026 Table 7 / web table (2026-09-03), known proper CW(n,k): `8^2: 42m, 62m, 73, 127,
  217, 254, 434, 511`; `11^2: 133, 665`; `12^2: 182m, 273, 336m, 403, 546, 744, 806, 819`;
  `13^2: 183, 549`; `17^2: 307`; `19^2: 381`. None of 146, 266, 366, 504, 614, 762 appears.
* Arasu-Gordon-Zhang 2021 (Table 8) had listed 366, 614, 762 via a theorem that Gordon 2025
  later corrected (the RDS-to-CW theorem needs `m, n` odd); these entries were removed in
  the 2025/26 table, i.e. their existence is currently unsupported in the literature.
* Tan, arXiv:2608.18468 (Sept 2026) settles 8 nonexistence cases in Strassler's range;
  none of the above.
* OpenAI 2026 release (CONTENTS.md): circulant Hadamard / Barker and merit factor results
  only; nothing on these CW parameters.

## RESEARCH DIRECTION

* Write `Z_{2m} = Z_m x Z_2` for odd `m`; `A = U + zV` is a CW(2m,k) iff `U+V` and `U-V`
  both satisfy `B B^(-1) = k`. Two CW(m,k) with *the same support* give a CW(2m,k).
* The classical Singer-complement CW(q^2+q+1, q^2) (q odd): `W_0([y]) = eta(N(y) Tr(y))`
  on `GF(q^3)^*/GF(q)^*`. Look for a second CW on the same support (e.g. compose with a
  collineation fixing the line `Tr = 0`).
* For other even orders: multiplier-invariant integer CWs `ICW_2(m,k)` paired as above.
* Products `A(X^{n/n1}) B(X^{n/n2})` for non-coprime orders when the difference sets of the
  supports meet only in 0.

## PITFALLS

* A lift of a smaller CW is not proper and does not count (e.g. `CW(266,121)` exists as a
  lift of `CW(133,121)`; only the *proper* question is open).
* The repository JSON has known inconsistencies (e.g. `CW(404,2)` "No" although the `2m`
  family gives it; `CW(96,6)`, `CW(338,6)` "Open" although covered by the `48m`, `26m`
  families). Novelty must be checked against Gordon's Table 7 as well, not the JSON alone.
* A general family claim ("for every odd prime power q") needs a proof; computer checks for
  finitely many q are evidence only.
* Statement drift: the Lean statement must mean "periodic autocorrelation is `k*delta`" for
  the *given* sequence, entries in `{0,+-1}`, length `n`, and properness as defined above.

## CERTIFICATE

Explicit first rows (integer lists of length `n`), checked in Lean 4 (core only) by
`decide +kernel`: length, entries in `{-1,0,1}`, `PAF(d) = k [d = 0]` for all `d < n`, and
properness (every divisor `e > 1` of `n` sees two support residues mod `e`).
