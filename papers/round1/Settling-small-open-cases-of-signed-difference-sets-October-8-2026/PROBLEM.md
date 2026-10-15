# PROBLEM — Open existence cases of signed difference sets (La Jolla SDS Repository)

## TARGET

For a finite abelian group `G` of order `v` (given by its invariant factors, e.g. `[3,9]` =
`ℤ/3 × ℤ/9`) decide whether a `(v,k,λ)` **signed difference set** exists in `G`, for the
group-specific parameter sets that are listed with status **"Open"** in D. M. Gordon's
*La Jolla Signed Difference Set Repository* (`sds.json`, v1.2, zenodo 10.5281/zenodo.7473882,
April 2026) **and** are not excluded by the four nonexistence criteria of He–Wu
(arXiv:2608.22936v2, 20 Sep 2026), which leave 22,462 open cases with `9 ≤ v ≤ 499`.

Concretely, the goal of this attempt is:

1. settle the smallest open case `SDS(9,8,1)` in `ℤ/3 × ℤ/3` (the only open case with `v < 20`);
2. settle (by explicit, machine-checked objects) as many as possible of the open cases with
   small `v` (we scanned all 710 remaining open cases with `v ≤ 100`);
3. for every claimed existence result, give a certificate checked by the Lean kernel.

## DEFINITIONS

* `ℤ[G]` is the integral group ring; for `A = ∑ a_g g` put `A⁽⁻¹⁾ = ∑ a_g g⁻¹`.
* A **signed set** is `D = ∑_{g∈G} s_g g` with `s_g ∈ {−1,0,1}`; `P = {g : s_g = 1}`,
  `N = {g : s_g = −1}`, `k = |P| + |N|` (the support size).
* `D` is a **`(v,k,λ)` signed difference set (SDS)** in `G` (Gordon, Des. Codes Cryptogr. 91
  (2023) 2107–2115, arXiv:2212.10630) if `D·D⁽⁻¹⁾ = (k−λ)·1_G + λ·G`.
  Equivalently (coefficient of `y`): `∑_{g∈G} s_g s_{g+y} = λ` for every `y ≠ 0`.
  `N = ∅` gives ordinary difference sets, `λ = 0` group-invariant weighing matrices.
* Necessary: `s² := k + λ(v−1)` is a perfect square and `|P| − |N| = ±s`
  (convention `|P| ≥ |N|`, so `|P| = (k+s)/2`, `|N| = (k−s)/2`).
* A *group-specific case* is a triple `(v,k,λ)` together with an isomorphism type of abelian
  group `G` of order `v` (the key `SDS(v,k,λ,[a₁,…,a_r])` of the repository).

## STATUS AND SOURCES (checked 2026-10-08)

* Gordon, *Signed difference sets*, DCC 2023 (arXiv:2212.10630): introduces SDS; constructions
  (Paley, Paley+0, quartic residues+0, prime-power pairs), cyclic searches; reports that a
  search for noncyclic SDS with `λ ≠ 0` found only one sporadic example `(18,13,4)` in
  `ℤ/2×ℤ/3×ℤ/3`.
* He–Chen–Ge, *New constructions of signed difference sets*, DCC 92 (2024) (arXiv:2306.05631):
  Paley-PDS constructions, `(3^{2m+1}, 3^{2m}+1, 1)` for even `m`, 4th-order cyclotomy.
* Gordon's repository (`sds.json`, v1.2, 2026-04-24, zenodo record 19741004; LJCR moved to
  https://dmgordon.org, databases frozen in 2026): 70,543 entries, **67,823 "Open"**.
* He–Wu, *Nonexistence results and constructions for signed difference sets*,
  arXiv:2608.22936v2 (20 Sep 2026): rules out 45,361 open cases; **22,462 remain open**
  (list reproduced with their script, `web/he/count_open_cases.py --write-csv`); constructs
  `(64,22,6)` in `ℤ/2⁶`, `(256,106,42)` in `ℤ/2⁸`, `(125,28,3)` in `ℤ/5³`.
* Web/literature search (Oct 2026) found no further work on these cases.
* Not in OpenAI's 722-paper release (CONTENTS.md has nothing on signed difference sets).

## RESEARCH DIRECTION

* Local search (simulated annealing) on the ternary sequence/array `s : G → {−1,0,1}` with
  fixed `|P|, |N|`, minimizing `∑_{y≠0} (C(y) − λ)²`, `C(y) = ∑_g s_g s_{g+y}`.
* Exhaustive search for small `v` with symmetry reduction (translate so `0` is in the support,
  negate so `s_0 = +1`), the necessary support condition `|S ∩ (S−y)| ≥ |λ|`,
  `|S ∩ (S−y)| ≡ λ (mod 2)`, and sign back-tracking with agreement/disagreement counts.
* Intersection numbers (quotient maps `ℤ[G] → ℤ[G/H]`) for short human nonexistence proofs.
* Check every found object against known constructions (Paley-type, skew Hadamard + {0},
  prime-power pairs, PDS with `λ−μ = 2` via `D = P − 1_G`, partial congruence partitions).

## PITFALLS

* "Open in the database" ≠ "open in the literature": the repository is incomplete. Several
  open entries actually follow from published constructions (we found such cases) — these
  must be reported as *database corrections*, not as new results.
* He–Wu's three existence results are not reflected in `remaining_open_cases.csv`
  (it only applies nonexistence criteria); `(64,22,6)` in `ℤ/2⁶` is theirs.
* The group matters: `ℤ/3×ℤ/9` vs `ℤ/3³` vs `ℤ/27` are different cases.
* An SDS is an element with coefficients in `{−1,0,1}` — a candidate with a coefficient 2
  (overlapping `P` and `N`) is not valid.
* Nonexistence claims from computer search are only as good as the search; only the
  Lean-checked ones are certified.
* Statement drift: the Lean predicate must say exactly "values in {−1,0,1}, support size k,
  all nonzero shifts have autocorrelation λ", over the right group.

## CERTIFICATE

* Existence: the explicit pair `(P, N)` of coordinate tuples; the Lean theorem
  `∃ D : ℕ → ℤ, IsSDS ms k λ D` proved by exhibiting `D` and `decide +kernel`.
* Nonexistence of `(9,8,1)` in `ℤ/3²`: a Lean proof that `¬ ∃ D, IsSDS [3,3] 8 1 D`,
  by a kernel-checked exhaustive enumeration of all `3⁹` coefficient vectors plus a short
  reduction lemma; and a human proof by intersection numbers.
