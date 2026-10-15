# PROBLEM (B06): two AlphaEvolve benchmark constants — the sign-uncertainty constant and the first autocorrelation constant

## TARGET
Beat, with a computation certified in exact arithmetic and in Lean 4, the best known upper bound for
(1) the one-dimensional sign-uncertainty constant C_SU of Bourgain–Clozel–Kahane (AlphaEvolve B.4 /
problem 6.11, "an uncertainty inequality"), and/or
(2) the first autocorrelation constant C₁ (AlphaEvolve B.1 / problem 6.2; the Sidon-set constant 2/σ²).

## DEFINITIONS
* f̂(ξ) = ∫ f(x) e^{-2πixξ} dx; A(f) = inf{r > 0 : f(x) ≥ 0 for all |x| ≥ r}.
  C_SU = largest C such that A(f)A(f̂) ≥ C for every even, integrable, real f with f̂ integrable,
  f(0) < 0 and f̂(0) < 0.
* (f*f)(t) = ∫ f(x) f(t-x) dx. C₁ = inf{ sup_t (f*f)(t)/(∫f)² : f ≥ 0, supp f ⊆ [-1/4,1/4], ∫f > 0 }.

## STATUS AND SOURCES (checked 2026-10-14 05:00–07:00 +05; re-checked 2026-10-15 03:00 +05: EinsteinArena leaderboards unchanged, no new 1-D sign-uncertainty bound found)
C_SU (upper bounds; lower bound 0.2025, Gonçalves–Oliveira e Silva–Steinerberger 2017):
* 0.353 / 0.3523 — Gonçalves, Oliveira e Silva, Steinerberger, J. Math. Anal. Appl. 2017 (Hermite).
* 0.3284 — Cohn–Gonçalves, Invent. Math. 2019 (A₊(1) ≲ 0.572990, Laguerre / double roots).
* 0.3216 — AlphaEvolve (Novikov et al. 2025; Georgiev–Gómez-Serrano–Tao–Wagner arXiv:2511.02864).
  arXiv:2608.15415 (Aug 2026) still quotes 0.45 ≤ A₊(1) ≤ 0.5671 (i.e. 0.3216) as best known.
* 0.313092 — EinsteinArena leaderboard (https://einsteinarena.com/problems/uncertainty-principle,
  agents CodexProLong/BasinHopper; verifier restricted to ≤ 25 prescribed double roots).
* 0.3089 — Chung, Du, Wesley, "Autonomous Mathematical Discovery in an Open-World Multi-Agent
  Environment", arXiv:2608.23691 (v2 Sep 14 2026), degree-226 Laguerre polynomial; they also show that
  ≤ 20 prescribed double roots cannot beat 0.315305.  ⇒ current record **C_SU ≤ 0.3089**.
C₁ (upper bounds; lower bound 1.2937, Kim–Pilanci arXiv:2606.31182):
* 1.50992 Matolcsi–Vinuesa 2010; 1.5053 / 1.5032 AlphaEvolve; 1.50314 ThetaEvolve; 1.50286 TTT-Discover
  (arXiv:2601.16175); EinsteinArena (API /api/leaderboard?problem_id=2, read 2026-10-14):
  **1.502743486709583** (agent Atris, 2026-10-13, n = 65536 steps) = current record.

## RESEARCH DIRECTION
* C_SU: f(x) = P(2πx²)e^{-πx²} with P in the span of Λ_{2j} = 2^{2j}(2j)! L_{2j}^{(-1/2)} is a +1
  Fourier eigenfunction (Hermite functions), so P(0) < 0 and P > 0 on [r,∞) give C_SU ≤ r/2π.
  For fixed degree this is an LP in the coefficients: cutting-plane LP (HiGHS) with stable
  (log-scaled) Laguerre recurrences, bisection in r, degrees far beyond the arena's 25-root cap.
  Certify P > 0 on [r,∞) exactly (Descartes / Vincent–Collins–Akritas bisection).
* C₁: polish the public record step function (smoothed max, L-BFGS-B, β-continuation), certify
  exactly via Kronecker substitution (all 131071 autoconvolution coefficients = digits of P²).

## PITFALLS
* Floating-point sign checks on a grid (as in the arena verifier) are not proofs; the polynomial can
  dip below 0 between grid points or beyond the sampled range; float underflow of e^{-u/2} for large u.
* Rationalising LP coefficients must not destroy small coefficients (use exact binary rationals).
* Prescribed-double-root families are provably limited (≥ 0.315305 for ≤ 20 roots).
* For C₁ the record vector is a degenerate minimax point; only tiny gains are realistic.
* Avoid native_decide: list-based polynomial arithmetic in the kernel is slow; use big-integer
  (GMP) evaluations whose digits encode coefficients.

## CERTIFICATE FORMAT
* `lean/Main.lean` (C_SU): Λ_n by the three-term recurrence; P = Σ γ_j Λ_{2j} (explicit integers γ_j);
  theorem `SU.P_sign : P(0) < 0 ∧ ∀ u ≥ a/b, 0 < P(u)`, all computations by `decide +kernel`.
  The Fourier-analytic reduction (Proposition in README) is classical and on paper (option (b)).
* `lean/C1.lean` (C₁): continuous statement formalised in Mathlib (option (a)):
  `C₁_le : C₁ ≤ p/q` with `C₁` defined as an infimum over admissible functions.
