# Smale's mean value problem: explicit and quantitative counterexamples (B10)

## TARGET
Smale's mean value conjecture (1981) asserts that for every complex polynomial `p` of degree `d ≥ 2`
and every `z` with `p'(z) ≠ 0` there is a critical point `c` of `p` with

    |p(z) − p(c)| / |z − c|  ≤  K · |p'(z)|                                  (MV_K)

with `K = 1` (and even `K = (d−1)/d`, attained by `z^d − dz`). In September 2026 a non-explicit
disproof of the `K = 1` form was announced (GPT-6 Astra, Lean-checked): there is *some* polynomial
of "very large, unspecified degree" violating (MV_1) "by a small margin".

Primary target (registered): an **explicit** counterexample of **explicit degree** with an exact
certificate (and Lean check of the finite certificate).

Secondary target (if the primary one is out of reach): a **quantitative** statement, i.e. a certified
numerical lower bound `K_∞ ≥ m > 1` for the asymptotically best constant

    K_d := sup { min_{p'(c)=0} |p(z) − p(c)| / (|z − c| |p'(z)|) : deg p = d, p'(z) ≠ 0 },
    K_∞ := sup_d K_d .

Smale proved `K_d ≤ 4`; the conjecture says `K_d ≤ 1` (resp. `= (d−1)/d`).

## DEFINITIONS
* Normalisation: by affine change of variable, `z = 0`, `p(0) = 0`, `p'(0) = 1`; then the quantity
  is `min_c |p(c)/c|`.
* Continuum witness: a Jordan domain `D ∋ z0`, `F` holomorphic near `D̄` with `F(z0)=0`, `F'(z0)=1`,
  `F' ≠ 0` on `D̄`, and `|F(z)| ≥ m |z − z0|` on `∂D`. Its *margin* is `m`.

## STATUS AND SOURCES (checked 2026-10-14)
* Smale 1981 (K=4); Beardon–Minda–Ng, Crane, Fujikawa–Sugawa: `K_d ≤ 4 − O(1/d)` type bounds.
* Conjecture known for `d ≤ 4` (Tischler), `d = 5` (Crane, interval arithmetic, announced);
  `d = 6` open (Zenodo 10.5281/zenodo.22390113, Sept 2026); numerical evidence `d ≤ 10`.
* K=1 form disproved non-explicitly: https://github.com/tadamcz/mean-value-problem (GPT-6 Astra,
  Sept 2026; Lean/Mathlib; "very large, unspecified degree ... small margin"). No explicit
  counterexample and no quantitative lower bound on `K_∞` is known to us (web search 2026-10-14;
  not in OpenAI's CONTENTS.md of 2026-10-06; Jatar–Ng arXiv:2608.27047 study a restricted family).

## RESEARCH DIRECTION
1. Understand the GPT construction as a *continuum* problem: domain `D = Φ(𝔻)`, `F = (z−z0)·B(W(z))/B(W(z0))`
   with `W = Φ^{-1}` and a Blaschke factor `B`; margin `= 1/|B(W(z0))|`; condition `F' ≠ 0` on `D̄`
   ⇔ `H'(w) = Φ'(w)B(w) + (Φ(w)−z0)B'(w)` zero-free on the closed unit disk.
2. Optimise the margin over explicit families of domains with explicit conformal maps
   (rounded slit discs / "Pac-Man" domains).
3. Discretise: place `N` critical points so that `p' ≈ F'` in `D`; polish by sequential LP on the
   exact objective `min_k |p(c_k)/c_k|`; certify a finite example exactly (Gaussian-integer
   critical points; Lean kernel check).
4. If (3) fails, prove a realisation lemma (continuum witness ⇒ polynomials with margin `m − ε`)
   and certify the continuum witness with rigorous ball arithmetic.

## PITFALLS
* GPT's own parameters give margin ≈ 1 + 3·10⁻⁷ (the hub of their lemniscate is extremely thin) —
  hopeless for explicit degrees.
* Numerical winding numbers alias when the critical pair of `F` touches `∂D`; an early "margin 1.03"
  was an artefact. Only adaptive / ball-arithmetic winding counts are trusted.
* For domains with a thin wall, the equilibrium measure (from ∞) of the wall tip is ~0, so the
  density `N·μ_∞ + σ` required for `p' ≈ F'` is negative there for every practical `N`; equivalently
  polynomial approximation of `F` on `D̄` converges extremely slowly. Explicit small degree is then
  impossible by this route.
* A first-order (in 1/N) analysis shows equilibrium-type configurations can never beat (d−1)/d
  (maximum principle for Re(1/κ), κ = zΨ'/Ψ of the exterior map) — an O(1) "design" margin is needed.

## CERTIFICATE
* Finite (primary target, not reached): list of Gaussian-integer coefficients of `p` and of its `d−1`
  critical points; checked by `SmaleCert.check` (Lean, `decide`), soundness `SmaleCert.check_sound`
  (`lean/ExplicitCheckAux.lean`).
* Continuum witness (reached): for a *rational* conformal map (rounded Koebe map `Φ = k∘u`) the
  condition `F' ≠ 0` on `D̄` is equivalent to an explicit cubic `P` having no zero in the closed unit
  disc; Lean checks `P` exactly in Gaussian-rational arithmetic plus a quadtree certificate, and proves
  injectivity of `Φ`, the derivative identities, the boundary identity and the margin bound
  (`lean/Main.lean`, theorem `SmaleKoebe.witness`). For non-rational maps (slit discs) the condition was
  certified with Arb ball arithmetic (`code/verify_cont.py`).
* The passage from a witness to polynomials (realisation lemma) and monotonicity of `K_d` are paper
  proofs.
