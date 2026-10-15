# A12 — Zhang–Zheng absolute-indicator conjecture for n = 13

## TARGET
Exhibit a **balanced** Boolean function `f : F_2^13 → F_2` of **algebraic degree ≥ 3** whose
**absolute indicator** `Δ_f = max_{d ≠ 0} |r_f(d)|` is **strictly less than `2^⌊(13+1)/2⌋ = 2^7 = 128`**,
and certify all three properties in Lean 4 (core only).
Such a function is a counterexample to the Zhang–Zheng conjecture (1995) in the case n = 13.

## DEFINITIONS
* Inputs `x = (x_0,…,x_12) ∈ F_2^13` are encoded as naturals `x = Σ x_i 2^i < 2^13`; `x ⊕ d` is bitwise xor.
* `f` is given by its truth table, a natural number `tt < 2^8192` whose bit `x` is `f(x)`.
* Autocorrelation: `r_f(d) = Σ_{x ∈ F_2^13} (−1)^{f(x) ⊕ f(x ⊕ d)}`; absolute indicator `Δ_f = max_{d≠0} |r_f(d)|`.
* Balanced: `#{x : f(x) = 1} = 2^12`.
* Algebraic normal form `f(x) = ⊕_u a_u ∏_{i∈u} x_i` with Möbius coefficients `a_u = ⊕_{x ⪯ u} f(x)`
  (`x ⪯ u` iff `x AND u = x`); `deg f = max{|u| : a_u = 1}`. "deg f ≥ 3" means some `a_u = 1` with `|u| ≥ 3`.

## STATUS AND SOURCES (why it was open)
* Conjecture (X.-M. Zhang, Y. Zheng, *GAC — the criterion for global avalanche characteristics of
  cryptographic functions*, J. Univ. Comp. Sci. 1(5), 1995): every balanced `f` on n variables with
  `deg f ≥ 3` has `Δ_f ≥ 2^⌊(n+1)/2⌋`.
* Odd n: disproved only for **n = 9, 11** (Kavut–Maitra–Yücel, BFCA 2006 / IEEE-IT 2007, RSBF search),
  and **n = 15, 21** (modifications of Patterson–Wiedemann-type functions, e.g. Maitra–Sarkar,
  IEEE-IT 48(1) 2002, for n = 15; see the references of Tang–Maitra below). This list is restated as the current state of the art by
  D. Tang, S. Maitra, *Construction of n-variable (n ≡ 2 mod 4) balanced Boolean functions with maximum
  absolute value in autocorrelation spectra < 2^{n/2}*, IEEE-IT 64(1) 2018, eprint
  https://eprint.iacr.org/2016/1078 (Sec. I: "For odd variables n, this conjecture has been disproved for
  n = 9, 11 [..], n = 15 [..] and n = 21 [..]"; the concluding open-problems section repeats this list
  and asks for a general odd-n construction). The same odd-n list appears in Kavut–Maitra–Yücel,
  eprint https://eprint.iacr.org/2006/181 (Sec. 1), and D. Tang's BFA 2018 survey slides
  (https://org.uib.no/selmer/workshops/BFA2018/Slides/Tang.pdf: counterexamples known for n = 9, 10, 11,
  14, 15, 21 only). Later work concerns even n only: Kavut–Maitra–Tang
  (DCC 87, 2019), F. Zhang–E. Pasalic–Y. Wei (Information Sciences 2021,
  https://www.sciencedirect.com/science/article/abs/pii/S0020025521006289), Kavut et al.
  (*Computers* 12(8):159, 2023). Searches (Oct 2026) of eprint/arXiv/web found no balanced 13-variable
  function with Δ < 128; the case n = 13 is the smallest odd n for which the conjecture was still unresolved.
  Not among the 722 items of OpenAI's release (grep of CONTENTS.md for autocorrelation/absolute indicator/Zhang).
* Even n: disproved for n = 10, 14 (search) and all even n ≥ 12 (constructions + search) — not our target.

## RESEARCH DIRECTION
Search in a small, highly symmetric class: functions invariant under the affine group
`AGL(1,13) = {i ↦ a i + b mod 13}` acting on the 13 coordinates (74 orbits on F_2^13, search space 2^74).
For a permutation-invariant f the Walsh spectrum and the autocorrelation are constant on the same 74 orbits,
so `r` can be computed from 74 Walsh values via a 74×74 orbit matrix. Use the Kavut–Yücel cost
`Σ_ω (W_f(ω)^2 − 2^n)^2 = 2^n Σ_{d≠0} r_f(d)^2` with steepest-descent/tabu moves (flip one orbit), many
random restarts, and record functions that are balanced (or have a Walsh zero) and have small Δ.

## PITFALLS
* The bound is strict: Δ = 128 (attained e.g. by concatenating two suitable 12-variable bent functions) does
  **not** count. For balanced f all r_f(d) ≡ 0 (mod 8), so the target is Δ ≤ 120.
* Unbalanced functions do not count; a function with a zero Walsh coefficient may be shifted to a balanced one,
  but odd-weight functions can never be balanced by affine shifts (their Δ values are ≡ 4 mod 8).
* The degree condition must be certified (quadratic functions are excluded by the conjecture).
* The Lean statement must use the *naive* definitions (sum over all 2^13 inputs, all 8191 shifts); fast
  evaluation tricks are allowed only inside the proof and must be proved equal to the naive definitions.
* Do not overstate: this settles only the case n = 13 (and gives nothing for n = 17, 19).

## CERTIFICATE
The 8192-bit truth table (hex) + a Lean file proving, for that literal:
`weight = 2^12`, `∃ u, |u| ≥ 3 ∧ a_u = 1`, and `∀ d, 0 < d < 2^13 → |r_f(d)| ≤ 112` (< 128), checked by the
kernel (`decide +kernel`, no `native_decide`), with `#print axioms` showing only standard axioms.
