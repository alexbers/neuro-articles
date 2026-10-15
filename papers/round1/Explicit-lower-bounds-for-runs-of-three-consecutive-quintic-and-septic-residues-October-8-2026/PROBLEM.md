# PROBLEM — Erdős Problem #436: runs of three consecutive k-th power residues (odd k ≥ 5)

## TARGET
For a prime `p` and integers `k, m ≥ 2` let `r(k,m,p)` be the least `r ≥ 1` such that
`r, r+1, …, r+m-1` are all `k`-th power residues modulo `p`, and
`Λ(k,m) = limsup_{p→∞} r(k,m,p)`.

Erdős–Graham (after Lehmer–Lehmer) ask: *Is `Λ(k,3)` finite for all odd `k`? How large are
`Λ(k,2)`, `Λ(k,3)`?*  The first open case is `k = 5`.

Primary target: decide whether `Λ(5,3) < ∞`.
Fallback target (if the primary resists): new, certified quantitative information on `Λ(5,3)`
and `Λ(7,3)` — explicit lower bounds — together with whatever the search reveals about finiteness.

## DEFINITIONS
* `IsPrime p :⇔ 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p`.
* A *prime assignment* is a map `g : primes → ℤ/kℤ`. Its completely additive extension is
  `χ_g(n) = Σ_{q^a ∥ n} a·g(q) (mod k)`.
* For a prime `P ≡ 1 (mod k)` the `k`-th power residue index `ind_P(n) mod k` (w.r.t. a fixed
  generator of the `k`-th roots of unity) is completely additive on integers prime to `P`, and
  `n` is a `k`-th power residue mod `P` iff `ind_P(n) ≡ 0 (mod k)`.
* Classical reduction (Lehmer–Lehmer–Mills 1963): for odd prime `k`, every prime assignment on a
  finite set of primes is realised by infinitely many primes `P ≡ 1 (mod k)` (Kummer theory +
  Chebotarev). Hence
  `Λ(k,3) = sup_g (first r with χ_g(r) = χ_g(r+1) = χ_g(r+2) = 0)`, and
  `Λ(k,3) = ∞` iff for every `B` some `g` has no zero triple below `B`.

## STATUS AND SOURCES (checked 2026-10-08)
* https://www.erdosproblems.com/436 (last edited 25 Oct 2025): status *open*; "The remaining
  questions are to examine whether Λ(k,3) is finite for all odd k ≥ 5, and the growth rate of
  Λ(k,2) and Λ(k,3)". Forum thread: 3 comments, none with new results.
* Known: Λ(2,2)=9, Λ(3,2)=77, Λ(4,2)=1224 (Bierstedt–Mills), Λ(5,2)=7888, Λ(6,2)=202124
  (Lehmer–Lehmer–Mills 1963), Λ(7,2)=1649375 (Brillhart–Lehmer–Lehmer 1964), Λ(3,3)=23532
  (Lehmer–Lehmer–Mills–Selfridge 1962), Λ(k,3)=∞ for even k, Λ(k,l)=∞ for l ≥ 4 (Graham 1964),
  Λ(k,2)<∞ for all k (Hildebrand 1991; combinatorial proof Dietzel, arXiv:1309.7506).
* No value or bound for Λ(5,3) or Λ(7,3) found in the literature or on the web (searches for
  "three consecutive quintic residues", Λ(k,3), 2024–2026); not among the results listed in
  ./CONTENTS.md.

## RESEARCH DIRECTION
1. Model the problem as a constraint problem on prime assignments (k colours on primes,
   completely additive extension, forbid three consecutive zeros).
2. Search for assignments avoiding zero triples as far as possible (DFS with conflict-directed
   backjumping; WalkSAT-style local search with incremental bookkeeping); probe for an UNSAT
   threshold (which would prove finiteness and, with a matching assignment, give the exact value).
3. Certify any obtained assignment in Lean: show that every completely additive function agreeing
   with `g` on primes has no zero triple up to `L` (finite check + kernel-checked reduction).

## PITFALLS
* A lower bound on Λ(5,3) says nothing about finiteness; do not present it as a resolution.
* The Lean theorem certifies only the combinatorial statement; the passage to primes `P`
  (Kummer + Chebotarev, including the prime `q = k` itself) is classical but not formalised.
* `native_decide` adds a trusted-evaluation axiom; disclose it.
* Statement drift: the Lean hypothesis must quantify over *all* completely additive `f` with the
  prescribed prime values (not over a table computed by the same code that is being checked).
* Computations beyond the Lean range (C programs) are evidence, not certificates.

## CERTIFICATE
An explicit prime assignment `g` (short exception list, default value 1), a bound `L`, and a
Lean 4 (core only) file proving
`∀ f, (complete additivity mod 5 on [1,L]) → (f = g on primes ≤ L) → no r ∈ [1, L-2] with
f(r) ≡ f(r+1) ≡ f(r+2) ≡ 0 (mod 5)`, with `#print axioms` output.
