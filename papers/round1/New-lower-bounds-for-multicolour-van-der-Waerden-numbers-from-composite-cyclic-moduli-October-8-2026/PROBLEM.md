# PROBLEM (A05): improve record lower bounds for small multicolour van der Waerden numbers

## TARGET
Improve (i.e. exhibit explicit colourings beating) the best published lower bounds for the
diagonal van der Waerden numbers `W(r,k)` with `r ∈ {4,5,6}` colours that appear in the standard
tables (Wikipedia "Van der Waerden number", table "W(r,k)", columns 4–6 colours, rows k = 3..11;
Monroe's table of 4-colour bounds, JCMCC 128 (Dec 2025), rows k = 3..25), and certify every new
bound in Lean 4 (core only) by a kernel-checked proof that a concrete r-colouring of
`{0, …, N-1}` has no monochromatic k-term arithmetic progression.

## DEFINITIONS
* A k-term AP in ℕ: `a, a+d, …, a+(k-1)d` with `d ≥ 1`.
* `W(r,k)` = least `N` such that every r-colouring of `{1,…,N}` contains a monochromatic k-term AP.
* `W(r,k) > N`  ⟺  some r-colouring of `N` consecutive integers has no monochromatic k-AP.
  In Lean: `VdWGt r k N := ∃ c : ℕ → ℕ, (∀ x < N, c x < r) ∧ NoMonoAP k N c`, with
  `NoMonoAP k N c := ∀ a d, 0 < d → a + (k-1)d < N → ∃ i < k, c (a + i d) ≠ c a`.
* Cyclic colouring: χ : ℤ/n → [s] with no monochromatic `a, a+d, …, a+(k-1)d (mod n)`, `d ≢ 0`.

## STATUS AND SOURCES (checked 2026-10-08)
* Wikipedia, "Van der Waerden number" (wikitext fetched 2026-10-08): 4-colour column
  W(4,6) > 157,209; W(4,8) > 12,288,155; W(4,9) > 139,847,085; W(4,11) > 3,464,368,083;
  5 colours: W(5,6) > 786,740, W(5,8) > 86,017,085, W(5,9) > 978,929,595, W(5,10) > 8,327,484,046,
  W(5,11) > 38,108,048,913; 6 colours: W(6,6) > 1,555,549, W(6,8) > 602,119,595,
  W(6,9) > 6,852,507,165, W(6,10) > 58,292,388,322, W(6,11) > 419,188,538,043.
  https://en.wikipedia.org/wiki/Van_der_Waerden_number
* D. Monroe, "New lower bounds for van der Waerden numbers using distributed computing",
  arXiv:1603.03301v7 (Nov 2022) and JCMCC 128 (published 4 Dec 2025): Table 1 (4 colours:
  W(4,6) > 157,348, W(4,8) > 12,288,155, W(4,9) > 139,847,085, W(4,11) > 3,464,368,083,
  W(4,12) > 37,054,469,451, all from Xu's product recursion with *prime* moduli
  1,069 / 3,389 / 17,863 / 58,013 / 139); the 5/6-colour entries on Wikipedia come from the
  Blankenship–Cummings–Taranchuk recursion W(r,k) > p·(W(r−⌈r/p⌉,k)−1) with p = largest prime ≤ k.
* Komkov 2020 (arXiv:1701.05603), Heule 2017 (J. Comb. 8), Rabung–Lotts 2012 (EJC 19 P35),
  Blankenship–Cummings–Taranchuk 2018 (Eur. J. Comb. 69): older table entries.
* Searches (Oct 2026) for the new values and for later tables (incl. the 2026 survey of
  Bergelson–Richter arXiv:2603.25922, Hunter arXiv:2301.06212, Fox arXiv:2606.02541,
  arXiv:2608.20824) found no improvement of these entries; the asymptotic papers do not
  tabulate small values.  OpenAI's Oct-2026 release (CONTENTS.md) has only the asymptotic
  superexponential result (item 160), no small-number table.

## RESEARCH DIRECTION
Lower-bound colourings for many colours are built recursively.  A unifying "blow-up" lemma:
if `F : ℤ/n × [t] → [r]` is injective in the second argument and every colour class
`P_γ = {z : γ ∈ F(z,[t])}` is free of cyclic k-APs, then for any t-colouring ψ of `[0,M)` without
monochromatic k-AP, `x ↦ F(x mod n, ψ(⌊x/n⌋))` is an r-colouring of `[0,nM)` without one.
Hence `W(r,k) − 1 ≥ n·(W(t,k) − 1)`.  Instances: (a) Xu/Hunter products with a cyclic
s-colouring (r = st), (b) BCT blocks (n = p ≤ k), (c) counting covers on ℤ/p, p > k prime,
where each P_γ has < k elements.  Look for better moduli than the ones used in the tables:
the record 2-colour certificates are cyclic on composite moduli (zipped colourings
226 = 2·113, 1642 = 2·821, 5158 = 2·2579, 19394 = 2·9697, 58066 = 2·29033), which the
published product bounds did not use; and BCT's own remark (blocks of prime size p > k with
p − ⌊p/r⌋ < k) was not applied in the tables (k = 10: p = 11 instead of 7).

## PITFALLS
* Cyclic vs interval: a colouring of `[0,(k-1)n)` with period n is AP-free iff the induced
  colouring of ℤ/n has no cyclic k-AP *including degenerate ones* (d with small order).
  Products need the full cyclic property.
* Off-by-one: `W(r,k) > N` means a good colouring of N integers; tables write ">N".
* Do not claim entries that only match known values (e.g. W(4,10) > 1,189,640,578 is Monroe's).
* Any claim must be checked against the newest tables (Monroe JCMCC 2025, Wikipedia 2026).
* Lean statement drift: the theorem must quantify over *all* APs with d ≥ 1 inside [0,N),
  and the colouring must use at most r colours on [0,N).

## CERTIFICATE
Explicit cyclic colourings (packed bit tables) + a kernel-checked Lean proof
(`decide +kernel` on bounded Boolean checks, general lemmas proved by hand) of
`VdWGt r k N` for each claimed (r,k,N); axioms limited to the standard ones.
