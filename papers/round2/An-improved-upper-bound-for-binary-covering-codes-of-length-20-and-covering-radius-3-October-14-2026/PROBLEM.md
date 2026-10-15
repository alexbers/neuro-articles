# PROBLEM (B09): upper bounds for small covering codes — the football pool problem and Kéri's tables

## TARGET
Primary (famous): improve an upper bound in the football pool problem, i.e. construct a ternary code of
length n with covering radius 1 and fewer words than the record:
K_3(6,1) ≤ 72 (record 73, 1989), K_3(7,1) ≤ 185 (record 186, 1989), K_3(8,1) ≤ 485 (486, 1989),
K_3(9,1) ≤ 1268, K_3(10,1) ≤ 3644 (3645, 1984).
Secondary: improve any upper bound in G. Kéri's standard tables of binary, ternary, quaternary and mixed
binary/ternary covering codes (K(n,R), K_3(n,R), K_4(n,R), K(t,b,R)), and in particular binary entries
whose current value is "trivial" (inherited by doubling/puncturing) or inconsistent with later improvements
of other entries.

## DEFINITIONS
- A q-ary code C ⊆ Z_q^n has covering radius ≤ R if every word x ∈ Z_q^n is within Hamming distance R of
  some codeword. K_q(n,R) is the minimum size of such a code (K(n,R) = K_2(n,R)).
- A binary code C of covering radius R is *normal* with respect to coordinate i if for every word x,
  d(x, C_i^0) + d(x, C_i^1) ≤ 2R+1, where C_i^a = {c ∈ C : c_i = a}.
- Amalgamated direct sum (ADS, Graham–Sloane 1985; Cohen–Lobstein–Sloane 1986): if A (length n_A, radius R_A)
  is normal w.r.t. its last coordinate and B (length n_B, radius R_B) w.r.t. its first coordinate, then
  A ⊕̇ B = {(a, s, b) : (a,s) ∈ A, (s,b) ∈ B} has length n_A+n_B−1, covering radius ≤ R_A+R_B and
  |A^0||B^0| + |A^1||B^1| words.
- Matrix method: C = {x ∈ Z_q^n : Hx ∈ S} for a k×n matrix H = [I_k | B]; C has covering radius ≤ R iff S is
  an R-dominating set of the Cayley graph Cay(Z_q^k, {sums of ≤ R nonzero multiples of columns}), and
  |C| = |S| q^(n−k).

## STATUS AND SOURCES (checked 2026-10-14)
- G. Kéri, Tables for bounds on covering codes, https://old.sztaki.hu/~keri/codes/index.htm (binary table
  PDF dated 2009-10-15; update log up to 2011-11-21). Football pool: 71 ≤ K_3(6,1) ≤ 73 (lower bound
  Linderoth–Margot–Thain 2007/2009, upper bound van Laarhoven–Aarts–van Lint–Wille 1989); 156 ≤ K_3(7,1) ≤ 186;
  402 ≤ K_3(8,1) ≤ 486.
- Binary: K(14,2) ≤ 248 (Bertolo–Di Pasquale–Santisi 2006), 892 ≤ K(20,3) ≤ 2048 (upper bound unmarked,
  i.e. "trivial" in Kéri's key).
- 2024–2026 literature: Gijswijt–Polak (arXiv 2504.01932, SDP lower bounds), Marosi (arXiv 2608.19872,
  q ≥ 5 only), Davydov–Marcugini–Pambianco (arXiv 2511.02542, linear codes, length function). None of them
  improves an upper bound for q ∈ {2,3} at the parameters above (searched 2026-10-14).

## RESEARCH DIRECTION
1. Strong local search (weighted two-stage exchange, as in modern dominating-set solvers) on the full
   Hamming space and on quotients (matrix method), simulated annealing over the columns of H,
   prescribed automorphism groups (orbit local search / ILP).
2. Exhaustive enumeration of small "column classes" of H = [I_k | B] for k = n−1, n−2, n−3 (classes of
   extra columns up to coordinate permutations), with local search for S on each Cayley graph.
3. Consistency check of the tables under ADS: recompute K(n_A+n_B−1, R_A+R_B) ≤ ⌊K(n_A,R_A)K(n_B,R_B)/2⌋
   for all pairs of entries and look for entries that should have improved when another entry improved —
   then construct normal codes realising the needed component bounds.

## PITFALLS
- ADS needs *normal* codes; a published code may be abnormal — normality must be checked explicitly.
- Kéri's tables were last updated around 2009–2011; check later literature before claiming novelty.
- Most football-pool records are highly structured; unstructured local search on H(7,3) stalls ~5% above
  the record — do not mistake LS failure for evidence of optimality.
- Kernel-checkable certificates for 2^20 words must not enumerate all words naively; use the ADS structure.

## CERTIFICATE
Lean 4 + Mathlib: `∃ C : Finset (Fin n → Fin 2), C.card ≤ M ∧ ∀ x, ∃ c ∈ C, hammingDist x c ≤ R`, with
the finite facts (normality of the two components) checked by `decide +kernel`, and the ADS covering
argument proved in Lean; `#print axioms` must show only the standard axioms.
