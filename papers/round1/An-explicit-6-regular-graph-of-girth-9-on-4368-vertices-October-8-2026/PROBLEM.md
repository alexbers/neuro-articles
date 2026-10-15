# PROBLEM (A11): explicit small (6,9)- and (6,10)-graphs — empty cells of the cage table

## TARGET
Construct an explicit 6-regular graph of girth exactly 9 (a *(6,9)-graph*) — and, if possible, a
6-regular graph of girth exactly 10 (a *(6,10)-graph*) — on as few vertices as possible, and certify
it in Lean 4 (core only, no Mathlib).  This gives an explicit upper bound
`n(6,9) ≤ N` (resp. `n(6,10) ≤ N`) for the cage function `n(k,g)`.

Success criterion: a certified graph of order well below the only bound currently implied by the
literature (see STATUS), i.e. `N < 7781` for (6,9) and `N < 7782` for (6,10), with the order
reported exactly.

## DEFINITIONS
* A graph on vertex set `Fin n` is given by a Boolean adjacency `adj : Fin n → Fin n → Bool`;
  it is *simple* if `adj` is symmetric and irreflexive.
* `degree adj v` = number of `w : Fin n` with `adj v w = true`; `k`-*regular*: all degrees equal `k`.
* A *cycle* is a list `[c₀,…,c_{L-1}]` of `L ≥ 3` pairwise distinct vertices with
  `adj cᵢ c_{(i+1) mod L}` for all `i < L`.
* *Girth exactly g*: some cycle has length `g` and every cycle has length `≥ g`.
* `n(k,g)` = minimum order of a `k`-regular graph of girth `g`.  Moore bound:
  `n(6,9) ≥ 1 + 6(1+5+25+125) = 937`, `n(6,10) ≥ 2(1+5+25+125+625) = 1562`.

## STATUS AND SOURCES (checked 2026-10-08)
* House of Graphs, cage meta-directory (current table, rows k=3..20, columns g=5..20):
  https://houseofgraphs.org/meta-directory/cages — the cells (6,9) and (6,10) are **empty**
  (no known graph listed); the same holds for (7,9),(7,10),(8,9),… .
* G. Exoo, J. Goedgebeur, J. Jooken, L. Stubbe, T. Van den Eede, *New small regular graphs of
  given girth: the cage problem and beyond*, arXiv:2511.07247 (v2, 22 Jul 2026), Electron. J.
  Combin. 33(3) P48 (28 Aug 2026).  Their Table 2 lists `n(6,9) ≥ 938, upper "?"` and
  `n(6,10) ≥ 1563, upper "?"`, where "?" means "a graph is known to exist but the known ones are
  orders of magnitude larger than the lower bound".  They give the first nontrivial bound
  `n(6,11) ≤ 7783`.
* Exoo–Jajcay, *Dynamic Cage Survey*, EJC DS16 (2013), Table 6: no entries for (6,9),(6,10).
* Implied bound: by the strict monotonicity `n(k,g₁) < n(k,g₂)` for `g₁ < g₂` (Fu–Huang–Rodger 1997)
  and `n(6,11) ≤ 7783` one gets only `n(6,10) ≤ 7782`, `n(6,9) ≤ 7781` (non-explicit).
* Searches (web, arXiv, CONTENTS.md of the OpenAI 2026 release) found no explicit (6,9)- or
  (6,10)-graph.  Not in the OpenAI release.

## RESEARCH DIRECTION
Voltage lifts (regular covers) of tiny base multigraphs with voltages in a "random-like" finite group:
the girth of the lift is ≥ g iff every cyclically reduced closed walk of length < g in the base has
non-identity net voltage.  Groups SL(2,p) are attractive: few elements of small order, and
left multiplication gives a large automorphism group, which reduces the girth verification to a
handful of root vertices.  Search: randomized depth-first backtracking with forbidden-value marking
(each closed walk containing the newest voltage exactly once forbids one value).

## PITFALLS
* Girth must be **exactly** g: exhibit a g-cycle as well as excluding shorter cycles.
* The graph must be simple (no loops/multi-edges in the lift) and regular of degree exactly 6.
* Vertex-transitivity arguments must be proved (automorphisms = left multiplications; requires
  associativity of the matrix product modulo p, proved in Lean), not assumed.
* Counting the vertices: the Lean statement must fix the order `N` of the vertex type `Fin N`.
* An implicit bound from monotonicity is not an explicit graph; conversely an explicit (6,10)-graph
  does not give an explicit (6,9)-graph.
* Novelty must be checked against the *current* House of Graphs table and the 2026 EJC paper.

## CERTIFICATE
Lean file `Main.lean` proving
`∃ adj : Fin N → Fin N → Bool, IsSimpleGraph adj ∧ IsRegular adj 6 ∧ HasGirth adj g`
with all definitions stated above the theorem, using only `decide +kernel` for finite checks
(no `native_decide`), and `#print axioms` showing only the standard axioms.  The voltage data and
search/verification scripts are included.
