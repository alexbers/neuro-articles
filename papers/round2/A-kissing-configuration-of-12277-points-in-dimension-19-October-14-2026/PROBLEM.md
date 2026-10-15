# PROBLEM (B04): two open questions about the newest kissing configurations in dimensions 19 and 21

## TARGET
Improve the best known lower bound for the kissing number τ₁₉ (currently 12 276) or τ₂₁ (currently
31 560). Give an exact, machine-checkable certificate. Concretely, settle either of the two questions
that the record holder states as open (K. Li, "Improved kissing numbers in nineteen and twenty-one
dimensions", Oct. 2026, §6):

* **Q19.** Can a second orbit of eight deleted base points be kept in the 12 276-point configuration,
  under the sign group Γ or under a smaller group with a larger table? A positive answer gives
  τ₁₉ ≥ 12 284. Even one extra point gives τ₁₉ ≥ 12 277.
* **Q21.** Can more than 3840 line-weighted sign vectors (entries ±2 on a line of PG(2,4), ±3
  elsewhere) be added to the 27 720-point Cohn–Li base in ℝ²¹, up to K. Li's bound 3908? Can other
  weights use more words of the punctured Golay code D? A positive answer gives τ₂₁ ≥ 31 561.

## DEFINITIONS
* A *kissing configuration* is a finite set X ⊂ ℝⁿ∖{0} with ∠(x,y) ≥ 60° for x ≠ y. For integer vectors
  this is the exact test ⟨x,y⟩ ≤ 0 or 4⟨x,y⟩² ≤ |x|²|y|². τₙ is the maximum size of such a set.
* **B₂₀** (Cohn–Li odd configuration):
  * E = the Golay code punctured at four coordinates, a [20,12,4] code. Its dual contains 130 octads.
  * B₂₀ consists of the roots ±2eᵢ ± 2eⱼ and the ±1 vectors on an octad with an odd number of minus
    signs. It has 17 400 points.
* **K. Li's dimension-19 configuration:**
  * T = {1,4,7,9}. The base is the 10 668 points of B₂₀ ⊥ 1_T, minus 184 of the 192 points on the
    four octads containing T.
  * P is the 8 restored points with tail +2f₁.
  * Γ is a group of 128 sign changes, and r₁, …, r₁₄ are integer representatives.
  * Total: 10 484 + 1792 = 12 276 points.
* **Dimension 21:**
  * D = the Golay code punctured at three coordinates, a [21,12,5] code. Its 21 weight-5 words
    ("lines") form PG(2,4).
  * B₂₁ = 27 720 Cohn–Li points.
  * x(w, L) = λ_L ∘ (−1)^w, with λ_L = 2 on the line L and 3 elsewhere.
  * The line rule (4): if w and w + P are both used, then L(w), L(w + P) and P are three distinct lines.

## STATUS AND SOURCES (dated 2026-10-14)
* Cohn's table (https://cohn.mit.edu/kissing-numbers, checked 2026-10-14) gives τ₁₉ ≥ 12 276
  (K. Li 2026) and τ₂₁ ≥ 31 288 (G. Long). K. Li's repository (github.com/Felpix-Studios/kissing-number,
  updated 2026-10-12) has τ₂₁ ≥ 31 560. Upper bounds: 24 417 and 53 524.
* History of τ₁₉: Leech–Sloane 10 668; Cohn–Li 11 692 (arXiv:2411.04916); Ho 11 948 (arXiv:2603.10425);
  K. Li 12 276.
* History of τ₂₁: Λ₂₁ 27 720; Cohn–Li 29 768; K. Li 30 779; G. Long 31 259/31 272/31 288; K. Li 31 560.
* Neither question is answered in the other 2026 sources:
  * Kravatskiy (github.com/alexlegeartis/KissingNumbers) proves ceilings only for *flat* sign vectors.
  * D21-Kissing (G. Long) proves the ceiling 31 816 only for the full-base family.
  * Takhanov–Yun and Yang et al. work in dimensions ≥ 25.

## RESEARCH DIRECTION
* **Q19.** Under Γ the 184 deleted points form 23 orbits of size 8, and each conflicts with one orbit
  of new points. Planned steps:
  1. Add one orbit back.
  2. Re-optimise the 14 representatives by sequential-LP minimax over the symmetry-reduced pair list.
  3. Vary the free combinatorial data: the 2⁷ Γ-invariant choices of kept words (one bipartition
     class per cube orbit), the 16 admissible sign groups, smaller groups, and joint motion of P, Q
     and base orbits.
  4. Also try single-point insertion with the stabiliser symmetry, or without any symmetry.
* **Q21.** Observe that the excluded words in each coset of the line code form a dominating set of
  Cay(F₂¹⁰, lines), so the line-weighted maximum is 4·(1024 − γ). Then compute γ, and try free
  per-word weights.

## PITFALLS
* Floating-point "≤ 1/2" proves nothing. Round to integers and check exactly. Minimax values within
  10⁻⁵ of 1/2 need care.
* The symmetry reduction is valid only if the group maps the base onto itself. Check this exactly.
* Do not double count. Distinct points must be distinct vectors (Nodup).
* The records move daily: re-check Cohn's table and the GitHub repositories before claiming.

## CERTIFICATE
For a record: integer data (base as octad/root records, representatives, sign masks). Lean 4 would
check base–base pairs structurally, all reduced pairs by kernel `decide`, group closure, distinctness
and count, without `native_decide`. An independent exact all-pairs Python check would accompany it.
(Outcome: Q19 in its one-point form gives τ₁₉ ≥ 12 277; see README.md.)
