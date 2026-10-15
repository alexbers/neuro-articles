# PROBLEM (A09): simple polygons whose sides lie on n lines — is the bound n·⌊(n−1)/2⌋ attained?

Source: MathOverflow 513798, "What is the maximum k for a k-gon inducible with an n-line arrangement?"
(https://mathoverflow.net/questions/513798, posted 2026-07-31, last edited 2026-08-13; 0 answers as of
2026-10-08).

## TARGET

Let `M(n)` be the largest `k` such that some simple polygon with `k` sides has all its sides lying on
`n` given lines. The asker proved `M(n) ≤ n·⌊(n−1)/2⌋` and wrote: *"I suspect that the bound is exact for
all n … However, I cannot construct an example satisfying the equality for n ≥ 7"*, *"for n = 11, the same
construction does not yield one connected polygon, so the question remains unsolved"*, and *"I wonder if
it is possible to somehow prove that only a genus 1 [= self-intersecting] polygon can satisfy n = 7"*.

Concretely:
1. Decide whether `M(7) = 21`; if not, determine `M(7)`.
2. Decide whether `M(11) = 55`.
3. Decide whether `M(n) = n·⌊(n−1)/2⌋` for all `n` (the asker's conjecture), at least for odd `n`.

## DEFINITIONS

* A *simple polygon* with `k` sides: a cyclic sequence of `k ≥ 3` points `P_0, …, P_{k−1}` such that
  consecutive sides `[P_{j−1},P_j]`, `[P_j,P_{j+1}]` are not collinear (genuine corners), and any two
  non-adjacent sides are disjoint closed segments. (So the boundary is a Jordan curve.)
* The polygon is *inducible with n lines* if there are `n` lines such that every side is contained in one
  of them.
* For odd `n`, `n·⌊(n−1)/2⌋ = n(n−1)/2 = C(n,2)`.
* A *simple arrangement*: no two lines parallel, no three concurrent. Sweeping a generic vertical line
  turns a simple arrangement into a *wiring diagram* = a reduced word of the longest permutation `w0`
  of `S_n` (each pair of wires crosses once, by adjacent transpositions); the same object for
  pseudolines.

## STATUS AND SOURCES (why open)

* MO 513798 has no answers (checked via the StackExchange API on 2026-10-08). Comments: DSM found a 24-gon
  on 8 lines; DSM: "IIRC I could get to 18 for n=7, but not 21"; the asker: "If the computer search can't
  improve the bounds on n=7, then I should probably work on proving impossibility."
* The bound comes from OEIS A050187 (longest closed trail in K_n). Web searches (2026-10-08) for polygons
  through all vertices of a line arrangement / parity obstructions found nothing relevant.
* Not among the 722 manuscripts of the OpenAI release (grep of CONTENTS.md for "arrangement", "polygon").

## RESEARCH DIRECTION

For odd `n`, a `C(n,2)`-gon must use every pair of lines exactly once as consecutive lines, so the
arrangement is simple and **every** intersection point is a vertex; disjointness then forces the sides on
each line to be `[p1p2],[p3p4],…` (consecutive intersection points). So the polygon is a fixed 2-regular
graph `G` (the *alternating 2-factor*) of the arrangement, and the question becomes: can `G` be a single
cycle? Look for an invariant of the number of components of `G` over all arrangements (a sweep / braid-move
argument), and search arrangements by computer when the invariant does not forbid a single cycle.

## PITFALLS

* Self-intersecting ("genus 1") polygons do not count; the asker already has those.
* Three collinear consecutive vertices are not a corner; a side may not be split into two collinear sides.
* Degenerate "lines" `0·x + 0·y = 0` contain every point — must be excluded.
* Floating-point checks of simplicity are not proofs: certify with exact rational arithmetic.
* An impossibility claim for `n = 7` must cover **all** arrangements of 7 lines, not a family, and the
  combinatorial (pseudoline) reduction must be justified.
* Do not claim `M(n)` for all `n`: only the cases actually proved.
* Statement drift: the Lean theorem must state exactly "∃ n lines and a simple polygon with k sides on
  them", with the definition of simplicity visible and auditable.

## CERTIFICATE

* For a construction: explicit integer lines `a x + b y = c` and the vertex list (exact rationals), with
  a Lean check (no Mathlib, kernel evaluation) of: genuine lines, every side on a listed line, genuine
  corners, pairwise disjointness of non-adjacent sides.
* For an impossibility: a complete proof covering every simple (pseudo)line arrangement, plus independent
  exhaustive computation for small `n`.
