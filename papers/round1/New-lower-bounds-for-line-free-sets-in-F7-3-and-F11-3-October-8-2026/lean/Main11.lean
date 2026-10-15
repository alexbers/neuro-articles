/-
  A10: a line-free subset of F_11^3 with 1010 points, i.e. r_11(F_11^3) ≥ 1010.

  F_11^3 = (Z/11Z)^3.  A set is *line-free* if it contains no affine line
  {a + t•d : t ∈ F_11} with d ≠ 0; equivalently it contains no 11-term arithmetic
  progression a, a+d, ..., a+10d with nonzero common difference.
  Previous record: r_11(F_11^3) ≥ 1005 ((p-1)^3+(p-1)/2, Elsholtz et al., arXiv:2310.03382, Thm 1.7 / Table 1).

  Core Lean 4 only (no Mathlib).  All computation is checked by the kernel
  (`decide +kernel`); no `native_decide`.
-/

set_option Elab.async false  -- elaborate sequentially (keeps peak memory low)

/-! ### Definitions used in the main statement -/

/-- Points of `F_11^3`.  Arithmetic in `Fin 11` is arithmetic modulo 11. -/
abbrev Pt := Fin 11 × Fin 11 × Fin 11

/-- Coordinatewise addition in `F_11^3`. -/
def add (a b : Pt) : Pt := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

/-- Scalar multiplication `t • d` in `F_11^3`. -/
def smul (t : Fin 11) (d : Pt) : Pt := (t * d.1, t * d.2.1, t * d.2.2)

/-- `L` contains no full affine line `{a + t • d : t ∈ F_11}` with `d ≠ 0`. -/
def LineFree (L : List Pt) : Prop :=
  ∀ a d : Pt, d ≠ (0, 0, 0) → ∃ t : Fin 11, add a (smul t d) ∉ L

/-- The explicit set: 1010 points `(x, y, z)` of `F_11^3`. -/
def theSet : List Pt := [
  (0, 0, 0), (0, 0, 1), (0, 0, 2), (0, 0, 3), (0, 0, 4), (0, 0, 6), (0, 0, 7), (0, 0, 8),
  (0, 0, 9), (0, 0, 10), (0, 1, 0), (0, 1, 1), (0, 1, 2), (0, 1, 3), (0, 1, 4), (0, 1, 5),
  (0, 1, 6), (0, 1, 9), (0, 1, 10), (0, 2, 0), (0, 2, 1), (0, 2, 2), (0, 2, 3), (0, 2, 4),
  (0, 2, 5), (0, 2, 6), (0, 2, 8), (0, 3, 1), (0, 3, 2), (0, 3, 3), (0, 3, 4), (0, 3, 5),
  (0, 3, 6), (0, 3, 7), (0, 3, 8), (0, 3, 9), (0, 3, 10), (0, 4, 0), (0, 4, 1), (0, 4, 3),
  (0, 4, 4), (0, 4, 6), (0, 4, 7), (0, 4, 8), (0, 4, 9), (0, 4, 10), (0, 5, 0), (0, 5, 1),
  (0, 5, 2), (0, 5, 3), (0, 5, 5), (0, 5, 6), (0, 5, 7), (0, 5, 8), (0, 5, 9), (0, 5, 10),
  (0, 6, 0), (0, 6, 1), (0, 6, 2), (0, 6, 4), (0, 6, 5), (0, 6, 7), (0, 6, 8), (0, 6, 9),
  (0, 7, 0), (0, 7, 1), (0, 7, 3), (0, 7, 4), (0, 7, 6), (0, 7, 7), (0, 7, 9), (0, 7, 10),
  (0, 8, 0), (0, 8, 2), (0, 8, 3), (0, 8, 4), (0, 8, 6), (0, 8, 7), (0, 8, 8), (0, 8, 9),
  (0, 9, 2), (0, 9, 3), (0, 9, 4), (0, 9, 5), (0, 9, 6), (0, 9, 7), (0, 9, 8), (0, 9, 9),
  (0, 9, 10), (0, 10, 0), (0, 10, 1), (0, 10, 2), (0, 10, 4), (0, 10, 5), (0, 10, 6), (0, 10, 7),
  (0, 10, 8), (0, 10, 9), (1, 0, 0), (1, 0, 2), (1, 0, 3), (1, 0, 4), (1, 0, 5), (1, 0, 7),
  (1, 0, 8), (1, 0, 9), (1, 0, 10), (1, 1, 1), (1, 1, 2), (1, 1, 3), (1, 1, 4), (1, 1, 5),
  (1, 1, 6), (1, 1, 9), (1, 1, 10), (1, 2, 0), (1, 2, 1), (1, 2, 2), (1, 2, 4), (1, 2, 5),
  (1, 2, 6), (1, 2, 7), (1, 2, 8), (1, 2, 9), (1, 3, 1), (1, 3, 2), (1, 3, 3), (1, 3, 4),
  (1, 3, 5), (1, 3, 6), (1, 3, 7), (1, 3, 8), (1, 3, 10), (1, 4, 0), (1, 4, 1), (1, 4, 2),
  (1, 4, 4), (1, 4, 5), (1, 4, 6), (1, 4, 7), (1, 4, 9), (1, 4, 10), (1, 5, 0), (1, 5, 1),
  (1, 5, 3), (1, 5, 4), (1, 5, 6), (1, 5, 8), (1, 5, 10), (1, 6, 0), (1, 6, 1), (1, 6, 2),
  (1, 6, 3), (1, 6, 4), (1, 6, 5), (1, 6, 8), (1, 6, 10), (1, 7, 0), (1, 7, 1), (1, 7, 2),
  (1, 7, 3), (1, 7, 4), (1, 7, 6), (1, 7, 7), (1, 7, 8), (1, 7, 10), (1, 8, 0), (1, 8, 1),
  (1, 8, 2), (1, 8, 5), (1, 8, 7), (1, 8, 8), (1, 8, 10), (1, 9, 0), (1, 9, 1), (1, 9, 5),
  (1, 9, 6), (1, 9, 8), (1, 9, 9), (1, 9, 10), (1, 10, 0), (1, 10, 1), (1, 10, 3), (1, 10, 5),
  (1, 10, 6), (1, 10, 7), (1, 10, 8), (1, 10, 9), (1, 10, 10), (2, 0, 0), (2, 0, 1), (2, 0, 2),
  (2, 0, 3), (2, 0, 5), (2, 0, 6), (2, 0, 8), (2, 0, 9), (2, 0, 10), (2, 1, 2), (2, 1, 5),
  (2, 1, 6), (2, 1, 7), (2, 1, 8), (2, 1, 10), (2, 2, 1), (2, 2, 3), (2, 2, 4), (2, 2, 5),
  (2, 2, 6), (2, 2, 7), (2, 2, 8), (2, 2, 9), (2, 3, 0), (2, 3, 3), (2, 3, 4), (2, 3, 6),
  (2, 3, 8), (2, 3, 9), (2, 3, 10), (2, 4, 1), (2, 4, 2), (2, 4, 3), (2, 4, 7), (2, 4, 9),
  (2, 4, 10), (2, 5, 0), (2, 5, 1), (2, 5, 2), (2, 5, 4), (2, 5, 5), (2, 5, 6), (2, 5, 7),
  (2, 5, 8), (2, 5, 9), (2, 6, 0), (2, 6, 1), (2, 6, 2), (2, 6, 3), (2, 6, 4), (2, 6, 5),
  (2, 6, 6), (2, 6, 7), (2, 6, 10), (2, 7, 0), (2, 7, 1), (2, 7, 2), (2, 7, 3), (2, 7, 5),
  (2, 7, 6), (2, 7, 7), (2, 7, 9), (2, 8, 2), (2, 8, 3), (2, 8, 4), (2, 8, 5), (2, 8, 6),
  (2, 8, 8), (2, 8, 10), (2, 9, 0), (2, 9, 1), (2, 9, 2), (2, 9, 4), (2, 9, 5), (2, 9, 6),
  (2, 9, 7), (2, 9, 8), (2, 9, 9), (2, 9, 10), (2, 10, 0), (2, 10, 1), (2, 10, 2), (2, 10, 3),
  (2, 10, 4), (2, 10, 6), (2, 10, 7), (2, 10, 8), (2, 10, 9), (2, 10, 10), (3, 0, 1), (3, 0, 2),
  (3, 0, 3), (3, 0, 4), (3, 0, 6), (3, 0, 7), (3, 0, 9), (3, 0, 10), (3, 1, 0), (3, 1, 1),
  (3, 1, 2), (3, 1, 3), (3, 1, 4), (3, 1, 5), (3, 1, 7), (3, 1, 8), (3, 2, 0), (3, 2, 2),
  (3, 2, 3), (3, 2, 4), (3, 2, 6), (3, 2, 7), (3, 2, 8), (3, 2, 9), (3, 2, 10), (3, 3, 0),
  (3, 3, 1), (3, 3, 2), (3, 3, 5), (3, 3, 6), (3, 3, 8), (3, 3, 10), (3, 4, 0), (3, 4, 1),
  (3, 4, 2), (3, 4, 4), (3, 4, 6), (3, 4, 7), (3, 4, 8), (3, 4, 9), (3, 4, 10), (3, 5, 0),
  (3, 5, 1), (3, 5, 3), (3, 5, 4), (3, 5, 6), (3, 5, 8), (3, 5, 9), (3, 5, 10), (3, 6, 0),
  (3, 6, 1), (3, 6, 2), (3, 6, 3), (3, 6, 4), (3, 6, 5), (3, 6, 7), (3, 6, 8), (3, 6, 10),
  (3, 7, 1), (3, 7, 2), (3, 7, 3), (3, 7, 4), (3, 7, 5), (3, 7, 6), (3, 7, 7), (3, 7, 8),
  (3, 7, 9), (3, 7, 10), (3, 8, 0), (3, 8, 1), (3, 8, 3), (3, 8, 5), (3, 8, 6), (3, 8, 7),
  (3, 8, 8), (3, 8, 9), (3, 9, 0), (3, 9, 1), (3, 9, 2), (3, 9, 3), (3, 9, 5), (3, 9, 6),
  (3, 9, 7), (3, 9, 8), (3, 9, 10), (3, 10, 0), (3, 10, 1), (3, 10, 3), (3, 10, 4), (3, 10, 5),
  (3, 10, 7), (3, 10, 9), (3, 10, 10), (4, 0, 0), (4, 0, 1), (4, 0, 2), (4, 0, 3), (4, 0, 4),
  (4, 0, 5), (4, 0, 7), (4, 0, 8), (4, 0, 9), (4, 1, 1), (4, 1, 2), (4, 1, 3), (4, 1, 4),
  (4, 1, 5), (4, 1, 6), (4, 1, 8), (4, 1, 10), (4, 2, 0), (4, 2, 1), (4, 2, 4), (4, 2, 5),
  (4, 2, 7), (4, 2, 9), (4, 2, 10), (4, 3, 0), (4, 3, 1), (4, 3, 2), (4, 3, 3), (4, 3, 5),
  (4, 3, 6), (4, 3, 8), (4, 3, 10), (4, 4, 0), (4, 4, 1), (4, 4, 2), (4, 4, 3), (4, 4, 4),
  (4, 4, 5), (4, 4, 7), (4, 4, 8), (4, 4, 9), (4, 4, 10), (4, 5, 0), (4, 5, 1), (4, 5, 2),
  (4, 5, 3), (4, 5, 4), (4, 5, 6), (4, 5, 7), (4, 5, 8), (4, 5, 9), (4, 5, 10), (4, 6, 0),
  (4, 6, 1), (4, 6, 2), (4, 6, 3), (4, 6, 4), (4, 6, 5), (4, 6, 6), (4, 6, 7), (4, 6, 9),
  (4, 7, 0), (4, 7, 4), (4, 7, 5), (4, 7, 6), (4, 7, 7), (4, 7, 8), (4, 7, 9), (4, 7, 10),
  (4, 8, 0), (4, 8, 1), (4, 8, 4), (4, 8, 5), (4, 8, 7), (4, 8, 8), (4, 9, 0), (4, 9, 2),
  (4, 9, 4), (4, 9, 6), (4, 9, 7), (4, 9, 8), (4, 9, 9), (4, 9, 10), (4, 10, 1), (4, 10, 2),
  (4, 10, 4), (4, 10, 5), (4, 10, 6), (4, 10, 7), (4, 10, 8), (4, 10, 9), (4, 10, 10), (5, 0, 0),
  (5, 0, 1), (5, 0, 3), (5, 0, 4), (5, 0, 5), (5, 0, 7), (5, 0, 8), (5, 0, 9), (5, 1, 0),
  (5, 1, 2), (5, 1, 3), (5, 1, 4), (5, 1, 5), (5, 1, 6), (5, 1, 7), (5, 1, 8), (5, 1, 9),
  (5, 1, 10), (5, 2, 1), (5, 2, 2), (5, 2, 4), (5, 2, 5), (5, 2, 6), (5, 2, 7), (5, 2, 8),
  (5, 2, 9), (5, 2, 10), (5, 3, 0), (5, 3, 1), (5, 3, 2), (5, 3, 3), (5, 3, 4), (5, 3, 6),
  (5, 3, 7), (5, 3, 8), (5, 3, 9), (5, 4, 0), (5, 4, 2), (5, 4, 3), (5, 4, 4), (5, 4, 5),
  (5, 4, 6), (5, 4, 8), (5, 4, 10), (5, 5, 0), (5, 5, 1), (5, 5, 2), (5, 5, 3), (5, 5, 4),
  (5, 5, 5), (5, 5, 6), (5, 5, 7), (5, 5, 10), (5, 6, 1), (5, 6, 2), (5, 6, 3), (5, 6, 4),
  (5, 6, 5), (5, 6, 6), (5, 6, 8), (5, 6, 9), (5, 6, 10), (5, 7, 0), (5, 7, 1), (5, 7, 4),
  (5, 7, 5), (5, 7, 8), (5, 7, 9), (5, 7, 10), (5, 8, 0), (5, 8, 1), (5, 8, 2), (5, 8, 3),
  (5, 8, 6), (5, 8, 7), (5, 8, 8), (5, 8, 9), (5, 8, 10), (5, 9, 0), (5, 9, 1), (5, 9, 2),
  (5, 9, 3), (5, 9, 7), (5, 9, 8), (5, 9, 10), (5, 10, 0), (5, 10, 1), (5, 10, 2), (5, 10, 5),
  (5, 10, 6), (5, 10, 7), (5, 10, 9), (5, 10, 10), (6, 0, 1), (6, 0, 2), (6, 0, 3), (6, 0, 6),
  (6, 0, 7), (6, 0, 8), (6, 0, 9), (6, 0, 10), (6, 1, 0), (6, 1, 1), (6, 1, 3), (6, 1, 5),
  (6, 1, 6), (6, 1, 7), (6, 1, 8), (6, 1, 9), (6, 1, 10), (6, 2, 0), (6, 2, 1), (6, 2, 2),
  (6, 2, 5), (6, 2, 6), (6, 2, 7), (6, 2, 8), (6, 2, 9), (6, 2, 10), (6, 3, 0), (6, 3, 1),
  (6, 3, 3), (6, 3, 4), (6, 3, 5), (6, 3, 7), (6, 3, 8), (6, 3, 9), (6, 3, 10), (6, 4, 0),
  (6, 4, 2), (6, 4, 3), (6, 4, 4), (6, 4, 5), (6, 4, 6), (6, 4, 7), (6, 4, 9), (6, 5, 0),
  (6, 5, 1), (6, 5, 2), (6, 5, 3), (6, 5, 4), (6, 5, 5), (6, 5, 6), (6, 5, 7), (6, 5, 8),
  (6, 5, 9), (6, 6, 0), (6, 6, 3), (6, 6, 4), (6, 6, 5), (6, 6, 6), (6, 6, 8), (6, 7, 0),
  (6, 7, 1), (6, 7, 2), (6, 7, 4), (6, 7, 5), (6, 7, 6), (6, 7, 7), (6, 7, 8), (6, 7, 10),
  (6, 8, 0), (6, 8, 1), (6, 8, 2), (6, 8, 3), (6, 8, 4), (6, 8, 6), (6, 8, 7), (6, 8, 9),
  (6, 8, 10), (6, 9, 0), (6, 9, 1), (6, 9, 2), (6, 9, 4), (6, 9, 5), (6, 9, 6), (6, 9, 8),
  (6, 9, 9), (6, 9, 10), (6, 10, 0), (6, 10, 1), (6, 10, 2), (6, 10, 5), (6, 10, 7), (6, 10, 8),
  (6, 10, 10), (7, 0, 0), (7, 0, 1), (7, 0, 2), (7, 0, 3), (7, 0, 5), (7, 0, 6), (7, 0, 7),
  (7, 0, 8), (7, 0, 10), (7, 1, 0), (7, 1, 1), (7, 1, 2), (7, 1, 4), (7, 1, 5), (7, 1, 6),
  (7, 1, 7), (7, 1, 8), (7, 1, 9), (7, 1, 10), (7, 2, 0), (7, 2, 1), (7, 2, 2), (7, 2, 3),
  (7, 2, 7), (7, 2, 8), (7, 2, 9), (7, 2, 10), (7, 3, 0), (7, 3, 1), (7, 3, 2), (7, 3, 3),
  (7, 3, 4), (7, 3, 6), (7, 3, 8), (7, 3, 10), (7, 4, 0), (7, 4, 1), (7, 4, 2), (7, 4, 5),
  (7, 4, 6), (7, 4, 7), (7, 4, 8), (7, 4, 10), (7, 5, 4), (7, 5, 5), (7, 5, 6), (7, 5, 7),
  (7, 5, 8), (7, 5, 10), (7, 6, 0), (7, 6, 3), (7, 6, 4), (7, 6, 5), (7, 6, 6), (7, 6, 7),
  (7, 6, 9), (7, 7, 2), (7, 7, 3), (7, 7, 5), (7, 7, 6), (7, 7, 8), (7, 7, 9), (7, 7, 10),
  (7, 8, 1), (7, 8, 2), (7, 8, 3), (7, 8, 4), (7, 8, 5), (7, 8, 7), (7, 8, 8), (7, 8, 9),
  (7, 9, 0), (7, 9, 1), (7, 9, 2), (7, 9, 3), (7, 9, 4), (7, 9, 5), (7, 9, 6), (7, 9, 7),
  (7, 9, 9), (7, 10, 1), (7, 10, 2), (7, 10, 4), (7, 10, 5), (7, 10, 6), (7, 10, 7), (8, 0, 1),
  (8, 0, 3), (8, 0, 4), (8, 0, 5), (8, 0, 6), (8, 0, 7), (8, 0, 8), (8, 0, 9), (8, 0, 10),
  (8, 1, 0), (8, 1, 1), (8, 1, 2), (8, 1, 3), (8, 1, 4), (8, 1, 5), (8, 1, 6), (8, 1, 7),
  (8, 1, 8), (8, 1, 9), (8, 2, 0), (8, 2, 1), (8, 2, 2), (8, 2, 3), (8, 2, 4), (8, 2, 5),
  (8, 2, 7), (8, 2, 8), (8, 2, 9), (8, 2, 10), (8, 3, 1), (8, 3, 2), (8, 3, 3), (8, 3, 4),
  (8, 3, 5), (8, 3, 6), (8, 3, 7), (8, 3, 9), (8, 4, 0), (8, 4, 1), (8, 4, 2), (8, 4, 3),
  (8, 4, 4), (8, 4, 5), (8, 4, 6), (8, 4, 9), (8, 4, 10), (8, 5, 2), (8, 5, 3), (8, 5, 4),
  (8, 5, 5), (8, 5, 7), (8, 5, 9), (8, 5, 10), (8, 6, 0), (8, 6, 1), (8, 6, 2), (8, 6, 4),
  (8, 6, 6), (8, 6, 7), (8, 6, 9), (8, 6, 10), (8, 7, 0), (8, 7, 1), (8, 7, 2), (8, 7, 3),
  (8, 7, 6), (8, 7, 7), (8, 7, 8), (8, 7, 9), (8, 7, 10), (8, 8, 0), (8, 8, 2), (8, 8, 4),
  (8, 8, 5), (8, 8, 6), (8, 8, 8), (8, 8, 9), (8, 8, 10), (8, 9, 0), (8, 9, 1), (8, 9, 3),
  (8, 9, 4), (8, 9, 6), (8, 9, 7), (8, 9, 8), (8, 9, 10), (8, 10, 2), (8, 10, 3), (8, 10, 4),
  (8, 10, 5), (8, 10, 6), (8, 10, 8), (8, 10, 9), (8, 10, 10), (9, 0, 0), (9, 0, 5), (9, 0, 6),
  (9, 0, 7), (9, 0, 8), (9, 0, 9), (9, 0, 10), (9, 1, 0), (9, 1, 1), (9, 1, 3), (9, 1, 4),
  (9, 1, 6), (9, 1, 7), (9, 1, 8), (9, 1, 9), (9, 1, 10), (9, 2, 0), (9, 2, 2), (9, 2, 3),
  (9, 2, 4), (9, 2, 5), (9, 2, 6), (9, 2, 8), (9, 2, 9), (9, 2, 10), (9, 3, 1), (9, 3, 2),
  (9, 3, 3), (9, 3, 4), (9, 3, 5), (9, 3, 6), (9, 3, 7), (9, 3, 8), (9, 3, 10), (9, 4, 1),
  (9, 4, 2), (9, 4, 3), (9, 4, 4), (9, 4, 5), (9, 4, 6), (9, 4, 7), (9, 4, 8), (9, 4, 9),
  (9, 5, 0), (9, 5, 1), (9, 5, 3), (9, 5, 4), (9, 5, 6), (9, 5, 7), (9, 5, 8), (9, 5, 10),
  (9, 6, 0), (9, 6, 1), (9, 6, 2), (9, 6, 3), (9, 6, 5), (9, 6, 6), (9, 6, 7), (9, 6, 9),
  (9, 6, 10), (9, 7, 0), (9, 7, 2), (9, 7, 3), (9, 7, 5), (9, 7, 8), (9, 7, 9), (9, 7, 10),
  (9, 8, 0), (9, 8, 2), (9, 8, 3), (9, 8, 4), (9, 8, 5), (9, 8, 7), (9, 8, 9), (9, 8, 10),
  (9, 9, 0), (9, 9, 2), (9, 9, 3), (9, 9, 4), (9, 9, 6), (9, 9, 7), (9, 9, 8), (9, 9, 9),
  (9, 9, 10), (9, 10, 0), (9, 10, 2), (9, 10, 3), (9, 10, 5), (9, 10, 6), (9, 10, 7), (9, 10, 8),
  (9, 10, 9), (9, 10, 10), (10, 0, 0), (10, 0, 1), (10, 0, 3), (10, 0, 5), (10, 0, 8), (10, 0, 9),
  (10, 0, 10), (10, 1, 0), (10, 1, 1), (10, 1, 2), (10, 1, 3), (10, 1, 4), (10, 1, 7), (10, 1, 8),
  (10, 1, 9), (10, 2, 1), (10, 2, 2), (10, 2, 5), (10, 2, 6), (10, 2, 7), (10, 2, 8), (10, 2, 9),
  (10, 2, 10), (10, 3, 0), (10, 3, 1), (10, 3, 2), (10, 3, 4), (10, 3, 5), (10, 3, 6), (10, 3, 7),
  (10, 3, 8), (10, 4, 0), (10, 4, 1), (10, 4, 3), (10, 4, 5), (10, 4, 6), (10, 4, 7), (10, 4, 8),
  (10, 4, 9), (10, 4, 10), (10, 5, 0), (10, 5, 2), (10, 5, 4), (10, 5, 5), (10, 5, 6), (10, 5, 7),
  (10, 5, 8), (10, 5, 9), (10, 5, 10), (10, 6, 1), (10, 6, 2), (10, 6, 3), (10, 6, 4), (10, 6, 6),
  (10, 6, 7), (10, 6, 9), (10, 6, 10), (10, 7, 1), (10, 7, 3), (10, 7, 4), (10, 7, 5), (10, 7, 6),
  (10, 7, 8), (10, 7, 9), (10, 8, 0), (10, 8, 1), (10, 8, 2), (10, 8, 4), (10, 8, 5), (10, 8, 6),
  (10, 8, 7), (10, 8, 8), (10, 8, 10), (10, 9, 2), (10, 9, 3), (10, 9, 5), (10, 9, 6), (10, 9, 7),
  (10, 9, 9), (10, 9, 10), (10, 10, 0), (10, 10, 1), (10, 10, 4), (10, 10, 5), (10, 10, 6), (10, 10, 8),
  (10, 10, 9), (10, 10, 10)]

/-! ### Computational verification (kernel) -/

/-- All points of `F_11^3`. -/
def allPts : List Pt :=
  (List.finRange 11).flatMap fun x => (List.finRange 11).flatMap fun y =>
    (List.finRange 11).map fun z => (x, y, z)

theorem mem_allPts (q : Pt) : q ∈ allPts := by
  obtain ⟨x, y, z⟩ := q
  simp [allPts, List.mem_flatMap, List.mem_map, List.mem_finRange]

/-- The points with first two coordinates `x, y`. -/
def row (x y : Fin 11) : List Pt := (List.finRange 11).map fun z => (x, y, z)

theorem mem_row (x y z : Fin 11) : (x, y, z) ∈ row x y := by
  simp [row, List.mem_map, List.mem_finRange]

/-- Lexicographic index of a point, in `[0, 1331)` (the position of the point in `allPts`). -/
def lex (q : Pt) : Nat := 121 * q.1.val + 11 * q.2.1.val + q.2.2.val

theorem allPts_lex : allPts.map lex = List.range 1331 := by decide +kernel

theorem allPts_nodup : allPts.Nodup := by
  have h : (allPts.map lex).Nodup := by rw [allPts_lex]; exact List.nodup_range
  unfold List.Nodup at h ⊢
  rw [List.pairwise_map] at h
  exact h.imp (fun {a b} (hne : lex a ≠ lex b) (e : a = b) => hne (by rw [e]))

/-- Bitmask of `theSet` (bit `lex q` is set iff `q ∈ theSet`), used for fast lookup. -/
def mask : Nat := 43665863577807083697934893537496458572205374700389626664762114020639851532220610941695651340982139225526950261205232581781507329070508262853134536175111198015952972030661216288417318924057793624948103012092458289717180408531125882943838397838790277399861960576263563441953219889599661784062269280707138613641567030372555873676366534340989561723939081746428740770863154160742988683044246495340778487775

def inMask (q : Pt) : Bool := mask.testBit (lex q)

/-- The explicit list is exactly the set of points selected by the mask, in `allPts` order. -/
theorem theSet_eq : theSet = allPts.filter inMask := by decide +kernel

theorem mem_iff (q : Pt) : q ∈ theSet ↔ inMask q = true := by
  rw [theSet_eq, List.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_allPts q, h⟩⟩

/-- Leading (first nonzero) coordinate of a vector. -/
def lead (d : Pt) : Fin 11 := if d.1 ≠ 0 then d.1 else if d.2.1 ≠ 0 then d.2.1 else d.2.2

/-- `d` is normalised: its leading coordinate is `1`. -/
def isNorm (d : Pt) : Bool := lead d == 1

/-- Multiplicative inverse in `Fin 11` found by search (only used for `u ≠ 0`). -/
def finv (u : Fin 11) : Fin 11 := ((List.finRange 11).find? (fun v => u * v == 1)).getD 0

/-- Every nonzero direction becomes normalised after scaling by the inverse of its leading
coordinate (so every line has a normalised direction vector). -/
theorem norm_ok :
    allPts.all (fun d => d == (0, 0, 0) || isNorm (smul (finv (lead d)) d)) = true := by
  decide +kernel

theorem fin_mul_assoc : ∀ a b c : Fin 11, a * b * c = a * (b * c) := by decide +kernel

theorem smul_smul (s u : Fin 11) (d : Pt) : smul s (smul u d) = smul (s * u) d := by
  obtain ⟨x, y, z⟩ := d
  simp only [smul, fin_mul_assoc]

/-- For the base point `a`: every normalised direction `d` has some `t` with `a + t•d ∉ theSet`. -/
def checkAt (a : Pt) : Bool :=
  allPts.all fun d => !isNorm d || (List.finRange 11).any fun t => !inMask (add a (smul t d))

theorem row_0_0_ok : (row 0 0).all checkAt = true := by decide +kernel
theorem row_0_1_ok : (row 0 1).all checkAt = true := by decide +kernel
theorem row_0_2_ok : (row 0 2).all checkAt = true := by decide +kernel
theorem row_0_3_ok : (row 0 3).all checkAt = true := by decide +kernel
theorem row_0_4_ok : (row 0 4).all checkAt = true := by decide +kernel
theorem row_0_5_ok : (row 0 5).all checkAt = true := by decide +kernel
theorem row_0_6_ok : (row 0 6).all checkAt = true := by decide +kernel
theorem row_0_7_ok : (row 0 7).all checkAt = true := by decide +kernel
theorem row_0_8_ok : (row 0 8).all checkAt = true := by decide +kernel
theorem row_0_9_ok : (row 0 9).all checkAt = true := by decide +kernel
theorem row_0_10_ok : (row 0 10).all checkAt = true := by decide +kernel
theorem rowx_0_ok (y : Fin 11) : (row 0 y).all checkAt = true := by
  match y with
  | ⟨0, _⟩ => exact row_0_0_ok
  | ⟨1, _⟩ => exact row_0_1_ok
  | ⟨2, _⟩ => exact row_0_2_ok
  | ⟨3, _⟩ => exact row_0_3_ok
  | ⟨4, _⟩ => exact row_0_4_ok
  | ⟨5, _⟩ => exact row_0_5_ok
  | ⟨6, _⟩ => exact row_0_6_ok
  | ⟨7, _⟩ => exact row_0_7_ok
  | ⟨8, _⟩ => exact row_0_8_ok
  | ⟨9, _⟩ => exact row_0_9_ok
  | ⟨10, _⟩ => exact row_0_10_ok
  | ⟨n + 11, h⟩ => exact absurd h (by omega)

theorem row_1_0_ok : (row 1 0).all checkAt = true := by decide +kernel
theorem row_1_1_ok : (row 1 1).all checkAt = true := by decide +kernel
theorem row_1_2_ok : (row 1 2).all checkAt = true := by decide +kernel
theorem row_1_3_ok : (row 1 3).all checkAt = true := by decide +kernel
theorem row_1_4_ok : (row 1 4).all checkAt = true := by decide +kernel
theorem row_1_5_ok : (row 1 5).all checkAt = true := by decide +kernel
theorem row_1_6_ok : (row 1 6).all checkAt = true := by decide +kernel
theorem row_1_7_ok : (row 1 7).all checkAt = true := by decide +kernel
theorem row_1_8_ok : (row 1 8).all checkAt = true := by decide +kernel
theorem row_1_9_ok : (row 1 9).all checkAt = true := by decide +kernel
theorem row_1_10_ok : (row 1 10).all checkAt = true := by decide +kernel
theorem rowx_1_ok (y : Fin 11) : (row 1 y).all checkAt = true := by
  match y with
  | ⟨0, _⟩ => exact row_1_0_ok
  | ⟨1, _⟩ => exact row_1_1_ok
  | ⟨2, _⟩ => exact row_1_2_ok
  | ⟨3, _⟩ => exact row_1_3_ok
  | ⟨4, _⟩ => exact row_1_4_ok
  | ⟨5, _⟩ => exact row_1_5_ok
  | ⟨6, _⟩ => exact row_1_6_ok
  | ⟨7, _⟩ => exact row_1_7_ok
  | ⟨8, _⟩ => exact row_1_8_ok
  | ⟨9, _⟩ => exact row_1_9_ok
  | ⟨10, _⟩ => exact row_1_10_ok
  | ⟨n + 11, h⟩ => exact absurd h (by omega)

theorem row_2_0_ok : (row 2 0).all checkAt = true := by decide +kernel
theorem row_2_1_ok : (row 2 1).all checkAt = true := by decide +kernel
theorem row_2_2_ok : (row 2 2).all checkAt = true := by decide +kernel
theorem row_2_3_ok : (row 2 3).all checkAt = true := by decide +kernel
theorem row_2_4_ok : (row 2 4).all checkAt = true := by decide +kernel
theorem row_2_5_ok : (row 2 5).all checkAt = true := by decide +kernel
theorem row_2_6_ok : (row 2 6).all checkAt = true := by decide +kernel
theorem row_2_7_ok : (row 2 7).all checkAt = true := by decide +kernel
theorem row_2_8_ok : (row 2 8).all checkAt = true := by decide +kernel
theorem row_2_9_ok : (row 2 9).all checkAt = true := by decide +kernel
theorem row_2_10_ok : (row 2 10).all checkAt = true := by decide +kernel
theorem rowx_2_ok (y : Fin 11) : (row 2 y).all checkAt = true := by
  match y with
  | ⟨0, _⟩ => exact row_2_0_ok
  | ⟨1, _⟩ => exact row_2_1_ok
  | ⟨2, _⟩ => exact row_2_2_ok
  | ⟨3, _⟩ => exact row_2_3_ok
  | ⟨4, _⟩ => exact row_2_4_ok
  | ⟨5, _⟩ => exact row_2_5_ok
  | ⟨6, _⟩ => exact row_2_6_ok
  | ⟨7, _⟩ => exact row_2_7_ok
  | ⟨8, _⟩ => exact row_2_8_ok
  | ⟨9, _⟩ => exact row_2_9_ok
  | ⟨10, _⟩ => exact row_2_10_ok
  | ⟨n + 11, h⟩ => exact absurd h (by omega)

theorem row_3_0_ok : (row 3 0).all checkAt = true := by decide +kernel
theorem row_3_1_ok : (row 3 1).all checkAt = true := by decide +kernel
theorem row_3_2_ok : (row 3 2).all checkAt = true := by decide +kernel
theorem row_3_3_ok : (row 3 3).all checkAt = true := by decide +kernel
theorem row_3_4_ok : (row 3 4).all checkAt = true := by decide +kernel
theorem row_3_5_ok : (row 3 5).all checkAt = true := by decide +kernel
theorem row_3_6_ok : (row 3 6).all checkAt = true := by decide +kernel
theorem row_3_7_ok : (row 3 7).all checkAt = true := by decide +kernel
theorem row_3_8_ok : (row 3 8).all checkAt = true := by decide +kernel
theorem row_3_9_ok : (row 3 9).all checkAt = true := by decide +kernel
theorem row_3_10_ok : (row 3 10).all checkAt = true := by decide +kernel
theorem rowx_3_ok (y : Fin 11) : (row 3 y).all checkAt = true := by
  match y with
  | ⟨0, _⟩ => exact row_3_0_ok
  | ⟨1, _⟩ => exact row_3_1_ok
  | ⟨2, _⟩ => exact row_3_2_ok
  | ⟨3, _⟩ => exact row_3_3_ok
  | ⟨4, _⟩ => exact row_3_4_ok
  | ⟨5, _⟩ => exact row_3_5_ok
  | ⟨6, _⟩ => exact row_3_6_ok
  | ⟨7, _⟩ => exact row_3_7_ok
  | ⟨8, _⟩ => exact row_3_8_ok
  | ⟨9, _⟩ => exact row_3_9_ok
  | ⟨10, _⟩ => exact row_3_10_ok
  | ⟨n + 11, h⟩ => exact absurd h (by omega)

theorem row_4_0_ok : (row 4 0).all checkAt = true := by decide +kernel
theorem row_4_1_ok : (row 4 1).all checkAt = true := by decide +kernel
theorem row_4_2_ok : (row 4 2).all checkAt = true := by decide +kernel
theorem row_4_3_ok : (row 4 3).all checkAt = true := by decide +kernel
theorem row_4_4_ok : (row 4 4).all checkAt = true := by decide +kernel
theorem row_4_5_ok : (row 4 5).all checkAt = true := by decide +kernel
theorem row_4_6_ok : (row 4 6).all checkAt = true := by decide +kernel
theorem row_4_7_ok : (row 4 7).all checkAt = true := by decide +kernel
theorem row_4_8_ok : (row 4 8).all checkAt = true := by decide +kernel
theorem row_4_9_ok : (row 4 9).all checkAt = true := by decide +kernel
theorem row_4_10_ok : (row 4 10).all checkAt = true := by decide +kernel
theorem rowx_4_ok (y : Fin 11) : (row 4 y).all checkAt = true := by
  match y with
  | ⟨0, _⟩ => exact row_4_0_ok
  | ⟨1, _⟩ => exact row_4_1_ok
  | ⟨2, _⟩ => exact row_4_2_ok
  | ⟨3, _⟩ => exact row_4_3_ok
  | ⟨4, _⟩ => exact row_4_4_ok
  | ⟨5, _⟩ => exact row_4_5_ok
  | ⟨6, _⟩ => exact row_4_6_ok
  | ⟨7, _⟩ => exact row_4_7_ok
  | ⟨8, _⟩ => exact row_4_8_ok
  | ⟨9, _⟩ => exact row_4_9_ok
  | ⟨10, _⟩ => exact row_4_10_ok
  | ⟨n + 11, h⟩ => exact absurd h (by omega)

theorem row_5_0_ok : (row 5 0).all checkAt = true := by decide +kernel
theorem row_5_1_ok : (row 5 1).all checkAt = true := by decide +kernel
theorem row_5_2_ok : (row 5 2).all checkAt = true := by decide +kernel
theorem row_5_3_ok : (row 5 3).all checkAt = true := by decide +kernel
theorem row_5_4_ok : (row 5 4).all checkAt = true := by decide +kernel
theorem row_5_5_ok : (row 5 5).all checkAt = true := by decide +kernel
theorem row_5_6_ok : (row 5 6).all checkAt = true := by decide +kernel
theorem row_5_7_ok : (row 5 7).all checkAt = true := by decide +kernel
theorem row_5_8_ok : (row 5 8).all checkAt = true := by decide +kernel
theorem row_5_9_ok : (row 5 9).all checkAt = true := by decide +kernel
theorem row_5_10_ok : (row 5 10).all checkAt = true := by decide +kernel
theorem rowx_5_ok (y : Fin 11) : (row 5 y).all checkAt = true := by
  match y with
  | ⟨0, _⟩ => exact row_5_0_ok
  | ⟨1, _⟩ => exact row_5_1_ok
  | ⟨2, _⟩ => exact row_5_2_ok
  | ⟨3, _⟩ => exact row_5_3_ok
  | ⟨4, _⟩ => exact row_5_4_ok
  | ⟨5, _⟩ => exact row_5_5_ok
  | ⟨6, _⟩ => exact row_5_6_ok
  | ⟨7, _⟩ => exact row_5_7_ok
  | ⟨8, _⟩ => exact row_5_8_ok
  | ⟨9, _⟩ => exact row_5_9_ok
  | ⟨10, _⟩ => exact row_5_10_ok
  | ⟨n + 11, h⟩ => exact absurd h (by omega)

theorem row_6_0_ok : (row 6 0).all checkAt = true := by decide +kernel
theorem row_6_1_ok : (row 6 1).all checkAt = true := by decide +kernel
theorem row_6_2_ok : (row 6 2).all checkAt = true := by decide +kernel
theorem row_6_3_ok : (row 6 3).all checkAt = true := by decide +kernel
theorem row_6_4_ok : (row 6 4).all checkAt = true := by decide +kernel
theorem row_6_5_ok : (row 6 5).all checkAt = true := by decide +kernel
theorem row_6_6_ok : (row 6 6).all checkAt = true := by decide +kernel
theorem row_6_7_ok : (row 6 7).all checkAt = true := by decide +kernel
theorem row_6_8_ok : (row 6 8).all checkAt = true := by decide +kernel
theorem row_6_9_ok : (row 6 9).all checkAt = true := by decide +kernel
theorem row_6_10_ok : (row 6 10).all checkAt = true := by decide +kernel
theorem rowx_6_ok (y : Fin 11) : (row 6 y).all checkAt = true := by
  match y with
  | ⟨0, _⟩ => exact row_6_0_ok
  | ⟨1, _⟩ => exact row_6_1_ok
  | ⟨2, _⟩ => exact row_6_2_ok
  | ⟨3, _⟩ => exact row_6_3_ok
  | ⟨4, _⟩ => exact row_6_4_ok
  | ⟨5, _⟩ => exact row_6_5_ok
  | ⟨6, _⟩ => exact row_6_6_ok
  | ⟨7, _⟩ => exact row_6_7_ok
  | ⟨8, _⟩ => exact row_6_8_ok
  | ⟨9, _⟩ => exact row_6_9_ok
  | ⟨10, _⟩ => exact row_6_10_ok
  | ⟨n + 11, h⟩ => exact absurd h (by omega)

theorem row_7_0_ok : (row 7 0).all checkAt = true := by decide +kernel
theorem row_7_1_ok : (row 7 1).all checkAt = true := by decide +kernel
theorem row_7_2_ok : (row 7 2).all checkAt = true := by decide +kernel
theorem row_7_3_ok : (row 7 3).all checkAt = true := by decide +kernel
theorem row_7_4_ok : (row 7 4).all checkAt = true := by decide +kernel
theorem row_7_5_ok : (row 7 5).all checkAt = true := by decide +kernel
theorem row_7_6_ok : (row 7 6).all checkAt = true := by decide +kernel
theorem row_7_7_ok : (row 7 7).all checkAt = true := by decide +kernel
theorem row_7_8_ok : (row 7 8).all checkAt = true := by decide +kernel
theorem row_7_9_ok : (row 7 9).all checkAt = true := by decide +kernel
theorem row_7_10_ok : (row 7 10).all checkAt = true := by decide +kernel
theorem rowx_7_ok (y : Fin 11) : (row 7 y).all checkAt = true := by
  match y with
  | ⟨0, _⟩ => exact row_7_0_ok
  | ⟨1, _⟩ => exact row_7_1_ok
  | ⟨2, _⟩ => exact row_7_2_ok
  | ⟨3, _⟩ => exact row_7_3_ok
  | ⟨4, _⟩ => exact row_7_4_ok
  | ⟨5, _⟩ => exact row_7_5_ok
  | ⟨6, _⟩ => exact row_7_6_ok
  | ⟨7, _⟩ => exact row_7_7_ok
  | ⟨8, _⟩ => exact row_7_8_ok
  | ⟨9, _⟩ => exact row_7_9_ok
  | ⟨10, _⟩ => exact row_7_10_ok
  | ⟨n + 11, h⟩ => exact absurd h (by omega)

theorem row_8_0_ok : (row 8 0).all checkAt = true := by decide +kernel
theorem row_8_1_ok : (row 8 1).all checkAt = true := by decide +kernel
theorem row_8_2_ok : (row 8 2).all checkAt = true := by decide +kernel
theorem row_8_3_ok : (row 8 3).all checkAt = true := by decide +kernel
theorem row_8_4_ok : (row 8 4).all checkAt = true := by decide +kernel
theorem row_8_5_ok : (row 8 5).all checkAt = true := by decide +kernel
theorem row_8_6_ok : (row 8 6).all checkAt = true := by decide +kernel
theorem row_8_7_ok : (row 8 7).all checkAt = true := by decide +kernel
theorem row_8_8_ok : (row 8 8).all checkAt = true := by decide +kernel
theorem row_8_9_ok : (row 8 9).all checkAt = true := by decide +kernel
theorem row_8_10_ok : (row 8 10).all checkAt = true := by decide +kernel
theorem rowx_8_ok (y : Fin 11) : (row 8 y).all checkAt = true := by
  match y with
  | ⟨0, _⟩ => exact row_8_0_ok
  | ⟨1, _⟩ => exact row_8_1_ok
  | ⟨2, _⟩ => exact row_8_2_ok
  | ⟨3, _⟩ => exact row_8_3_ok
  | ⟨4, _⟩ => exact row_8_4_ok
  | ⟨5, _⟩ => exact row_8_5_ok
  | ⟨6, _⟩ => exact row_8_6_ok
  | ⟨7, _⟩ => exact row_8_7_ok
  | ⟨8, _⟩ => exact row_8_8_ok
  | ⟨9, _⟩ => exact row_8_9_ok
  | ⟨10, _⟩ => exact row_8_10_ok
  | ⟨n + 11, h⟩ => exact absurd h (by omega)

theorem row_9_0_ok : (row 9 0).all checkAt = true := by decide +kernel
theorem row_9_1_ok : (row 9 1).all checkAt = true := by decide +kernel
theorem row_9_2_ok : (row 9 2).all checkAt = true := by decide +kernel
theorem row_9_3_ok : (row 9 3).all checkAt = true := by decide +kernel
theorem row_9_4_ok : (row 9 4).all checkAt = true := by decide +kernel
theorem row_9_5_ok : (row 9 5).all checkAt = true := by decide +kernel
theorem row_9_6_ok : (row 9 6).all checkAt = true := by decide +kernel
theorem row_9_7_ok : (row 9 7).all checkAt = true := by decide +kernel
theorem row_9_8_ok : (row 9 8).all checkAt = true := by decide +kernel
theorem row_9_9_ok : (row 9 9).all checkAt = true := by decide +kernel
theorem row_9_10_ok : (row 9 10).all checkAt = true := by decide +kernel
theorem rowx_9_ok (y : Fin 11) : (row 9 y).all checkAt = true := by
  match y with
  | ⟨0, _⟩ => exact row_9_0_ok
  | ⟨1, _⟩ => exact row_9_1_ok
  | ⟨2, _⟩ => exact row_9_2_ok
  | ⟨3, _⟩ => exact row_9_3_ok
  | ⟨4, _⟩ => exact row_9_4_ok
  | ⟨5, _⟩ => exact row_9_5_ok
  | ⟨6, _⟩ => exact row_9_6_ok
  | ⟨7, _⟩ => exact row_9_7_ok
  | ⟨8, _⟩ => exact row_9_8_ok
  | ⟨9, _⟩ => exact row_9_9_ok
  | ⟨10, _⟩ => exact row_9_10_ok
  | ⟨n + 11, h⟩ => exact absurd h (by omega)

theorem row_10_0_ok : (row 10 0).all checkAt = true := by decide +kernel
theorem row_10_1_ok : (row 10 1).all checkAt = true := by decide +kernel
theorem row_10_2_ok : (row 10 2).all checkAt = true := by decide +kernel
theorem row_10_3_ok : (row 10 3).all checkAt = true := by decide +kernel
theorem row_10_4_ok : (row 10 4).all checkAt = true := by decide +kernel
theorem row_10_5_ok : (row 10 5).all checkAt = true := by decide +kernel
theorem row_10_6_ok : (row 10 6).all checkAt = true := by decide +kernel
theorem row_10_7_ok : (row 10 7).all checkAt = true := by decide +kernel
theorem row_10_8_ok : (row 10 8).all checkAt = true := by decide +kernel
theorem row_10_9_ok : (row 10 9).all checkAt = true := by decide +kernel
theorem row_10_10_ok : (row 10 10).all checkAt = true := by decide +kernel
theorem rowx_10_ok (y : Fin 11) : (row 10 y).all checkAt = true := by
  match y with
  | ⟨0, _⟩ => exact row_10_0_ok
  | ⟨1, _⟩ => exact row_10_1_ok
  | ⟨2, _⟩ => exact row_10_2_ok
  | ⟨3, _⟩ => exact row_10_3_ok
  | ⟨4, _⟩ => exact row_10_4_ok
  | ⟨5, _⟩ => exact row_10_5_ok
  | ⟨6, _⟩ => exact row_10_6_ok
  | ⟨7, _⟩ => exact row_10_7_ok
  | ⟨8, _⟩ => exact row_10_8_ok
  | ⟨9, _⟩ => exact row_10_9_ok
  | ⟨10, _⟩ => exact row_10_10_ok
  | ⟨n + 11, h⟩ => exact absurd h (by omega)

theorem checkAt_ok (a : Pt) : checkAt a = true := by
  obtain ⟨x, y, z⟩ := a
  have hx : (row x y).all checkAt = true := by
    match x with
    | ⟨0, _⟩ => exact rowx_0_ok y
    | ⟨1, _⟩ => exact rowx_1_ok y
    | ⟨2, _⟩ => exact rowx_2_ok y
    | ⟨3, _⟩ => exact rowx_3_ok y
    | ⟨4, _⟩ => exact rowx_4_ok y
    | ⟨5, _⟩ => exact rowx_5_ok y
    | ⟨6, _⟩ => exact rowx_6_ok y
    | ⟨7, _⟩ => exact rowx_7_ok y
    | ⟨8, _⟩ => exact rowx_8_ok y
    | ⟨9, _⟩ => exact rowx_9_ok y
    | ⟨10, _⟩ => exact rowx_10_ok y
    | ⟨n + 11, h⟩ => exact absurd h (by omega)
  exact List.all_eq_true.mp hx _ (mem_row x y z)

theorem lineFree_theSet : LineFree theSet := by
  intro a d hd
  have hn := List.all_eq_true.mp norm_ok d (mem_allPts d)
  simp only [Bool.or_eq_true, beq_iff_eq] at hn
  rcases hn with hn | hn
  · exact absurd hn hd
  · have h := List.all_eq_true.mp (checkAt_ok a) _ (mem_allPts (smul (finv (lead d)) d))
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · rw [hn] at h; exact absurd h (by decide)
    · obtain ⟨t, -, ht⟩ := List.any_eq_true.mp h
      refine ⟨t * finv (lead d), ?_⟩
      rw [mem_iff, ← smul_smul]
      simpa using ht

theorem theSet_nodup : theSet.Nodup := by
  rw [theSet_eq]; exact allPts_nodup.filter _

theorem theSet_length : theSet.length = 1010 := by decide +kernel

/-! ### Main theorem -/

/-- **Main theorem** (`r_11(F_11^3) ≥ 1010`): there is a list of 1010 pairwise distinct points of
`F_11^3` containing no full affine line, i.e. no 11-term progression `a + t•d` (`t ∈ F_11`)
with `d ≠ 0`. -/
theorem main : ∃ L : List Pt, L.Nodup ∧ L.length = 1010 ∧ LineFree L :=
  ⟨theSet, theSet_nodup, theSet_length, lineFree_theSet⟩

#print axioms main

/-! ### Higher dimensions: vectors of `F_11^n` as lists of length `n` -/

/-- Coordinatewise addition of vectors (lists) over `F_11`. -/
def vadd (a b : List (Fin 11)) : List (Fin 11) := List.zipWith (· + ·) a b

/-- Scalar multiplication of a vector (list) over `F_11`. -/
def vsmul (t : Fin 11) (d : List (Fin 11)) : List (Fin 11) := d.map (t * ·)

/-- `L ⊆ F_11^n` (vectors = lists of length `n`) contains no full line `{a + t•d}`, `d ≠ 0`. -/
def LineFreeN (n : Nat) (L : List (List (Fin 11))) : Prop :=
  ∀ a d : List (Fin 11), a.length = n → d.length = n → (∃ x ∈ d, x ≠ 0) →
    ∃ t : Fin 11, vadd a (vsmul t d) ∉ L

/-- Cartesian product of two sets of vectors (concatenation of coordinates). -/
def prodSet (L M : List (List (Fin 11))) : List (List (Fin 11)) :=
  L.flatMap fun u => M.map fun v => u ++ v

theorem mem_prodSet {L M : List (List (Fin 11))} {w : List (Fin 11)} :
    w ∈ prodSet L M ↔ ∃ u ∈ L, ∃ v ∈ M, w = u ++ v := by
  simp only [prodSet, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩; exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩; exact ⟨u, hu, v, hv, rfl⟩

theorem length_prodSet (L M : List (List (Fin 11))) :
    (prodSet L M).length = L.length * M.length := by
  induction L with
  | nil => simp [prodSet]
  | cons u L ih =>
    simp only [prodSet, List.flatMap_cons, List.length_append, List.length_map] at ih ⊢
    rw [ih, List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem nodup_prodSet {m : Nat} {L M : List (List (Fin 11))} (hL : L.Nodup) (hM : M.Nodup)
    (hlen : ∀ u ∈ L, u.length = m) : (prodSet L M).Nodup := by
  induction L with
  | nil => simp [prodSet]
  | cons u L ih =>
    rw [List.nodup_cons] at hL
    have ih' := ih hL.2 (fun u' hu' => hlen u' (List.mem_cons_of_mem _ hu'))
    simp only [prodSet, List.flatMap_cons] at ih' ⊢
    rw [List.nodup_append]
    refine ⟨?_, ih', ?_⟩
    · unfold List.Nodup
      rw [List.pairwise_map]
      exact List.Pairwise.imp (fun h e => h (List.append_cancel_left e)) hM
    · intro a ha b hb hab
      rw [List.mem_map] at ha
      obtain ⟨v, -, rfl⟩ := ha
      have hb' : b ∈ prodSet L M := hb
      rw [mem_prodSet] at hb'
      obtain ⟨u', hu', v', -, rfl⟩ := hb'
      have h1 : u.length = u'.length := by
        rw [hlen u (List.mem_cons_self), hlen u' (List.mem_cons_of_mem _ hu')]
      have := List.append_inj_left hab h1
      exact hL.1 (this ▸ hu')

theorem vadd_vsmul_append (a₁ a₂ d₁ d₂ : List (Fin 11)) (t : Fin 11)
    (h₁ : a₁.length = d₁.length) :
    vadd (a₁ ++ a₂) (vsmul t (d₁ ++ d₂)) = vadd a₁ (vsmul t d₁) ++ vadd a₂ (vsmul t d₂) := by
  unfold vadd vsmul
  rw [List.map_append, List.zipWith_append (by simp [h₁])]

theorem length_vadd_vsmul (a d : List (Fin 11)) (t : Fin 11) (h : a.length = d.length) :
    (vadd a (vsmul t d)).length = a.length := by
  simp [vadd, vsmul, List.length_zipWith, h]

theorem lineFree_prodSet {m k : Nat} {L M : List (List (Fin 11))}
    (hL : LineFreeN m L) (hM : LineFreeN k M) (hLlen : ∀ u ∈ L, u.length = m) :
    LineFreeN (m + k) (prodSet L M) := by
  intro a d ha hd hnz
  have ha1 : (a.take m).length = m := by simp [List.length_take, ha]
  have hd1 : (d.take m).length = m := by simp [List.length_take, hd]
  have ha2 : (a.drop m).length = k := by simp [List.length_drop, ha]
  have hd2 : (d.drop m).length = k := by simp [List.length_drop, hd]
  have split : ∀ t : Fin 11, vadd a (vsmul t d) =
      vadd (a.take m) (vsmul t (d.take m)) ++ vadd (a.drop m) (vsmul t (d.drop m)) := by
    intro t
    conv => lhs; rw [← List.take_append_drop m a, ← List.take_append_drop m d]
    exact vadd_vsmul_append _ _ _ _ t (by rw [ha1, hd1])
  obtain ⟨x, hx, hx0⟩ := hnz
  rw [← List.take_append_drop m d, List.mem_append] at hx
  rcases hx with hx | hx
  · obtain ⟨t, ht⟩ := hL (a.take m) (d.take m) ha1 hd1 ⟨x, hx, hx0⟩
    refine ⟨t, fun hw => ht ?_⟩
    rw [mem_prodSet] at hw
    obtain ⟨u, hu, v, -, huv⟩ := hw
    rw [split t] at huv
    have hlen : (vadd (a.take m) (vsmul t (d.take m))).length = u.length := by
      rw [length_vadd_vsmul _ _ _ (by rw [ha1, hd1]), ha1, hLlen u hu]
    rw [List.append_inj_left huv hlen]; exact hu
  · obtain ⟨t, ht⟩ := hM (a.drop m) (d.drop m) ha2 hd2 ⟨x, hx, hx0⟩
    refine ⟨t, fun hw => ht ?_⟩
    rw [mem_prodSet] at hw
    obtain ⟨u, hu, v, hv, huv⟩ := hw
    rw [split t] at huv
    have hlen : (vadd (a.take m) (vsmul t (d.take m))).length = u.length := by
      rw [length_vadd_vsmul _ _ _ (by rw [ha1, hd1]), ha1, hLlen u hu]
    rw [(List.append_inj huv hlen).2]; exact hv

/-- `k`-fold power of a set of vectors. -/
def powSet (L : List (List (Fin 11))) : Nat → List (List (Fin 11))
  | 0 => [[]]
  | k + 1 => prodSet L (powSet L k)

theorem powSet_spec {m N : Nat} {L : List (List (Fin 11))} (hnd : L.Nodup) (hl : L.length = N)
    (hlen : ∀ u ∈ L, u.length = m) (hlf : LineFreeN m L) (k : Nat) :
    (powSet L k).Nodup ∧ (powSet L k).length = N ^ k ∧
      (∀ w ∈ powSet L k, w.length = m * k) ∧ LineFreeN (m * k) (powSet L k) := by
  induction k with
  | zero =>
    refine ⟨by simp [powSet], by simp [powSet], by simp [powSet], ?_⟩
    intro a d _ hd hnz
    obtain ⟨x, hx, -⟩ := hnz
    have : d = [] := List.eq_nil_of_length_eq_zero (by simpa using hd)
    subst this; simp at hx
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    refine ⟨nodup_prodSet hnd h1 hlen, ?_, ?_, ?_⟩
    · simp only [powSet]; rw [length_prodSet, h2, hl, Nat.pow_succ, Nat.mul_comm]
    · intro w hw
      simp only [powSet] at hw
      rw [mem_prodSet] at hw
      obtain ⟨u, hu, v, hv, rfl⟩ := hw
      rw [List.length_append, hlen u hu, h3 v hv, Nat.mul_succ, Nat.add_comm]
    · have := lineFree_prodSet hlf h4 hlen
      simp only [powSet]
      rwa [Nat.mul_succ, Nat.add_comm]

/-- Coordinates of a point of `F_11^3` as a list. -/
def toList (q : Pt) : List (Fin 11) := [q.1, q.2.1, q.2.2]

theorem lineFreeN_three {L : List Pt} (h : LineFree L) : LineFreeN 3 (L.map toList) := by
  intro a d ha hd hnz
  match a, d, ha, hd with
  | [a0, a1, a2], [d0, d1, d2], _, _ =>
    have hd0 : (d0, d1, d2) ≠ ((0, 0, 0) : Pt) := by
      intro e
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, rfl, rfl⟩ := e
      obtain ⟨x, hx, hx0⟩ := hnz
      simp at hx
      rcases hx with rfl | rfl | rfl <;> exact hx0 rfl
    obtain ⟨t, ht⟩ := h (a0, a1, a2) (d0, d1, d2) hd0
    refine ⟨t, fun hm => ht ?_⟩
    rw [List.mem_map] at hm
    obtain ⟨q, hq, hqe⟩ := hm
    have : q = add (a0, a1, a2) (smul t (d0, d1, d2)) := by
      obtain ⟨q0, q1, q2⟩ := q
      simp [toList, vadd, vsmul] at hqe
      simp [add, smul, hqe]
    exact this ▸ hq

theorem nodup_map_toList {L : List Pt} (h : L.Nodup) : (L.map toList).Nodup := by
  unfold List.Nodup at *
  rw [List.pairwise_map]
  refine List.Pairwise.imp ?_ h
  intro a b hab e
  apply hab
  obtain ⟨a0, a1, a2⟩ := a
  obtain ⟨b0, b1, b2⟩ := b
  simp [toList] at e
  obtain ⟨rfl, rfl, rfl⟩ := e
  rfl

theorem product_bound {L : List Pt} {N : Nat} (hnd : L.Nodup) (hl : L.length = N) (hlf : LineFree L)
    (k : Nat) : ∃ M : List (List (Fin 11)), M.Nodup ∧ M.length = N ^ k ∧
      (∀ v ∈ M, v.length = 3 * k) ∧ LineFreeN (3 * k) M := by
  have hlen : ∀ u ∈ L.map toList, u.length = 3 := by
    intro u hu; rw [List.mem_map] at hu; obtain ⟨q, -, rfl⟩ := hu; rfl
  have := powSet_spec (nodup_map_toList hnd) (by rw [List.length_map, hl]) hlen (lineFreeN_three hlf) k
  exact ⟨_, this⟩

/-- **Corollary** (product construction, `r_11(F_11^{3k}) ≥ 1010^k` for every `k`): for every `k`
there are `1010^k` pairwise distinct vectors of `F_11^{3k}` (lists of length `3k`) containing no
full affine line.  Hence `α_11 = lim r_11(F_11^n)^(1/n) ≥ 1010^(1/3)`. -/
theorem main_pow (k : Nat) : ∃ M : List (List (Fin 11)), M.Nodup ∧ M.length = 1010 ^ k ∧
    (∀ v ∈ M, v.length = 3 * k) ∧ LineFreeN (3 * k) M :=
  product_bound theSet_nodup theSet_length lineFree_theSet k

#print axioms main_pow
