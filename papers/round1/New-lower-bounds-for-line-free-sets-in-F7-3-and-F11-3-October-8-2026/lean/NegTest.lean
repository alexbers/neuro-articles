/-
  A10: a line-free subset of F_7^3 with 227 points, i.e. r_7(F_7^3) ≥ 227.

  F_7^3 = (Z/7Z)^3.  A set is *line-free* if it contains no affine line
  {a + t•d : t ∈ F_7} with d ≠ 0; equivalently it contains no 7-term arithmetic
  progression a, a+d, ..., a+6d with nonzero common difference.
  Previous record: r_7(F_7^3) ≥ 225 (Elsholtz–Führer–Füredi–Kovács–Pach–Simon–Velich, arXiv:2310.03382, Thm 1.2).

  Core Lean 4 only (no Mathlib).  All computation is checked by the kernel
  (`decide +kernel`); no `native_decide`.
-/

set_option Elab.async false  -- elaborate sequentially (keeps peak memory low)

/-! ### Definitions used in the main statement -/

/-- Points of `F_7^3`.  Arithmetic in `Fin 7` is arithmetic modulo 7. -/
abbrev Pt := Fin 7 × Fin 7 × Fin 7

/-- Coordinatewise addition in `F_7^3`. -/
def add (a b : Pt) : Pt := (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

/-- Scalar multiplication `t • d` in `F_7^3`. -/
def smul (t : Fin 7) (d : Pt) : Pt := (t * d.1, t * d.2.1, t * d.2.2)

/-- `L` contains no full affine line `{a + t • d : t ∈ F_7}` with `d ≠ 0`. -/
def LineFree (L : List Pt) : Prop :=
  ∀ a d : Pt, d ≠ (0, 0, 0) → ∃ t : Fin 7, add a (smul t d) ∉ L

/-- The explicit set: 227 points `(x, y, z)` of `F_7^3`. -/
def theSet : List Pt := [
  (0, 0, 1), (0, 0, 2), (0, 0, 3), (0, 0, 4), (0, 0, 5), (0, 0, 6), (0, 1, 0), (0, 1, 1),
  (0, 1, 3), (0, 1, 5), (0, 1, 6), (0, 2, 0), (0, 2, 1), (0, 2, 3), (0, 2, 4), (0, 2, 5),
  (0, 2, 6), (0, 3, 0), (0, 3, 1), (0, 3, 2), (0, 3, 4), (0, 3, 6), (0, 4, 1), (0, 4, 3),
  (0, 4, 4), (0, 4, 5), (0, 5, 0), (0, 5, 1), (0, 5, 3), (0, 5, 5), (0, 5, 6), (0, 6, 0),
  (0, 6, 3), (0, 6, 4), (0, 6, 6), (1, 1, 0), (1, 1, 1), (1, 1, 2), (1, 1, 4), (1, 1, 6),
  (1, 2, 0), (1, 2, 1), (1, 2, 2), (1, 2, 4), (1, 2, 5), (1, 2, 6), (1, 3, 0), (1, 3, 1),
  (1, 3, 2), (1, 3, 3), (1, 3, 4), (1, 4, 0), (1, 4, 1), (1, 4, 4), (1, 4, 5), (1, 5, 1),
  (1, 5, 3), (1, 5, 4), (1, 5, 5), (1, 6, 0), (1, 6, 2), (1, 6, 5), (1, 6, 6), (2, 0, 0),
  (2, 0, 1), (2, 0, 3), (2, 0, 5), (2, 0, 6), (2, 1, 0), (2, 1, 1), (2, 1, 4), (2, 1, 5),
  (2, 2, 0), (2, 2, 1), (2, 2, 2), (2, 2, 4), (2, 2, 5), (2, 2, 6), (2, 3, 3), (2, 3, 6),
  (2, 4, 0), (2, 4, 1), (2, 4, 2), (2, 4, 6), (2, 5, 0), (2, 5, 2), (2, 5, 3), (2, 5, 5),
  (2, 5, 6), (2, 6, 1), (2, 6, 2), (2, 6, 3), (2, 6, 6), (3, 0, 1), (3, 0, 2), (3, 0, 4),
  (3, 0, 6), (3, 1, 0), (3, 1, 2), (3, 1, 3), (3, 1, 4), (3, 1, 6), (3, 2, 0), (3, 2, 1),
  (3, 2, 6), (3, 3, 0), (3, 3, 1), (3, 3, 2), (3, 3, 3), (3, 3, 4), (3, 3, 6), (3, 4, 0),
  (3, 4, 1), (3, 4, 2), (3, 4, 3), (3, 4, 4), (3, 4, 6), (3, 5, 0), (3, 5, 1), (3, 5, 2),
  (3, 5, 4), (3, 5, 6), (3, 6, 2), (3, 6, 3), (3, 6, 4), (4, 0, 0), (4, 0, 1), (4, 0, 2),
  (4, 0, 3), (4, 0, 5), (4, 1, 1), (4, 1, 2), (4, 1, 3), (4, 1, 4), (4, 1, 5), (4, 1, 6),
  (4, 2, 2), (4, 2, 4), (4, 3, 0), (4, 3, 3), (4, 3, 4), (4, 3, 5), (4, 4, 0), (4, 4, 2),
  (4, 4, 3), (4, 4, 4), (4, 4, 5), (4, 5, 0), (4, 5, 1), (4, 5, 2), (4, 5, 3), (4, 5, 6),
  (4, 6, 0), (4, 6, 1), (4, 6, 3), (4, 6, 4), (4, 6, 5), (4, 6, 6), (5, 0, 0), (5, 0, 2),
  (5, 0, 3), (5, 0, 4), (5, 0, 6), (5, 1, 0), (5, 1, 1), (5, 1, 2), (5, 1, 3), (5, 1, 4),
  (5, 2, 1), (5, 2, 2), (5, 2, 3), (5, 2, 4), (5, 2, 5), (5, 2, 6), (5, 3, 0), (5, 3, 2),
  (5, 3, 3), (5, 3, 4), (5, 3, 5), (5, 3, 6), (5, 4, 1), (5, 4, 3), (5, 4, 4), (5, 4, 5),
  (5, 4, 6), (5, 5, 1), (5, 5, 2), (5, 5, 6), (5, 6, 0), (5, 6, 1), (5, 6, 2), (5, 6, 3),
  (5, 6, 5), (5, 6, 6), (6, 0, 0), (6, 0, 1), (6, 0, 2), (6, 0, 3), (6, 0, 4), (6, 1, 2),
  (6, 1, 3), (6, 1, 4), (6, 1, 6), (6, 2, 0), (6, 2, 1), (6, 2, 2), (6, 2, 5), (6, 2, 6),
  (6, 3, 2), (6, 3, 3), (6, 3, 4), (6, 3, 6), (6, 4, 0), (6, 4, 2), (6, 4, 3), (6, 4, 4),
  (6, 4, 5), (6, 4, 6), (6, 5, 0), (6, 5, 3), (6, 5, 4), (6, 5, 6), (6, 6, 0), (6, 6, 1),
  (6, 6, 3), (6, 6, 4), (6, 6, 5)]

/-! ### Computational verification (kernel) -/

/-- All points of `F_7^3`. -/
def allPts : List Pt :=
  (List.finRange 7).flatMap fun x => (List.finRange 7).flatMap fun y =>
    (List.finRange 7).map fun z => (x, y, z)

theorem mem_allPts (q : Pt) : q ∈ allPts := by
  obtain ⟨x, y, z⟩ := q
  simp [allPts, List.mem_flatMap, List.mem_map, List.mem_finRange]

/-- The points with first coordinate `x`. -/
def slice (x : Fin 7) : List Pt :=
  (List.finRange 7).flatMap fun y => (List.finRange 7).map fun z => (x, y, z)

theorem mem_slice (x y z : Fin 7) : (x, y, z) ∈ slice x := by
  simp [slice, List.mem_flatMap, List.mem_map, List.mem_finRange]

/-- Lexicographic index of a point, in `[0, 343)` (the position of the point in `allPts`). -/
def lex (q : Pt) : Nat := 49 * q.1.val + 7 * q.2.1.val + q.2.2.val

theorem allPts_lex : allPts.map lex = List.range 343 := by decide +kernel

theorem allPts_nodup : allPts.Nodup := by
  have h : (allPts.map lex).Nodup := by rw [allPts_lex]; exact List.nodup_range
  unfold List.Nodup at h ⊢
  rw [List.pairwise_map] at h
  exact h.imp (fun {a b} (hne : lex a ≠ lex b) (e : a = b) => hne (by rw [e]))

/-- Bitmask of `theSet` (bit `lex q` is set iff `q ∈ theSet`), used for fast lookup. -/
def mask : Nat := 8357465582602579456950128556911733518314085189728468316077593132122850920297462176629368582396507518462

def inMask (q : Pt) : Bool := mask.testBit (lex q)

/-- The explicit list is exactly the set of points selected by the mask, in `allPts` order. -/
theorem theSet_eq : theSet = allPts.filter inMask := by decide +kernel

theorem mem_iff (q : Pt) : q ∈ theSet ↔ inMask q = true := by
  rw [theSet_eq, List.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨mem_allPts q, h⟩⟩

/-- For the base point `a`: every nonzero direction `d` has some `t` with `a + t•d ∉ theSet`. -/
def checkAt (a : Pt) : Bool :=
  allPts.all fun d => d == (0, 0, 0) || (List.finRange 7).any fun t => !inMask (add a (smul t d))


-- negative control (#eval only, not part of the certificate):
-- the same checker must reject a set containing a line, or the set plus one extra point
def bad : List Pt := (List.finRange 7).map fun t => (t, 0, 0)
def badMask : Nat := (bad.map lex).foldl (fun m i => m ||| (1 <<< i)) 0
def checkWith (m : Nat) : Bool :=
  allPts.all fun a => allPts.all fun d =>
    d == (0, 0, 0) || (List.finRange 7).any fun t => !m.testBit (lex (add a (smul t d)))
#eval checkWith mask                       -- expected: true
#eval checkWith (mask ||| badMask)         -- expected: false (contains the line {(t,0,0)})
#eval (allPts.filter (fun q => !inMask q)).map (fun q => checkWith (mask ||| (1 <<< lex q))) |>.all (· == false)
                                           -- expected: true (adding ANY missing point creates a line)
#eval (allPts.filter inMask).length        -- expected: 227
