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

theorem slice0_ok : (slice 0).all checkAt = true := by decide +kernel
theorem slice1_ok : (slice 1).all checkAt = true := by decide +kernel
theorem slice2_ok : (slice 2).all checkAt = true := by decide +kernel
theorem slice3_ok : (slice 3).all checkAt = true := by decide +kernel
theorem slice4_ok : (slice 4).all checkAt = true := by decide +kernel
theorem slice5_ok : (slice 5).all checkAt = true := by decide +kernel
theorem slice6_ok : (slice 6).all checkAt = true := by decide +kernel

theorem checkAt_ok (a : Pt) : checkAt a = true := by
  obtain ⟨x, y, z⟩ := a
  have hx : (slice x).all checkAt = true := by
    match x with
    | ⟨0, _⟩ => exact slice0_ok
    | ⟨1, _⟩ => exact slice1_ok
    | ⟨2, _⟩ => exact slice2_ok
    | ⟨3, _⟩ => exact slice3_ok
    | ⟨4, _⟩ => exact slice4_ok
    | ⟨5, _⟩ => exact slice5_ok
    | ⟨6, _⟩ => exact slice6_ok
    | ⟨n + 7, h⟩ => exact absurd h (by omega)
  exact List.all_eq_true.mp hx _ (mem_slice x y z)

theorem lineFree_theSet : LineFree theSet := by
  intro a d hd
  have h := List.all_eq_true.mp (checkAt_ok a) d (mem_allPts d)
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact absurd h hd
  · obtain ⟨t, -, ht⟩ := List.any_eq_true.mp h
    refine ⟨t, ?_⟩
    rw [mem_iff]
    simpa using ht

theorem theSet_nodup : theSet.Nodup := by
  rw [theSet_eq]; exact allPts_nodup.filter _

theorem theSet_length : theSet.length = 227 := by decide +kernel

/-! ### Main theorem -/

/-- **Main theorem** (`r_7(F_7^3) ≥ 227`): there is a list of 227 pairwise distinct points of
`F_7^3` containing no full affine line, i.e. no 7-term progression `a + t•d` (`t ∈ F_7`)
with `d ≠ 0`. -/
theorem main : ∃ L : List Pt, L.Nodup ∧ L.length = 227 ∧ LineFree L :=
  ⟨theSet, theSet_nodup, theSet_length, lineFree_theSet⟩

#print axioms main

/-! ### Higher dimensions: vectors of `F_7^n` as lists of length `n` -/

/-- Coordinatewise addition of vectors (lists) over `F_7`. -/
def vadd (a b : List (Fin 7)) : List (Fin 7) := List.zipWith (· + ·) a b

/-- Scalar multiplication of a vector (list) over `F_7`. -/
def vsmul (t : Fin 7) (d : List (Fin 7)) : List (Fin 7) := d.map (t * ·)

/-- `L ⊆ F_7^n` (vectors = lists of length `n`) contains no full line `{a + t•d}`, `d ≠ 0`. -/
def LineFreeN (n : Nat) (L : List (List (Fin 7))) : Prop :=
  ∀ a d : List (Fin 7), a.length = n → d.length = n → (∃ x ∈ d, x ≠ 0) →
    ∃ t : Fin 7, vadd a (vsmul t d) ∉ L

/-- Cartesian product of two sets of vectors (concatenation of coordinates). -/
def prodSet (L M : List (List (Fin 7))) : List (List (Fin 7)) :=
  L.flatMap fun u => M.map fun v => u ++ v

theorem mem_prodSet {L M : List (List (Fin 7))} {w : List (Fin 7)} :
    w ∈ prodSet L M ↔ ∃ u ∈ L, ∃ v ∈ M, w = u ++ v := by
  simp only [prodSet, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩; exact ⟨u, hu, v, hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩; exact ⟨u, hu, v, hv, rfl⟩

theorem length_prodSet (L M : List (List (Fin 7))) :
    (prodSet L M).length = L.length * M.length := by
  induction L with
  | nil => simp [prodSet]
  | cons u L ih =>
    simp only [prodSet, List.flatMap_cons, List.length_append, List.length_map] at ih ⊢
    rw [ih, List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem nodup_prodSet {m : Nat} {L M : List (List (Fin 7))} (hL : L.Nodup) (hM : M.Nodup)
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

theorem vadd_vsmul_append (a₁ a₂ d₁ d₂ : List (Fin 7)) (t : Fin 7)
    (h₁ : a₁.length = d₁.length) :
    vadd (a₁ ++ a₂) (vsmul t (d₁ ++ d₂)) = vadd a₁ (vsmul t d₁) ++ vadd a₂ (vsmul t d₂) := by
  unfold vadd vsmul
  rw [List.map_append, List.zipWith_append (by simp [h₁])]

theorem length_vadd_vsmul (a d : List (Fin 7)) (t : Fin 7) (h : a.length = d.length) :
    (vadd a (vsmul t d)).length = a.length := by
  simp [vadd, vsmul, List.length_zipWith, h]

theorem lineFree_prodSet {m k : Nat} {L M : List (List (Fin 7))}
    (hL : LineFreeN m L) (hM : LineFreeN k M) (hLlen : ∀ u ∈ L, u.length = m) :
    LineFreeN (m + k) (prodSet L M) := by
  intro a d ha hd hnz
  have ha1 : (a.take m).length = m := by simp [List.length_take, ha]
  have hd1 : (d.take m).length = m := by simp [List.length_take, hd]
  have ha2 : (a.drop m).length = k := by simp [List.length_drop, ha]
  have hd2 : (d.drop m).length = k := by simp [List.length_drop, hd]
  have split : ∀ t : Fin 7, vadd a (vsmul t d) =
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
def powSet (L : List (List (Fin 7))) : Nat → List (List (Fin 7))
  | 0 => [[]]
  | k + 1 => prodSet L (powSet L k)

theorem powSet_spec {m N : Nat} {L : List (List (Fin 7))} (hnd : L.Nodup) (hl : L.length = N)
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

/-- Coordinates of a point of `F_7^3` as a list. -/
def toList (q : Pt) : List (Fin 7) := [q.1, q.2.1, q.2.2]

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
    (k : Nat) : ∃ M : List (List (Fin 7)), M.Nodup ∧ M.length = N ^ k ∧
      (∀ v ∈ M, v.length = 3 * k) ∧ LineFreeN (3 * k) M := by
  have hlen : ∀ u ∈ L.map toList, u.length = 3 := by
    intro u hu; rw [List.mem_map] at hu; obtain ⟨q, -, rfl⟩ := hu; rfl
  have := powSet_spec (nodup_map_toList hnd) (by rw [List.length_map, hl]) hlen (lineFreeN_three hlf) k
  exact ⟨_, this⟩

/-- **Corollary** (product construction, `r_7(F_7^{3k}) ≥ 227^k` for every `k`): for every `k`
there are `227^k` pairwise distinct vectors of `F_7^{3k}` (lists of length `3k`) containing no
full affine line.  Hence `α_7 = lim r_7(F_7^n)^(1/n) ≥ 227^(1/3)`. -/
theorem main_pow (k : Nat) : ∃ M : List (List (Fin 7)), M.Nodup ∧ M.length = 227 ^ k ∧
    (∀ v ∈ M, v.length = 3 * k) ∧ LineFreeN (3 * k) M :=
  product_bound theSet_nodup theSet_length lineFree_theSet k

#print axioms main_pow
