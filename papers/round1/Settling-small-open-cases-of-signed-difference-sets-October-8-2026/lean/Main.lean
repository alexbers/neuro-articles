/-
  A07 — Signed difference sets: settling open group-specific existence cases of the
  La Jolla Signed Difference Set Repository (D. M. Gordon, zenodo 10.5281/zenodo.7473882,
  v1.2, April 2026), which remained open after He–Wu, arXiv:2608.22936 (Sep 2026).

  Self-contained: Lean 4 core only (no Mathlib).  All certificates are checked by the kernel
  (`decide +kernel`); no `native_decide`, no `sorry`, no extra axioms.
-/
set_option Elab.async false

/-! ## The group `ℤ/m₁ × ⋯ × ℤ/m_r`

We model the abelian group `G = ℤ/m₁ × ⋯ × ℤ/m_r` (invariant factors / moduli `ms = [m₁,…,m_r]`,
order `v = m₁⋯m_r`) on the carrier `{0, 1, …, v-1} ⊆ ℕ` through mixed-radix coordinates:
`x ↔ (x₁,…,x_r)` with `x = x₁·(m₂⋯m_r) + x₂·(m₃⋯m_r) + ⋯ + x_r`, `0 ≤ xᵢ < mᵢ`.
The group law `gadd` is componentwise addition modulo `mᵢ` of the coordinates; `0` is the
identity.  (The lemmas `model_G…` below check, for every group used, that this really is a
bijective coordinatisation.) -/

/-- mixed-radix coordinates of `x` (most significant first) -/
def coords : List Nat → Nat → List Nat
  | [], _ => []
  | m :: ms, x => (x / ms.prod) % m :: coords ms x

/-- the number with the given mixed-radix coordinates -/
def ofCoords : List Nat → List Nat → Nat
  | [], _ => 0
  | _ :: ms, c => c.headD 0 * ms.prod + ofCoords ms c.tail

/-- componentwise addition of coordinate tuples modulo the `mᵢ` -/
def addCoords : List Nat → List Nat → List Nat → List Nat
  | m :: ms, a :: as, b :: bs => (a + b) % m :: addCoords ms as bs
  | _, _, _ => []

/-- the group law of `ℤ/m₁ × ⋯ × ℤ/m_r` on `{0,…,v-1}` -/
def gadd (ms : List Nat) (x y : Nat) : Nat :=
  ofCoords ms (addCoords ms (coords ms x) (coords ms y))

/-- a coordinate tuple is valid if it has the right length and `0 ≤ xᵢ < mᵢ` -/
def validCoords : List Nat → List Nat → Bool
  | [], [] => true
  | m :: ms, a :: as => decide (a < m) && validCoords ms as
  | _, _ => false

/-- all valid coordinate tuples: the Cartesian product `[0,m₁) × ⋯ × [0,m_r)` -/
def tuples : List Nat → List (List Nat)
  | [] => [[]]
  | m :: ms => (List.range m).flatMap (fun a => (tuples ms).map (a :: ·))

/-- Sanity property of the model: `coords` maps `{0,…,v-1}` to valid tuples with left inverse
`ofCoords`, and `ofCoords` maps every tuple of `[0,m₁) × ⋯ × [0,m_r)` into `{0,…,v-1}` with
left inverse `coords`.  Hence `coords` is a bijection `{0,…,v-1} ≃ ∏ [0,mᵢ)` and, by its
definition, `gadd` is componentwise addition mod `mᵢ` transported along this bijection. -/
def GroupModelOK (ms : List Nat) : Prop :=
  (∀ x ∈ List.range ms.prod,
      validCoords ms (coords ms x) = true ∧ ofCoords ms (coords ms x) = x) ∧
  (∀ t ∈ tuples ms, ofCoords ms t < ms.prod ∧ coords ms (ofCoords ms t) = t)

instance (ms : List Nat) : Decidable (GroupModelOK ms) := by unfold GroupModelOK; infer_instance

/-! ## Signed difference sets

A `(v,k,λ)` signed difference set (Gordon, Des. Codes Cryptogr. 91 (2023)) in a group `G` of
order `v` is a group-ring element `D = ∑ s_g g` with `s_g ∈ {-1,0,1}`, exactly `k` nonzero
coefficients, and `D·D⁽⁻¹⁾ = (k-λ)·1_G + λ·G` in `ℤ[G]`.  The coefficient of `y` in `D·D⁽⁻¹⁾`
is `∑_g s_{g+y} s_g`; at `y = 0` it is automatically `k`, so the condition is exactly:
for every `y ≠ 0`, `∑_g D(g)·D(g+y) = λ`.  We write `P = {g : D g = 1}`, `N = {g : D g = -1}`. -/

/-- `D : ℕ → ℤ` (only its values on `{0,…,v-1}` matter) is a `(v,k,λ)` signed difference set
in `ℤ/m₁ × ⋯ × ℤ/m_r`, `v = ms.prod`. -/
def IsSDS (ms : List Nat) (k : Nat) (lam : Int) (D : Nat → Int) : Prop :=
  (∀ g ∈ List.range ms.prod, D g = -1 ∨ D g = 0 ∨ D g = 1) ∧
  ((List.range ms.prod).filter (fun g => D g ≠ 0)).length = k ∧
  ∀ y ∈ List.range ms.prod, y ≠ 0 →
    ((List.range ms.prod).map (fun g => D g * D (gadd ms g y))).sum = lam

instance (ms : List Nat) (k : Nat) (lam : Int) (D : Nat → Int) : Decidable (IsSDS ms k lam D) := by
  unfold IsSDS; infer_instance

/-- The signed set with positive part `P` and negative part `N`, both given as lists of
coordinate tuples (if a tuple were in both lists it would count as positive). -/
def signedOf (ms : List Nat) (P N : List (List Nat)) (g : Nat) : Int :=
  if coords ms g ∈ P then 1 else if coords ms g ∈ N then -1 else 0


/-! ## Nonexistence of a (9,8,1) signed difference set in ℤ/3 × ℤ/3

Proof by exhaustive enumeration of all `3^9` coefficient vectors, checked by the kernel.
The enumeration is split into 27 lemmas according to the first three coefficients. -/

/-- all lists of length `n` with entries in `{-1,0,1}` -/
def tern : Nat → List (List Int)
  | 0 => [[]]
  | n+1 => (tern n).flatMap (fun l => [(-1)::l, 0::l, 1::l])

theorem mem_tern (D : Nat → Int) : ∀ l : List Nat, (∀ g ∈ l, D g = -1 ∨ D g = 0 ∨ D g = 1) →
    l.map D ∈ tern l.length := by
  intro l
  induction l with
  | nil => intro _; simp [tern]
  | cons a l ih =>
    intro h
    have h1 := ih (fun g hg => h g (List.mem_cons_of_mem a hg))
    have h2 := h a List.mem_cons_self
    simp only [List.map_cons, List.length_cons, tern, List.mem_flatMap]
    refine ⟨_, h1, ?_⟩
    rcases h2 with h2 | h2 | h2 <;> simp [h2]

theorem gadd_lt_33 : ∀ g ∈ List.range 9, ∀ y ∈ List.range 9, gadd [3,3] g y < 9 := by
  decide +kernel

/-- `IsSDS [3,3]` only depends on the values of `D` on `{0,…,8}`. -/
theorem IsSDS_congr_33 (k : Nat) (lam : Int) (D D' : Nat → Int)
    (hDD : ∀ g, g < 9 → D g = D' g) : IsSDS [3,3] k lam D → IsSDS [3,3] k lam D' := by
  have hp : ([3,3] : List Nat).prod = 9 := by decide
  intro ⟨h1, h2, h3⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    have := h1 g hg
    rw [hp, List.mem_range] at hg
    rw [← hDD g hg]; exact this
  · rw [← h2]; congr 1
    apply List.filter_congr
    intro g hg
    rw [hp, List.mem_range] at hg
    rw [hDD g hg]
  · intro y hy hy0
    rw [← h3 y hy hy0]
    congr 1
    apply List.map_congr_left
    intro g hg
    have hg' := hg
    rw [hp] at hg' hy
    have hlt := gadd_lt_33 g hg' y hy
    rw [List.mem_range] at hg'
    rw [hDD g hg', hDD _ hlt]

theorem no_9_8_1_part0 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([-1,-1,-1] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part1 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([-1,-1,0] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part2 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([-1,-1,1] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part3 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([-1,0,-1] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part4 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([-1,0,0] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part5 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([-1,0,1] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part6 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([-1,1,-1] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part7 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([-1,1,0] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part8 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([-1,1,1] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part9 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([0,-1,-1] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part10 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([0,-1,0] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part11 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([0,-1,1] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part12 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([0,0,-1] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part13 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([0,0,0] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part14 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([0,0,1] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part15 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([0,1,-1] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part16 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([0,1,0] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part17 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([0,1,1] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part18 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([1,-1,-1] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part19 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([1,-1,0] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part20 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([1,-1,1] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part21 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([1,0,-1] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part22 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([1,0,0] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part23 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([1,0,1] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part24 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([1,1,-1] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part25 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([1,1,0] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_part26 : ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => ([1,1,1] ++ c2 ++ c3).getD g 0) := by
  decide +kernel

theorem no_9_8_1_vec : ∀ c1 ∈ tern 3, ∀ c2 ∈ tern 3, ∀ c3 ∈ tern 3,
    ¬ IsSDS [3,3] 8 1 (fun g => (c1 ++ c2 ++ c3).getD g 0) := by
  intro c1 hc1
  simp only [tern, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc1
  rcases hc1 with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    first
    | exact no_9_8_1_part0
    | exact no_9_8_1_part1
    | exact no_9_8_1_part2
    | exact no_9_8_1_part3
    | exact no_9_8_1_part4
    | exact no_9_8_1_part5
    | exact no_9_8_1_part6
    | exact no_9_8_1_part7
    | exact no_9_8_1_part8
    | exact no_9_8_1_part9
    | exact no_9_8_1_part10
    | exact no_9_8_1_part11
    | exact no_9_8_1_part12
    | exact no_9_8_1_part13
    | exact no_9_8_1_part14
    | exact no_9_8_1_part15
    | exact no_9_8_1_part16
    | exact no_9_8_1_part17
    | exact no_9_8_1_part18
    | exact no_9_8_1_part19
    | exact no_9_8_1_part20
    | exact no_9_8_1_part21
    | exact no_9_8_1_part22
    | exact no_9_8_1_part23
    | exact no_9_8_1_part24
    | exact no_9_8_1_part25
    | exact no_9_8_1_part26

/-- **Nonexistence.** There is no `(9,8,1)` signed difference set in `ℤ/3 × ℤ/3`. -/
theorem no_SDS_9_8_1_Z3xZ3 : ¬ ∃ D : Nat → Int, IsSDS [3,3] 8 1 D := by
  intro ⟨D, h⟩
  have hv : ∀ g, g < 9 → D g = -1 ∨ D g = 0 ∨ D g = 1 := by
    intro g hg; exact h.1 g (by simpa using hg)
  have h1 := mem_tern D [0,1,2] (by intro g hg; simp at hg; exact hv g (by omega))
  have h2 := mem_tern D [3,4,5] (by intro g hg; simp at hg; exact hv g (by omega))
  have h3 := mem_tern D [6,7,8] (by intro g hg; simp at hg; exact hv g (by omega))
  apply no_9_8_1_vec _ h1 _ h2 _ h3
  apply IsSDS_congr_33 8 1 D _ _ h
  intro g hg
  rcases (by omega : g = 0 ∨ g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4 ∨ g = 5 ∨ g = 6 ∨ g = 7 ∨ g = 8)
    with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl


/-! ## Sanity checks of the group model for every group used below

For each list of moduli `ms`, `coords ms : {0,…,v-1} → [0,m₁) × ⋯ × [0,m_r)` is a bijection
with inverse `ofCoords ms`; since `gadd ms x y = ofCoords ms (addCoords ms (coords ms x) (coords ms y))`,
`({0,…,v-1}, gadd ms)` is the group `ℤ/m₁ × ⋯ × ℤ/m_r`. -/

theorem model_G5x5 : GroupModelOK [5, 5] := by decide +kernel

theorem model_G3x3x3 : GroupModelOK [3, 3, 3] := by decide +kernel

theorem model_G3x9 : GroupModelOK [3, 9] := by decide +kernel

theorem model_G2x2x2x2x2 : GroupModelOK [2, 2, 2, 2, 2] := by decide +kernel

theorem model_G2x2x2x4 : GroupModelOK [2, 2, 2, 4] := by decide +kernel

theorem model_G2x2x8 : GroupModelOK [2, 2, 8] := by decide +kernel

theorem model_G2x4x4 : GroupModelOK [2, 4, 4] := by decide +kernel

theorem model_G2x16 : GroupModelOK [2, 16] := by decide +kernel

theorem model_G4x8 : GroupModelOK [4, 8] := by decide +kernel

theorem model_G3x12 : GroupModelOK [3, 12] := by decide +kernel

theorem model_G6x6 : GroupModelOK [6, 6] := by decide +kernel

theorem model_G2x2x2x6 : GroupModelOK [2, 2, 2, 6] := by decide +kernel

theorem model_G2x2x12 : GroupModelOK [2, 2, 12] := by decide +kernel

theorem model_G4x12 : GroupModelOK [4, 12] := by decide +kernel

theorem model_G3x3x6 : GroupModelOK [3, 3, 6] := by decide +kernel

theorem model_G2x2x2x2x2x2 : GroupModelOK [2, 2, 2, 2, 2, 2] := by decide +kernel

theorem model_G2x2x2x2x4 : GroupModelOK [2, 2, 2, 2, 4] := by decide +kernel

theorem model_G2x2x2x8 : GroupModelOK [2, 2, 2, 8] := by decide +kernel

theorem model_G2x2x4x4 : GroupModelOK [2, 2, 4, 4] := by decide +kernel

theorem model_G2x4x8 : GroupModelOK [2, 4, 8] := by decide +kernel

theorem model_G4x4x4 : GroupModelOK [4, 4, 4] := by decide +kernel

theorem model_G4x16 : GroupModelOK [4, 16] := by decide +kernel

theorem model_G8x8 : GroupModelOK [8, 8] := by decide +kernel


/-! ## Explicit signed difference sets (existence certificates)

Each theorem settles one group-specific case listed as "Open" in the La Jolla SDS
Repository v1.2 and not excluded by He–Wu (arXiv:2608.22936).  Cases marked
"database correction" follow from constructions already in the literature (see README). -/

/-- `SDS(25,12,1,[5,5])`: a (25,12,1) signed difference set in ℤ/5 × ℤ/5, |P| = 9, |N| = 3.
  Eighth-order cyclotomic construction in GF(25) (found by computer search; D = C0 - C2 + C3 + C4). -/
theorem sds_25_12_1_G5x5 : ∃ D : Nat → Int, IsSDS [5, 5] 12 (1) D :=
  ⟨signedOf [5, 5]
    [[1,0],[2,1],[2,4],[0,1],[3,2],[2,2],[3,1],[4,0],[3,4]]
    [[4,2],[4,3],[2,0]], by decide +kernel⟩

/-- `SDS(27,10,1,[3,3,3])`: a (27,10,1) signed difference set in ℤ/3 × ℤ/3 × ℤ/3, |P| = 8, |N| = 2.
  Database correction: follows from the construction of He-Chen-Ge 2024, Thm 4.1, taken with m=1 and D'=(3,2,-1) Paley SDS of Gordon Prop 2.2 (their statement assumes m even). -/
theorem sds_27_10_1_G3x3x3 : ∃ D : Nat → Int, IsSDS [3, 3, 3] 10 (1) D :=
  ⟨signedOf [3, 3, 3]
    [[0,0,1],[1,0,2],[1,1,1],[1,2,1],[1,2,2],[2,1,1],[2,2,0],[2,2,1]]
    [[0,1,2],[1,0,1]], by decide +kernel⟩

/-- `SDS(27,10,1,[3,9])`: a (27,10,1) signed difference set in ℤ/3 × ℤ/9, |P| = 8, |N| = 2.
  Found by computer search (simulated annealing). -/
theorem sds_27_10_1_G3x9 : ∃ D : Nat → Int, IsSDS [3, 9] 10 (1) D :=
  ⟨signedOf [3, 9]
    [[0,6],[0,7],[1,3],[1,7],[2,0],[2,3],[2,6],[2,7]]
    [[0,3],[1,6]], by decide +kernel⟩

/-- `SDS(27,14,5,[3,3,3])`: a (27,14,5) signed difference set in ℤ/3 × ℤ/3 × ℤ/3, |P| = 13, |N| = 1.
  Database correction: follows from Gordon 2023, Prop. 2.3 (Paley (27,13,6) DS in GF(27) plus N={0}); GF(27)+ = Z3^3. -/
theorem sds_27_14_5_G3x3x3 : ∃ D : Nat → Int, IsSDS [3, 3, 3] 14 (5) D :=
  ⟨signedOf [3, 3, 3]
    [[0,0,0],[0,0,1],[0,1,0],[1,0,0],[1,0,2],[1,1,1],[1,1,2],[1,2,1],[2,0,0],[2,1,0],[2,1,1],[2,2,1],[2,2,2]]
    [[0,2,2]], by decide +kernel⟩

/-- `SDS(27,14,5,[3,9])`: a (27,14,5) signed difference set in ℤ/3 × ℤ/9, |P| = 13, |N| = 1.
  Found by computer search (simulated annealing). -/
theorem sds_27_14_5_G3x9 : ∃ D : Nat → Int, IsSDS [3, 9] 14 (5) D :=
  ⟨signedOf [3, 9]
    [[0,0],[0,1],[0,3],[1,3],[1,5],[1,6],[1,7],[1,8],[2,0],[2,4],[2,5],[2,6],[2,8]]
    [[0,2]], by decide +kernel⟩

/-- `SDS(27,17,8,[3,3,3])`: a (27,17,8) signed difference set in ℤ/3 × ℤ/3 × ℤ/3, |P| = 16, |N| = 1.
  Database correction: follows from Gordon 2023, Thm 4.1 (prime-power pair q=3, r=9: GF(3)+GF(9) = Z3^3); the repository files this example under [3,9]. -/
theorem sds_27_17_8_G3x3x3 : ∃ D : Nat → Int, IsSDS [3, 3, 3] 17 (8) D :=
  ⟨signedOf [3, 3, 3]
    [[0,0,0],[0,0,1],[0,0,2],[0,1,0],[0,1,1],[0,1,2],[0,2,0],[1,1,0],[1,1,1],[1,2,0],[1,2,2],[2,0,1],[2,1,1],[2,1,2],[2,2,0],[2,2,1]]
    [[2,2,2]], by decide +kernel⟩

/-- `SDS(32,20,4,[2,2,2,2,2])`: a (32,20,4) signed difference set in ℤ/2 × ℤ/2 × ℤ/2 × ℤ/2 × ℤ/2, |P| = 16, |N| = 4.
  Found by computer search (simulated annealing). -/
theorem sds_32_20_4_G2x2x2x2x2 : ∃ D : Nat → Int, IsSDS [2, 2, 2, 2, 2] 20 (4) D :=
  ⟨signedOf [2, 2, 2, 2, 2]
    [[0,0,0,1,0],[0,0,1,0,0],[0,0,1,1,0],[0,0,1,1,1],[0,1,0,0,0],[0,1,0,1,0],[0,1,0,1,1],[0,1,1,0,0],[0,1,1,0,1],[1,0,0,0,0],[1,0,0,0,1],[1,0,0,1,1],[1,0,1,0,0],[1,0,1,1,0],[1,1,0,0,1],[1,1,1,0,1]]
    [[0,1,1,1,1],[1,0,1,1,1],[1,1,1,0,0],[1,1,1,1,1]], by decide +kernel⟩

/-- `SDS(32,20,4,[2,2,2,4])`: a (32,20,4) signed difference set in ℤ/2 × ℤ/2 × ℤ/2 × ℤ/4, |P| = 16, |N| = 4.
  Found by computer search (simulated annealing). -/
theorem sds_32_20_4_G2x2x2x4 : ∃ D : Nat → Int, IsSDS [2, 2, 2, 4] 20 (4) D :=
  ⟨signedOf [2, 2, 2, 4]
    [[0,0,0,2],[0,0,0,3],[0,0,1,2],[0,1,0,1],[0,1,0,2],[0,1,1,1],[0,1,1,3],[1,0,0,0],[1,0,0,2],[1,0,0,3],[1,0,1,0],[1,0,1,1],[1,0,1,2],[1,1,0,0],[1,1,0,2],[1,1,0,3]]
    [[0,0,0,1],[0,1,0,3],[0,1,1,0],[1,1,1,3]], by decide +kernel⟩

/-- `SDS(32,20,4,[2,2,8])`: a (32,20,4) signed difference set in ℤ/2 × ℤ/2 × ℤ/8, |P| = 16, |N| = 4.
  Found by computer search (simulated annealing). -/
theorem sds_32_20_4_G2x2x8 : ∃ D : Nat → Int, IsSDS [2, 2, 8] 20 (4) D :=
  ⟨signedOf [2, 2, 8]
    [[0,0,3],[0,1,0],[0,1,1],[0,1,3],[0,1,5],[0,1,7],[1,0,2],[1,0,3],[1,0,4],[1,0,6],[1,0,7],[1,1,1],[1,1,2],[1,1,3],[1,1,5],[1,1,6]]
    [[0,0,7],[0,1,4],[1,0,0],[1,1,7]], by decide +kernel⟩

/-- `SDS(32,20,4,[2,4,4])`: a (32,20,4) signed difference set in ℤ/2 × ℤ/4 × ℤ/4, |P| = 16, |N| = 4.
  Found by computer search (simulated annealing). -/
theorem sds_32_20_4_G2x4x4 : ∃ D : Nat → Int, IsSDS [2, 4, 4] 20 (4) D :=
  ⟨signedOf [2, 4, 4]
    [[0,0,0],[0,0,1],[0,0,2],[0,0,3],[0,1,2],[0,2,0],[0,2,1],[0,2,2],[0,3,1],[0,3,3],[1,0,0],[1,0,3],[1,1,0],[1,1,1],[1,2,0],[1,3,2]]
    [[0,1,0],[0,2,3],[1,2,3],[1,3,3]], by decide +kernel⟩

/-- `SDS(32,20,4,[2,16])`: a (32,20,4) signed difference set in ℤ/2 × ℤ/16, |P| = 16, |N| = 4.
  Found by computer search (simulated annealing). -/
theorem sds_32_20_4_G2x16 : ∃ D : Nat → Int, IsSDS [2, 16] 20 (4) D :=
  ⟨signedOf [2, 16]
    [[0,0],[0,1],[0,3],[0,4],[0,5],[0,6],[0,8],[0,11],[0,12],[0,14],[1,2],[1,3],[1,5],[1,9],[1,10],[1,11]]
    [[0,9],[0,13],[1,1],[1,13]], by decide +kernel⟩

/-- `SDS(32,20,4,[4,8])`: a (32,20,4) signed difference set in ℤ/4 × ℤ/8, |P| = 16, |N| = 4.
  Found by computer search (simulated annealing). -/
theorem sds_32_20_4_G4x8 : ∃ D : Nat → Int, IsSDS [4, 8] 20 (4) D :=
  ⟨signedOf [4, 8]
    [[0,0],[0,1],[0,2],[0,6],[0,7],[1,0],[1,2],[1,5],[2,0],[2,1],[2,3],[2,4],[3,0],[3,1],[3,5],[3,6]]
    [[0,4],[1,1],[1,3],[1,7]], by decide +kernel⟩

/-- `SDS(32,28,12,[2,4,4])`: a (32,28,12) signed difference set in ℤ/2 × ℤ/4 × ℤ/4, |P| = 24, |N| = 4.
  Found by computer search (simulated annealing). -/
theorem sds_32_28_12_G2x4x4 : ∃ D : Nat → Int, IsSDS [2, 4, 4] 28 (12) D :=
  ⟨signedOf [2, 4, 4]
    [[0,0,2],[0,0,3],[0,1,0],[0,1,1],[0,1,2],[0,2,0],[0,2,1],[0,2,2],[0,2,3],[0,3,1],[0,3,2],[0,3,3],[1,0,1],[1,0,3],[1,1,0],[1,1,1],[1,1,2],[1,1,3],[1,2,1],[1,2,3],[1,3,0],[1,3,1],[1,3,2],[1,3,3]]
    [[0,0,0],[0,0,1],[0,1,3],[0,3,0]], by decide +kernel⟩

/-- `SDS(32,28,12,[4,8])`: a (32,28,12) signed difference set in ℤ/4 × ℤ/8, |P| = 24, |N| = 4.
  Found by computer search (simulated annealing). -/
theorem sds_32_28_12_G4x8 : ∃ D : Nat → Int, IsSDS [4, 8] 28 (12) D :=
  ⟨signedOf [4, 8]
    [[0,1],[0,2],[0,4],[0,5],[0,6],[1,0],[1,1],[1,2],[1,3],[1,4],[1,5],[1,6],[1,7],[2,0],[2,1],[2,2],[2,4],[2,5],[3,1],[3,3],[3,4],[3,5],[3,6],[3,7]]
    [[0,0],[2,6],[3,0],[3,2]], by decide +kernel⟩

/-- `SDS(36,11,2,[3,12])`: a (36,11,2) signed difference set in ℤ/3 × ℤ/12, |P| = 10, |N| = 1.
  Found by computer search (simulated annealing). -/
theorem sds_36_11_2_G3x12 : ∃ D : Nat → Int, IsSDS [3, 12] 11 (2) D :=
  ⟨signedOf [3, 12]
    [[0,2],[0,5],[0,9],[0,11],[1,1],[1,5],[1,6],[1,11],[2,10],[2,11]]
    [[2,5]], by decide +kernel⟩

/-- `SDS(36,11,2,[6,6])`: a (36,11,2) signed difference set in ℤ/6 × ℤ/6, |P| = 10, |N| = 1.
  Database correction: follows from the PDS trick D = P - 1 with P the (36,10,4,2) rook-graph (2-PCP) PDS in Z6 x Z6 (method of He-Wu Thm 5.3). -/
theorem sds_36_11_2_G6x6 : ∃ D : Nat → Int, IsSDS [6, 6] 11 (2) D :=
  ⟨signedOf [6, 6]
    [[0,5],[1,0],[1,1],[1,3],[2,1],[3,4],[4,3],[5,1],[5,2],[5,3]]
    [[3,5]], by decide +kernel⟩

/-- `SDS(48,24,8,[2,2,2,6])`: a (48,24,8) signed difference set in ℤ/2 × ℤ/2 × ℤ/2 × ℤ/6, |P| = 22, |N| = 2.
  Found by computer search (simulated annealing). -/
theorem sds_48_24_8_G2x2x2x6 : ∃ D : Nat → Int, IsSDS [2, 2, 2, 6] 24 (8) D :=
  ⟨signedOf [2, 2, 2, 6]
    [[0,0,0,0],[0,0,0,1],[0,0,0,3],[0,0,0,5],[0,0,1,4],[0,0,1,5],[0,1,0,0],[0,1,0,2],[0,1,1,1],[0,1,1,2],[0,1,1,3],[0,1,1,4],[1,0,0,1],[1,0,1,0],[1,0,1,1],[1,1,0,0],[1,1,0,1],[1,1,0,3],[1,1,1,0],[1,1,1,1],[1,1,1,3],[1,1,1,4]]
    [[1,0,0,0],[1,1,0,4]], by decide +kernel⟩

/-- `SDS(48,24,8,[2,2,12])`: a (48,24,8) signed difference set in ℤ/2 × ℤ/2 × ℤ/12, |P| = 22, |N| = 2.
  Found by computer search (simulated annealing). -/
theorem sds_48_24_8_G2x2x12 : ∃ D : Nat → Int, IsSDS [2, 2, 12] 24 (8) D :=
  ⟨signedOf [2, 2, 12]
    [[0,0,2],[0,0,3],[0,0,4],[0,0,6],[0,0,9],[0,0,11],[0,1,0],[0,1,1],[0,1,3],[0,1,4],[0,1,7],[0,1,8],[0,1,9],[0,1,11],[1,0,4],[1,0,5],[1,0,6],[1,0,8],[1,1,0],[1,1,2],[1,1,4],[1,1,5]]
    [[0,0,1],[0,0,7]], by decide +kernel⟩

/-- `SDS(48,24,8,[4,12])`: a (48,24,8) signed difference set in ℤ/4 × ℤ/12, |P| = 22, |N| = 2.
  Found by computer search (simulated annealing). -/
theorem sds_48_24_8_G4x12 : ∃ D : Nat → Int, IsSDS [4, 12] 24 (8) D :=
  ⟨signedOf [4, 12]
    [[0,1],[0,2],[0,4],[0,5],[0,7],[1,4],[1,5],[1,7],[1,11],[2,0],[2,2],[2,3],[2,4],[2,6],[2,9],[2,10],[2,11],[3,1],[3,4],[3,5],[3,8],[3,11]]
    [[0,10],[3,2]], by decide +kernel⟩

/-- `SDS(48,32,16,[2,2,2,6])`: a (48,32,16) signed difference set in ℤ/2 × ℤ/2 × ℤ/2 × ℤ/6, |P| = 30, |N| = 2.
  Found by computer search (simulated annealing). -/
theorem sds_48_32_16_G2x2x2x6 : ∃ D : Nat → Int, IsSDS [2, 2, 2, 6] 32 (16) D :=
  ⟨signedOf [2, 2, 2, 6]
    [[0,0,0,0],[0,0,0,1],[0,0,0,2],[0,0,0,4],[0,0,0,5],[0,0,1,0],[0,0,1,1],[0,0,1,4],[0,1,0,3],[0,1,1,0],[0,1,1,1],[0,1,1,2],[0,1,1,5],[1,0,0,0],[1,0,0,2],[1,0,0,5],[1,0,1,0],[1,0,1,1],[1,0,1,2],[1,0,1,4],[1,0,1,5],[1,1,0,0],[1,1,0,2],[1,1,0,4],[1,1,0,5],[1,1,1,1],[1,1,1,2],[1,1,1,3],[1,1,1,4],[1,1,1,5]]
    [[0,1,1,4],[1,1,0,1]], by decide +kernel⟩

/-- `SDS(48,32,16,[2,2,12])`: a (48,32,16) signed difference set in ℤ/2 × ℤ/2 × ℤ/12, |P| = 30, |N| = 2.
  Found by computer search (simulated annealing). -/
theorem sds_48_32_16_G2x2x12 : ∃ D : Nat → Int, IsSDS [2, 2, 12] 32 (16) D :=
  ⟨signedOf [2, 2, 12]
    [[0,0,0],[0,0,1],[0,0,3],[0,0,5],[0,0,6],[0,0,10],[0,0,11],[0,1,0],[0,1,3],[0,1,6],[0,1,7],[0,1,9],[0,1,10],[1,0,0],[1,0,2],[1,0,3],[1,0,5],[1,0,6],[1,0,7],[1,0,8],[1,0,9],[1,0,10],[1,0,11],[1,1,0],[1,1,1],[1,1,2],[1,1,6],[1,1,8],[1,1,9],[1,1,10]]
    [[0,0,9],[1,1,3]], by decide +kernel⟩

/-- `SDS(48,32,16,[4,12])`: a (48,32,16) signed difference set in ℤ/4 × ℤ/12, |P| = 30, |N| = 2.
  Found by computer search (simulated annealing). -/
theorem sds_48_32_16_G4x12 : ∃ D : Nat → Int, IsSDS [4, 12] 32 (16) D :=
  ⟨signedOf [4, 12]
    [[0,1],[0,3],[0,4],[0,5],[0,7],[0,8],[0,9],[0,10],[0,11],[1,0],[1,1],[1,2],[1,4],[1,7],[1,9],[1,10],[1,11],[2,0],[2,5],[2,6],[2,9],[2,11],[3,1],[3,2],[3,4],[3,5],[3,6],[3,7],[3,9],[3,10]]
    [[0,2],[2,3]], by decide +kernel⟩

/-- `SDS(54,46,10,[3,3,6])`: a (54,46,10) signed difference set in ℤ/3 × ℤ/3 × ℤ/6, |P| = 35, |N| = 11.
  Found by computer search (simulated annealing). -/
theorem sds_54_46_10_G3x3x6 : ∃ D : Nat → Int, IsSDS [3, 3, 6] 46 (10) D :=
  ⟨signedOf [3, 3, 6]
    [[0,0,0],[0,0,1],[0,0,3],[0,0,4],[0,1,0],[0,1,3],[0,2,0],[0,2,1],[0,2,2],[0,2,4],[1,0,3],[1,0,4],[1,0,5],[1,1,1],[1,1,2],[1,1,5],[1,2,0],[1,2,2],[1,2,3],[1,2,4],[1,2,5],[2,0,2],[2,0,4],[2,0,5],[2,1,0],[2,1,2],[2,1,3],[2,1,4],[2,1,5],[2,2,0],[2,2,1],[2,2,2],[2,2,3],[2,2,4],[2,2,5]]
    [[0,1,1],[0,1,4],[0,2,3],[0,2,5],[1,0,0],[1,0,1],[1,0,2],[1,1,4],[1,2,1],[2,0,1],[2,1,1]], by decide +kernel⟩

/-- `SDS(64,18,2,[2,2,2,2,2,2])`: a (64,18,2) signed difference set in ℤ/2 × ℤ/2 × ℤ/2 × ℤ/2 × ℤ/2 × ℤ/2, |P| = 15, |N| = 3.
  Found by computer search (simulated annealing). -/
theorem sds_64_18_2_G2x2x2x2x2x2 : ∃ D : Nat → Int, IsSDS [2, 2, 2, 2, 2, 2] 18 (2) D :=
  ⟨signedOf [2, 2, 2, 2, 2, 2]
    [[0,0,0,0,0,0],[0,0,0,1,0,1],[0,0,0,1,1,1],[0,0,1,0,0,0],[0,0,1,0,1,1],[0,1,1,0,0,0],[0,1,1,0,0,1],[0,1,1,0,1,1],[0,1,1,1,1,1],[1,0,0,0,0,0],[1,0,0,0,0,1],[1,0,0,1,0,1],[1,0,1,0,0,1],[1,0,1,1,1,1],[1,1,0,1,0,0]]
    [[0,0,0,1,0,0],[1,0,0,1,1,1],[1,1,0,0,0,1]], by decide +kernel⟩

/-- `SDS(64,18,2,[2,2,2,2,4])`: a (64,18,2) signed difference set in ℤ/2 × ℤ/2 × ℤ/2 × ℤ/2 × ℤ/4, |P| = 15, |N| = 3.
  Found by computer search (simulated annealing). -/
theorem sds_64_18_2_G2x2x2x2x4 : ∃ D : Nat → Int, IsSDS [2, 2, 2, 2, 4] 18 (2) D :=
  ⟨signedOf [2, 2, 2, 2, 4]
    [[0,0,0,0,2],[0,0,0,1,2],[0,0,1,0,0],[0,0,1,0,2],[0,1,0,0,2],[0,1,0,1,3],[0,1,1,0,0],[0,1,1,0,3],[1,0,0,0,0],[1,0,1,0,1],[1,0,1,0,2],[1,0,1,0,3],[1,0,1,1,1],[1,1,0,1,2],[1,1,1,1,2]]
    [[1,0,0,0,3],[1,1,0,1,0],[1,1,1,0,2]], by decide +kernel⟩

/-- `SDS(64,18,2,[2,2,2,8])`: a (64,18,2) signed difference set in ℤ/2 × ℤ/2 × ℤ/2 × ℤ/8, |P| = 15, |N| = 3.
  Found by computer search (simulated annealing). -/
theorem sds_64_18_2_G2x2x2x8 : ∃ D : Nat → Int, IsSDS [2, 2, 2, 8] 18 (2) D :=
  ⟨signedOf [2, 2, 2, 8]
    [[0,0,0,2],[0,0,0,4],[0,1,0,1],[0,1,0,2],[0,1,0,5],[0,1,1,0],[0,1,1,1],[0,1,1,2],[0,1,1,4],[0,1,1,5],[1,0,0,2],[1,0,0,4],[1,1,0,0],[1,1,0,2],[1,1,1,6]]
    [[0,1,0,4],[0,1,1,6],[1,1,1,2]], by decide +kernel⟩

/-- `SDS(64,18,2,[2,2,4,4])`: a (64,18,2) signed difference set in ℤ/2 × ℤ/2 × ℤ/4 × ℤ/4, |P| = 15, |N| = 3.
  Found by computer search (simulated annealing). -/
theorem sds_64_18_2_G2x2x4x4 : ∃ D : Nat → Int, IsSDS [2, 2, 4, 4] 18 (2) D :=
  ⟨signedOf [2, 2, 4, 4]
    [[0,0,0,0],[0,0,0,1],[0,0,1,1],[0,0,1,3],[0,0,2,0],[0,0,2,2],[0,0,3,0],[0,1,0,1],[0,1,0,2],[1,0,0,2],[1,0,2,3],[1,0,3,0],[1,1,0,0],[1,1,1,0],[1,1,3,2]]
    [[0,0,3,2],[1,0,1,2],[1,1,2,1]], by decide +kernel⟩

/-- `SDS(64,18,2,[2,4,8])`: a (64,18,2) signed difference set in ℤ/2 × ℤ/4 × ℤ/8, |P| = 15, |N| = 3.
  Found by computer search (simulated annealing). -/
theorem sds_64_18_2_G2x4x8 : ∃ D : Nat → Int, IsSDS [2, 4, 8] 18 (2) D :=
  ⟨signedOf [2, 4, 8]
    [[0,0,5],[0,1,0],[0,1,5],[0,2,0],[0,2,1],[0,2,5],[0,2,6],[0,2,7],[0,3,2],[1,0,5],[1,1,3],[1,1,4],[1,2,2],[1,2,4],[1,3,6]]
    [[0,1,7],[1,1,1],[1,2,3]], by decide +kernel⟩

/-- `SDS(64,18,2,[4,4,4])`: a (64,18,2) signed difference set in ℤ/4 × ℤ/4 × ℤ/4, |P| = 15, |N| = 3.
  Found by computer search (simulated annealing). -/
theorem sds_64_18_2_G4x4x4 : ∃ D : Nat → Int, IsSDS [4, 4, 4] 18 (2) D :=
  ⟨signedOf [4, 4, 4]
    [[0,0,3],[0,1,3],[1,0,0],[1,1,0],[1,1,1],[1,1,3],[1,2,1],[1,2,2],[1,3,0],[1,3,2],[2,0,3],[2,1,0],[2,3,0],[3,0,2],[3,1,0]]
    [[1,0,2],[1,0,3],[2,3,3]], by decide +kernel⟩

/-- `SDS(64,18,2,[8,8])`: a (64,18,2) signed difference set in ℤ/8 × ℤ/8, |P| = 15, |N| = 3.
  Found by computer search (simulated annealing). -/
theorem sds_64_18_2_G8x8 : ∃ D : Nat → Int, IsSDS [8, 8] 18 (2) D :=
  ⟨signedOf [8, 8]
    [[1,1],[1,6],[1,7],[2,0],[2,4],[3,1],[3,3],[3,4],[3,7],[5,1],[5,2],[5,3],[6,2],[6,6],[7,0]]
    [[1,5],[5,5],[7,1]], by decide +kernel⟩

/-- `SDS(64,22,6,[2,2,2,2,2,2])`: a (64,22,6) signed difference set in ℤ/2 × ℤ/2 × ℤ/2 × ℤ/2 × ℤ/2 × ℤ/2, |P| = 21, |N| = 1.
  Database correction: constructed by He-Wu 2026, Thm 5.3 / Example 5.4 (not reflected in the repository snapshot). -/
theorem sds_64_22_6_G2x2x2x2x2x2 : ∃ D : Nat → Int, IsSDS [2, 2, 2, 2, 2, 2] 22 (6) D :=
  ⟨signedOf [2, 2, 2, 2, 2, 2]
    [[0,0,0,0,1,0],[0,0,0,1,1,0],[0,0,0,1,1,1],[0,0,1,0,0,0],[0,0,1,0,1,0],[0,0,1,0,1,1],[0,0,1,1,0,1],[0,0,1,1,1,0],[0,1,0,0,1,0],[0,1,0,1,0,0],[0,1,0,1,1,0],[0,1,1,0,0,1],[1,0,0,1,0,1],[1,0,0,1,1,0],[1,0,0,1,1,1],[1,0,1,1,0,1],[1,1,0,0,0,0],[1,1,0,0,0,1],[1,1,0,1,1,0],[1,1,1,0,0,0],[1,1,1,1,1,1]]
    [[1,1,1,0,0,1]], by decide +kernel⟩

/-- `SDS(64,22,6,[2,2,2,2,4])`: a (64,22,6) signed difference set in ℤ/2 × ℤ/2 × ℤ/2 × ℤ/2 × ℤ/4, |P| = 21, |N| = 1.
  Found by computer search (simulated annealing).
  Possibly known-type: would follow from the PDS trick if a Latin-square-type LS_3(8) PDS (64,21,8,6) exists in this group (not checked). -/
theorem sds_64_22_6_G2x2x2x2x4 : ∃ D : Nat → Int, IsSDS [2, 2, 2, 2, 4] 22 (6) D :=
  ⟨signedOf [2, 2, 2, 2, 4]
    [[0,0,0,0,3],[0,0,0,1,3],[0,0,1,0,0],[0,0,1,0,2],[0,0,1,0,3],[0,0,1,1,0],[0,0,1,1,2],[0,0,1,1,3],[0,1,0,0,2],[0,1,0,1,3],[0,1,1,0,1],[0,1,1,1,0],[1,0,0,0,0],[1,0,0,0,3],[1,0,1,0,1],[1,0,1,0,2],[1,1,0,0,1],[1,1,0,0,3],[1,1,1,0,3],[1,1,1,1,0],[1,1,1,1,1]]
    [[1,1,1,0,0]], by decide +kernel⟩

/-- `SDS(64,22,6,[2,2,2,8])`: a (64,22,6) signed difference set in ℤ/2 × ℤ/2 × ℤ/2 × ℤ/8, |P| = 21, |N| = 1.
  Found by computer search (simulated annealing).
  Possibly known-type: would follow from the PDS trick if a Latin-square-type LS_3(8) PDS (64,21,8,6) exists in this group (not checked). -/
theorem sds_64_22_6_G2x2x2x8 : ∃ D : Nat → Int, IsSDS [2, 2, 2, 8] 22 (6) D :=
  ⟨signedOf [2, 2, 2, 8]
    [[0,0,0,0],[0,0,0,2],[0,0,0,6],[0,0,0,7],[0,0,1,0],[0,0,1,3],[0,0,1,6],[0,1,0,0],[0,1,0,5],[0,1,1,0],[0,1,1,2],[0,1,1,3],[0,1,1,7],[1,0,0,0],[1,0,0,2],[1,0,0,3],[1,0,0,4],[1,0,1,1],[1,0,1,7],[1,1,0,5],[1,1,0,6]]
    [[0,0,1,5]], by decide +kernel⟩

/-- `SDS(64,22,6,[2,2,4,4])`: a (64,22,6) signed difference set in ℤ/2 × ℤ/2 × ℤ/4 × ℤ/4, |P| = 21, |N| = 1.
  Database correction: follows from the PDS trick with the 3-PCP PDS in H x H, H = Z2 x Z4 (method of He-Wu Thm 5.3). -/
theorem sds_64_22_6_G2x2x4x4 : ∃ D : Nat → Int, IsSDS [2, 2, 4, 4] 22 (6) D :=
  ⟨signedOf [2, 2, 4, 4]
    [[0,0,1,1],[0,0,1,2],[0,1,0,3],[0,1,1,1],[0,1,2,3],[0,1,3,0],[0,1,3,1],[0,1,3,3],[1,0,0,3],[1,0,1,2],[1,0,2,1],[1,0,3,0],[1,0,3,1],[1,0,3,2],[1,1,0,1],[1,1,0,2],[1,1,1,2],[1,1,2,2],[1,1,2,3],[1,1,3,1],[1,1,3,3]]
    [[1,1,1,1]], by decide +kernel⟩

/-- `SDS(64,22,6,[2,4,8])`: a (64,22,6) signed difference set in ℤ/2 × ℤ/4 × ℤ/8, |P| = 21, |N| = 1.
  Found by computer search (simulated annealing).
  Possibly known-type: would follow from the PDS trick if a Latin-square-type LS_3(8) PDS (64,21,8,6) exists in this group (not checked). -/
theorem sds_64_22_6_G2x4x8 : ∃ D : Nat → Int, IsSDS [2, 4, 8] 22 (6) D :=
  ⟨signedOf [2, 4, 8]
    [[0,0,0],[0,0,5],[0,1,0],[0,1,1],[0,1,4],[0,1,7],[0,2,1],[0,2,2],[0,2,4],[0,2,6],[0,3,1],[0,3,7],[1,0,0],[1,0,1],[1,0,2],[1,0,3],[1,0,6],[1,1,0],[1,1,4],[1,2,3],[1,2,4]]
    [[1,0,5]], by decide +kernel⟩

/-- `SDS(64,22,6,[4,4,4])`: a (64,22,6) signed difference set in ℤ/4 × ℤ/4 × ℤ/4, |P| = 21, |N| = 1.
  Found by computer search (simulated annealing).
  Possibly known-type: would follow from the PDS trick if a Latin-square-type LS_3(8) PDS (64,21,8,6) exists in this group (not checked). -/
theorem sds_64_22_6_G4x4x4 : ∃ D : Nat → Int, IsSDS [4, 4, 4] 22 (6) D :=
  ⟨signedOf [4, 4, 4]
    [[0,0,2],[0,1,3],[0,2,0],[0,2,2],[1,0,2],[1,2,2],[1,2,3],[1,3,2],[2,0,0],[2,0,1],[2,0,2],[2,1,1],[2,2,0],[2,2,3],[2,3,0],[2,3,2],[3,0,1],[3,2,2],[3,3,0],[3,3,1],[3,3,3]]
    [[3,2,0]], by decide +kernel⟩

/-- `SDS(64,22,6,[4,16])`: a (64,22,6) signed difference set in ℤ/4 × ℤ/16, |P| = 21, |N| = 1.
  Found by computer search (simulated annealing).
  Possibly known-type: would follow from the PDS trick if a Latin-square-type LS_3(8) PDS (64,21,8,6) exists in this group (not checked). -/
theorem sds_64_22_6_G4x16 : ∃ D : Nat → Int, IsSDS [4, 16] 22 (6) D :=
  ⟨signedOf [4, 16]
    [[0,1],[0,2],[0,4],[0,6],[0,7],[0,10],[0,11],[0,14],[1,3],[1,4],[1,9],[1,15],[2,1],[2,3],[2,4],[2,15],[3,4],[3,5],[3,7],[3,11],[3,13]]
    [[3,1]], by decide +kernel⟩

/-- `SDS(64,22,6,[8,8])`: a (64,22,6) signed difference set in ℤ/8 × ℤ/8, |P| = 21, |N| = 1.
  Database correction: follows from the PDS trick with the 3-PCP PDS in Z8 x Z8 (method of He-Wu Thm 5.3). -/
theorem sds_64_22_6_G8x8 : ∃ D : Nat → Int, IsSDS [8, 8] 22 (6) D :=
  ⟨signedOf [8, 8]
    [[1,0],[0,1],[1,1],[2,0],[0,2],[2,2],[3,0],[0,3],[3,3],[4,0],[0,4],[4,4],[5,0],[0,5],[5,5],[6,0],[0,6],[6,6],[7,0],[0,7],[7,7]]
    [[0,0]], by decide +kernel⟩

/-- `SDS(64,46,30,[2,2,2,2,2,2])`: a (64,46,30) signed difference set in ℤ/2 × ℤ/2 × ℤ/2 × ℤ/2 × ℤ/2 × ℤ/2, |P| = 45, |N| = 1.
  Database correction: follows from the PDS trick D = P - 1 with P the complement of a negative-Latin-square-type NL_2(8) PDS (64,18,2,6) in Z2^6 (our search found exactly such an object). -/
theorem sds_64_46_30_G2x2x2x2x2x2 : ∃ D : Nat → Int, IsSDS [2, 2, 2, 2, 2, 2] 46 (30) D :=
  ⟨signedOf [2, 2, 2, 2, 2, 2]
    [[0,0,0,0,0,0],[0,0,0,0,0,1],[0,0,0,0,1,0],[0,0,0,0,1,1],[0,0,0,1,0,1],[0,0,0,1,1,1],[0,0,1,0,0,0],[0,0,1,0,0,1],[0,0,1,0,1,1],[0,0,1,1,0,0],[0,0,1,1,1,0],[0,0,1,1,1,1],[0,1,0,0,0,0],[0,1,0,0,0,1],[0,1,0,0,1,0],[0,1,0,1,0,0],[0,1,0,1,1,0],[0,1,0,1,1,1],[0,1,1,0,0,0],[0,1,1,0,0,1],[0,1,1,0,1,0],[0,1,1,0,1,1],[0,1,1,1,0,0],[0,1,1,1,1,1],[1,0,0,0,0,0],[1,0,0,0,0,1],[1,0,0,0,1,0],[1,0,0,0,1,1],[1,0,0,1,0,0],[1,0,0,1,0,1],[1,0,0,1,1,0],[1,0,0,1,1,1],[1,0,1,0,0,0],[1,0,1,1,0,0],[1,0,1,1,1,0],[1,0,1,1,1,1],[1,1,0,0,0,0],[1,1,0,0,1,0],[1,1,0,0,1,1],[1,1,0,1,0,1],[1,1,1,0,0,0],[1,1,1,0,0,1],[1,1,1,0,1,0],[1,1,1,1,0,0],[1,1,1,1,0,1]]
    [[1,1,1,0,1,1]], by decide +kernel⟩

/-- `SDS(64,46,30,[2,2,2,2,4])`: a (64,46,30) signed difference set in ℤ/2 × ℤ/2 × ℤ/2 × ℤ/2 × ℤ/4, |P| = 45, |N| = 1.
  Found by computer search (simulated annealing).
  Possibly known-type: would follow from the PDS trick if an NL_2(8) PDS (64,18,2,6) exists in this group (not checked). -/
theorem sds_64_46_30_G2x2x2x2x4 : ∃ D : Nat → Int, IsSDS [2, 2, 2, 2, 4] 46 (30) D :=
  ⟨signedOf [2, 2, 2, 2, 4]
    [[0,0,0,0,0],[0,0,0,0,1],[0,0,0,0,2],[0,0,0,0,3],[0,0,0,1,0],[0,0,0,1,1],[0,0,0,1,2],[0,0,0,1,3],[0,0,1,0,0],[0,0,1,0,1],[0,0,1,0,3],[0,0,1,1,0],[0,0,1,1,2],[0,0,1,1,3],[0,1,0,0,1],[0,1,0,0,2],[0,1,0,1,0],[0,1,0,1,1],[0,1,0,1,2],[0,1,0,1,3],[0,1,1,0,0],[0,1,1,0,1],[0,1,1,0,2],[0,1,1,1,3],[1,0,0,0,0],[1,0,0,0,1],[1,0,0,1,1],[1,0,0,1,2],[1,0,1,0,1],[1,0,1,0,2],[1,0,1,0,3],[1,0,1,1,0],[1,0,1,1,2],[1,0,1,1,3],[1,1,0,0,0],[1,1,0,0,1],[1,1,0,0,2],[1,1,0,0,3],[1,1,0,1,0],[1,1,0,1,1],[1,1,1,0,0],[1,1,1,0,1],[1,1,1,0,2],[1,1,1,1,0],[1,1,1,1,2]]
    [[1,1,1,1,3]], by decide +kernel⟩

/-- `SDS(64,46,30,[2,2,2,8])`: a (64,46,30) signed difference set in ℤ/2 × ℤ/2 × ℤ/2 × ℤ/8, |P| = 45, |N| = 1.
  Found by computer search (simulated annealing).
  Possibly known-type: would follow from the PDS trick if an NL_2(8) PDS (64,18,2,6) exists in this group (not checked). -/
theorem sds_64_46_30_G2x2x2x8 : ∃ D : Nat → Int, IsSDS [2, 2, 2, 8] 46 (30) D :=
  ⟨signedOf [2, 2, 2, 8]
    [[0,0,0,1],[0,0,0,2],[0,0,0,3],[0,0,0,6],[0,0,0,7],[0,0,1,0],[0,0,1,1],[0,0,1,2],[0,0,1,3],[0,0,1,7],[0,1,0,0],[0,1,0,3],[0,1,0,5],[0,1,0,6],[0,1,0,7],[0,1,1,0],[0,1,1,2],[0,1,1,3],[0,1,1,4],[0,1,1,5],[0,1,1,7],[1,0,0,0],[1,0,0,1],[1,0,0,3],[1,0,0,4],[1,0,0,5],[1,0,0,6],[1,0,0,7],[1,0,1,0],[1,0,1,1],[1,0,1,2],[1,0,1,3],[1,0,1,5],[1,0,1,6],[1,0,1,7],[1,1,0,0],[1,1,0,2],[1,1,0,6],[1,1,1,0],[1,1,1,1],[1,1,1,3],[1,1,1,4],[1,1,1,5],[1,1,1,6],[1,1,1,7]]
    [[0,1,1,6]], by decide +kernel⟩

/-- `SDS(64,46,30,[2,2,4,4])`: a (64,46,30) signed difference set in ℤ/2 × ℤ/2 × ℤ/4 × ℤ/4, |P| = 45, |N| = 1.
  Found by computer search (simulated annealing).
  Possibly known-type: would follow from the PDS trick if an NL_2(8) PDS (64,18,2,6) exists in this group (not checked). -/
theorem sds_64_46_30_G2x2x4x4 : ∃ D : Nat → Int, IsSDS [2, 2, 4, 4] 46 (30) D :=
  ⟨signedOf [2, 2, 4, 4]
    [[0,0,0,0],[0,0,0,1],[0,0,0,3],[0,0,1,0],[0,0,1,1],[0,0,1,3],[0,0,2,1],[0,0,2,2],[0,0,2,3],[0,0,3,0],[0,0,3,2],[0,0,3,3],[0,1,0,0],[0,1,0,1],[0,1,0,2],[0,1,1,0],[0,1,1,1],[0,1,1,3],[0,1,2,0],[0,1,2,2],[0,1,2,3],[1,0,0,0],[1,0,0,2],[1,0,0,3],[1,0,1,0],[1,0,1,1],[1,0,1,2],[1,0,2,0],[1,0,2,2],[1,0,2,3],[1,0,3,0],[1,0,3,1],[1,0,3,3],[1,1,0,0],[1,1,0,1],[1,1,0,2],[1,1,1,0],[1,1,1,1],[1,1,1,3],[1,1,2,0],[1,1,2,1],[1,1,2,2],[1,1,3,0],[1,1,3,1],[1,1,3,2]]
    [[0,1,3,1]], by decide +kernel⟩

/-- `SDS(64,46,30,[2,4,8])`: a (64,46,30) signed difference set in ℤ/2 × ℤ/4 × ℤ/8, |P| = 45, |N| = 1.
  Found by computer search (simulated annealing).
  Possibly known-type: would follow from the PDS trick if an NL_2(8) PDS (64,18,2,6) exists in this group (not checked). -/
theorem sds_64_46_30_G2x4x8 : ∃ D : Nat → Int, IsSDS [2, 4, 8] 46 (30) D :=
  ⟨signedOf [2, 4, 8]
    [[0,0,4],[0,0,6],[0,0,7],[0,1,0],[0,1,1],[0,1,2],[0,1,3],[0,1,4],[0,1,6],[0,1,7],[0,2,0],[0,2,1],[0,2,5],[0,2,6],[0,2,7],[0,3,0],[0,3,2],[0,3,4],[0,3,5],[0,3,6],[1,0,0],[1,0,1],[1,0,2],[1,0,3],[1,0,4],[1,0,5],[1,0,7],[1,1,0],[1,1,1],[1,1,3],[1,1,4],[1,1,5],[1,1,6],[1,1,7],[1,2,0],[1,2,1],[1,2,2],[1,2,4],[1,2,5],[1,2,7],[1,3,0],[1,3,2],[1,3,3],[1,3,4],[1,3,7]]
    [[1,2,3]], by decide +kernel⟩

/-- `SDS(64,46,30,[4,4,4])`: a (64,46,30) signed difference set in ℤ/4 × ℤ/4 × ℤ/4, |P| = 45, |N| = 1.
  Found by computer search (simulated annealing).
  Possibly known-type: would follow from the PDS trick if an NL_2(8) PDS (64,18,2,6) exists in this group (not checked). -/
theorem sds_64_46_30_G4x4x4 : ∃ D : Nat → Int, IsSDS [4, 4, 4] 46 (30) D :=
  ⟨signedOf [4, 4, 4]
    [[0,0,0],[0,0,1],[0,0,2],[0,0,3],[0,1,1],[0,1,2],[0,2,1],[0,2,2],[0,2,3],[0,3,1],[0,3,2],[0,3,3],[1,0,0],[1,0,1],[1,0,2],[1,0,3],[1,1,0],[1,1,1],[1,1,2],[1,1,3],[1,2,0],[1,2,3],[1,3,1],[1,3,2],[1,3,3],[2,0,0],[2,0,1],[2,0,2],[2,0,3],[2,1,0],[2,1,2],[2,2,1],[2,2,2],[2,2,3],[2,3,0],[2,3,2],[2,3,3],[3,0,0],[3,0,1],[3,1,1],[3,1,3],[3,2,1],[3,2,2],[3,2,3],[3,3,2]]
    [[1,2,2]], by decide +kernel⟩

/-- `SDS(64,46,30,[8,8])`: a (64,46,30) signed difference set in ℤ/8 × ℤ/8, |P| = 45, |N| = 1.
  Found by computer search (simulated annealing).
  Possibly known-type: would follow from the PDS trick if an NL_2(8) PDS (64,18,2,6) exists in this group (not checked). -/
theorem sds_64_46_30_G8x8 : ∃ D : Nat → Int, IsSDS [8, 8] 46 (30) D :=
  ⟨signedOf [8, 8]
    [[0,0],[0,1],[0,2],[0,3],[0,4],[0,5],[0,6],[0,7],[1,0],[1,1],[1,2],[1,3],[1,5],[1,6],[2,2],[2,5],[2,6],[2,7],[3,1],[3,2],[3,3],[3,4],[3,6],[3,7],[4,0],[4,2],[4,4],[4,6],[4,7],[5,0],[5,1],[5,2],[5,5],[5,6],[5,7],[6,0],[6,1],[6,4],[6,7],[7,2],[7,3],[7,4],[7,5],[7,6],[7,7]]
    [[4,3]], by decide +kernel⟩


/-! ## Axiom report -/

#print axioms no_SDS_9_8_1_Z3xZ3

#print axioms model_G5x5

#print axioms model_G3x3x3

#print axioms model_G3x9

#print axioms model_G2x2x2x2x2

#print axioms model_G2x2x2x4

#print axioms model_G2x2x8

#print axioms model_G2x4x4

#print axioms model_G2x16

#print axioms model_G4x8

#print axioms model_G3x12

#print axioms model_G6x6

#print axioms model_G2x2x2x6

#print axioms model_G2x2x12

#print axioms model_G4x12

#print axioms model_G3x3x6

#print axioms model_G2x2x2x2x2x2

#print axioms model_G2x2x2x2x4

#print axioms model_G2x2x2x8

#print axioms model_G2x2x4x4

#print axioms model_G2x4x8

#print axioms model_G4x4x4

#print axioms model_G4x16

#print axioms model_G8x8

#print axioms sds_25_12_1_G5x5

#print axioms sds_27_10_1_G3x3x3

#print axioms sds_27_10_1_G3x9

#print axioms sds_27_14_5_G3x3x3

#print axioms sds_27_14_5_G3x9

#print axioms sds_27_17_8_G3x3x3

#print axioms sds_32_20_4_G2x2x2x2x2

#print axioms sds_32_20_4_G2x2x2x4

#print axioms sds_32_20_4_G2x2x8

#print axioms sds_32_20_4_G2x4x4

#print axioms sds_32_20_4_G2x16

#print axioms sds_32_20_4_G4x8

#print axioms sds_32_28_12_G2x4x4

#print axioms sds_32_28_12_G4x8

#print axioms sds_36_11_2_G3x12

#print axioms sds_36_11_2_G6x6

#print axioms sds_48_24_8_G2x2x2x6

#print axioms sds_48_24_8_G2x2x12

#print axioms sds_48_24_8_G4x12

#print axioms sds_48_32_16_G2x2x2x6

#print axioms sds_48_32_16_G2x2x12

#print axioms sds_48_32_16_G4x12

#print axioms sds_54_46_10_G3x3x6

#print axioms sds_64_18_2_G2x2x2x2x2x2

#print axioms sds_64_18_2_G2x2x2x2x4

#print axioms sds_64_18_2_G2x2x2x8

#print axioms sds_64_18_2_G2x2x4x4

#print axioms sds_64_18_2_G2x4x8

#print axioms sds_64_18_2_G4x4x4

#print axioms sds_64_18_2_G8x8

#print axioms sds_64_22_6_G2x2x2x2x2x2

#print axioms sds_64_22_6_G2x2x2x2x4

#print axioms sds_64_22_6_G2x2x2x8

#print axioms sds_64_22_6_G2x2x4x4

#print axioms sds_64_22_6_G2x4x8

#print axioms sds_64_22_6_G4x4x4

#print axioms sds_64_22_6_G4x16

#print axioms sds_64_22_6_G8x8

#print axioms sds_64_46_30_G2x2x2x2x2x2

#print axioms sds_64_46_30_G2x2x2x2x4

#print axioms sds_64_46_30_G2x2x2x8

#print axioms sds_64_46_30_G2x2x4x4

#print axioms sds_64_46_30_G2x4x8

#print axioms sds_64_46_30_G4x4x4

#print axioms sds_64_46_30_G8x8
