set_option Elab.async false

/-
  A (6,9)-graph on 4368 vertices: a 6-regular graph of girth exactly 9.

  The graph is a voltage lift of a 2-vertex base multigraph with voltages in SL(2,13):
  vertices are pairs (u, M) with u < 2 a base vertex and M ∈ SL(2,13);
  (u, M) is adjacent to (w, M·A) for every dart u → w of the base graph carrying voltage A.

  Everything is checked by the Lean kernel (`decide +kernel`); no `native_decide`.
-/

namespace Cage

/-! ## Part A. Definitions used in the main statement -/

/-- A graph on `Fin n` given by a Boolean adjacency relation is *simple* if the relation is
symmetric and irreflexive. -/
def IsSimpleGraph {n : Nat} (adj : Fin n → Fin n → Bool) : Prop :=
  (∀ u v, adj u v = adj v u) ∧ (∀ v, adj v v = false)

/-- degree of `v`: the number of vertices `w` with `adj v w`. -/
def degree {n : Nat} (adj : Fin n → Fin n → Bool) (v : Fin n) : Nat :=
  ((List.finRange n).filter (fun w => adj v w)).length

/-- `k`-regular: every vertex has degree `k`. -/
def IsRegular {n : Nat} (adj : Fin n → Fin n → Bool) (k : Nat) : Prop :=
  ∀ v, degree adj v = k

/-- `c = [c₀, …, c_{L-1}]` is a cycle: at least 3 pairwise distinct vertices with
`cᵢ ~ c_{(i+1) mod L}` for all `i`. -/
def IsCycle {α : Type} (adj : α → α → Bool) (c : List α) : Prop :=
  3 ≤ c.length ∧ c.Nodup ∧
    ∀ i (h : i < c.length), adj c[i] (c[(i + 1) % c.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) h))) = true


/-- girth exactly `g`: some cycle has length `g`, and every cycle has length at least `g`. -/
def HasGirth {n : Nat} (adj : Fin n → Fin n → Bool) (g : Nat) : Prop :=
  (∃ c, IsCycle adj c ∧ c.length = g) ∧ ∀ c, IsCycle adj c → g ≤ c.length

/-! ## Part B. Generic lemmas (walk enumeration and its soundness) -/


/-- Bitset-based duplicate test for a list of natural numbers. -/
def allDistinct : List Nat → Nat → Bool
  | [], _ => true
  | x :: xs, acc => !(acc.testBit x) && allDistinct xs (acc ||| (1 <<< x))

theorem testBit_one_shiftLeft (x y : Nat) : (1 <<< x).testBit y = decide (x = y) := by
  rw [Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]

theorem allDistinct_sound : ∀ (l : List Nat) (acc : Nat), allDistinct l acc = true →
    l.Nodup ∧ ∀ x ∈ l, acc.testBit x = false
  | [], _, _ => ⟨List.nodup_nil, by simp⟩
  | x :: xs, acc, h => by
    simp only [allDistinct, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ih1, ih2⟩ := allDistinct_sound xs _ h2
    refine ⟨List.nodup_cons.2 ⟨?_, ih1⟩, ?_⟩
    · intro hx
      have := ih2 x hx
      rw [Nat.testBit_or, testBit_one_shiftLeft] at this
      simp at this
    · intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact h1
      · have := ih2 y hy
        rw [Nat.testBit_or, Bool.or_eq_false_iff] at this
        exact this.1

theorem nodup_map_inj {α β : Type} (g : α → β) : ∀ (l : List α), (l.map g).Nodup →
    ∀ x ∈ l, ∀ y ∈ l, g x = g y → x = y
  | [], _, x, hx, _, _, _ => absurd hx List.not_mem_nil
  | a :: l, h, x, hx, y, hy, hxy => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 hx with rfl | hx' <;> rcases List.mem_cons.1 hy with rfl | hy'
    · rfl
    · exact absurd (List.mem_map.2 ⟨y, hy', hxy.symm⟩) h.1
    · exact absurd (List.mem_map.2 ⟨x, hx', hxy⟩) h.1
    · exact nodup_map_inj g l h.2 x hx' y hy' hxy

section Walks
variable {V : Type} (nbrs : V → List V)

/-- one-step extensions of a reversed non-backtracking walk `w = [current, previous, ...]` -/
def extend [DecidableEq V] (w : List V) : List (List V) :=
  match w with
  | [] => []
  | [x] => (nbrs x).map (fun y => [y, x])
  | x :: q :: rest => ((nbrs x).filter (fun y => y != q)).map (fun y => y :: x :: q :: rest)

/-- all reversed non-backtracking walks of length `k` starting at `r` -/
def layer [DecidableEq V] (r : V) : Nat → List (List V)
  | 0 => [[r]]
  | k + 1 => (layer r k).flatMap (extend nbrs)

/-- the list `[f k, f (k-1), …, f 0]` -/
def walkList (f : Nat → V) : Nat → List V
  | 0 => [f 0]
  | k + 1 => f (k + 1) :: walkList f k

theorem walkList_head (f : Nat → V) : ∀ k, ∃ t, walkList f k = f k :: t
  | 0 => ⟨[], rfl⟩
  | k + 1 => ⟨walkList f k, rfl⟩

theorem walkList_length (f : Nat → V) : ∀ k, (walkList f k).length = k + 1
  | 0 => rfl
  | k + 1 => by simp [walkList, walkList_length f k]

theorem walkList_getElem (f : Nat → V) : ∀ k i (h : i < (walkList f k).length),
    (walkList f k)[i] = f (k - i)
  | 0, 0, _ => rfl
  | 0, i + 1, h => by simp [walkList] at h
  | k + 1, 0, _ => rfl
  | k + 1, i + 1, h => by
    simp only [walkList, List.getElem_cons_succ]
    rw [walkList_getElem f k i]
    congr 1
    omega

/-- Completeness of the enumeration: every non-backtracking walk appears in `layer`. -/
theorem walkList_mem_layer [DecidableEq V] (r : V) (f : Nat → V) (h0 : f 0 = r) :
    ∀ k, (∀ i, i < k → f (i + 1) ∈ nbrs (f i)) → (∀ i, i + 2 ≤ k → f (i + 2) ≠ f i) →
      walkList f k ∈ layer nbrs r k
  | 0, _, _ => by simp [walkList, layer, h0]
  | k + 1, hn, hb => by
    have ih := walkList_mem_layer r f h0 k (fun i hi => hn i (by omega)) (fun i hi => hb i (by omega))
    simp only [layer, List.mem_flatMap]
    refine ⟨walkList f k, ih, ?_⟩
    match k, ih with
    | 0, _ =>
      simp only [walkList, extend, List.mem_map]
      exact ⟨f 1, hn 0 (by omega), rfl⟩
    | k' + 1, _ =>
      obtain ⟨t, ht⟩ := walkList_head f k'
      have hw : walkList f (k' + 1 + 1) = f (k' + 2) :: f (k' + 1) :: f k' :: t := by
        simp [walkList, ht]
      have hw' : walkList f (k' + 1) = f (k' + 1) :: f k' :: t := by simp [walkList, ht]
      rw [hw, hw']
      simp only [extend, List.mem_map, List.mem_filter]
      refine ⟨f (k' + 2), ⟨hn (k' + 1) (by omega), ?_⟩, rfl⟩
      have := hb k' (by omega)
      simpa using this


/-- codes of the end vertices of all non-backtracking walks of length `≤ R` from `r` -/
def headCodes [DecidableEq V] (enc : V → Nat) (r : V) (R : Nat) : List Nat :=
  ((List.range (R + 1)).flatMap (layer nbrs r)).map (fun w => enc (w.headD r))

theorem getD_eq {α : Type} (c : List α) (d : α) (i : Nat) (h : i < c.length) : c.getD i d = c[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-- Soundness of the local girth check: if all non-backtracking walks of length `≤ R` from `r`
have distinct end vertices, then no cycle of length `≤ 2R` starts at `r`. -/
theorem no_short_cycle [DecidableEq V] (enc : V → Nat) (adj : V → V → Bool)
    (hadj : ∀ x y, adj x y = true → y ∈ nbrs x)
    (r : V) (R : Nat) (hchk : allDistinct (headCodes nbrs enc r R) 0 = true)
    (c : List V) (hc : IsCycle adj c)
    (hsym : ∀ x ∈ c, ∀ y ∈ c, adj x y = true → adj y x = true)
    (h0 : c.getD 0 r = r) (hL : c.length ≤ 2 * R) : False := by
  obtain ⟨h3, hnd, hcyc⟩ := hc
  have hnd' := List.pairwise_iff_getElem.1 hnd
  have hne : ∀ i j (hi : i < c.length) (hj : j < c.length), i ≠ j → c[i] ≠ c[j] := by
    intro i j hi hj hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact hnd' i j hi hj h
    · exact fun e => hnd' j i hj hi h e.symm
  -- generic facts
  have hmem : ∀ i (hi : i < c.length), c[i] ∈ c := fun i hi => List.getElem_mem hi
  have hstep : ∀ i (hi : i + 1 < c.length), c[i + 1] ∈ nbrs c[i] := by
    intro i hi
    have := hcyc i (by omega)
    have e : (i + 1) % c.length = i + 1 := Nat.mod_eq_of_lt hi
    simp only [e] at this
    exact hadj _ _ this
  have hstep' : ∀ i (hi : i + 1 < c.length), c[i] ∈ nbrs c[i + 1] := by
    intro i hi
    have := hcyc i (by omega)
    have e : (i + 1) % c.length = i + 1 := Nat.mod_eq_of_lt hi
    simp only [e] at this
    exact hadj _ _ (hsym _ (hmem _ _) _ (hmem _ _) this)
  have hlast : c[0] ∈ nbrs c[c.length - 1] := by
    have := hcyc (c.length - 1) (by omega)
    have e : (c.length - 1 + 1) % c.length = 0 := by
      rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
    simp only [e] at this
    exact hadj _ _ this
  have hlast' : c[c.length - 1] ∈ nbrs c[0] := by
    have := hcyc (c.length - 1) (by omega)
    have e : (c.length - 1 + 1) % c.length = 0 := by
      rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
    simp only [e] at this
    exact hadj _ _ (hsym _ (hmem _ _) _ (hmem _ _) this)
  have hr : c[0] = r := by rw [← getD_eq c r 0 (by omega)]; exact h0
  -- the two halves
  let L := c.length
  let a := L / 2
  let f1 : Nat → V := fun i => c.getD i r
  let f2 : Nat → V := fun i => c.getD ((L - i) % L) r
  have hW1 : walkList f1 a ∈ layer nbrs r a := by
    apply walkList_mem_layer nbrs r f1 h0
    · intro i hi
      show c.getD (i + 1) r ∈ nbrs (c.getD i r)
      rw [getD_eq c r (i + 1) (by omega), getD_eq c r i (by omega)]
      exact hstep i (by omega)
    · intro i hi
      show c.getD (i + 2) r ≠ c.getD i r
      rw [getD_eq c r (i + 2) (by omega), getD_eq c r i (by omega)]
      exact hne _ _ _ _ (by omega)
  have hW2 : walkList f2 (L - a) ∈ layer nbrs r (L - a) := by
    apply walkList_mem_layer nbrs r f2
    · show c.getD ((L - 0) % L) r = r
      rw [Nat.sub_zero, Nat.mod_self]; exact h0
    · intro i hi
      show c.getD ((L - (i + 1)) % L) r ∈ nbrs (c.getD ((L - i) % L) r)
      have e1 : (L - (i + 1)) % L = L - (i + 1) := Nat.mod_eq_of_lt (by omega)
      rw [e1, getD_eq c r (L - (i + 1)) (by omega)]
      by_cases hi0 : i = 0
      · subst hi0
        have e2 : (L - 0) % L = 0 := by rw [Nat.sub_zero, Nat.mod_self]
        rw [e2, getD_eq c r 0 (by omega)]
        have : L - (0 + 1) = c.length - 1 := rfl
        simp only [this]
        exact hlast'
      · have e2 : (L - i) % L = L - i := Nat.mod_eq_of_lt (by omega)
        rw [e2, getD_eq c r (L - i) (by omega)]
        have := hstep' (L - (i + 1)) (by omega)
        have e3 : L - (i + 1) + 1 = L - i := by omega
        simp only [e3] at this
        exact this
    · intro i hi
      show c.getD ((L - (i + 2)) % L) r ≠ c.getD ((L - i) % L) r
      have e1 : (L - (i + 2)) % L = L - (i + 2) := Nat.mod_eq_of_lt (by omega)
      rw [e1, getD_eq c r (L - (i + 2)) (by omega)]
      by_cases hi0 : i = 0
      · subst hi0
        have e2 : (L - 0) % L = 0 := by rw [Nat.sub_zero, Nat.mod_self]
        rw [e2, getD_eq c r 0 (by omega)]
        exact hne _ _ _ _ (by omega)
      · have e2 : (L - i) % L = L - i := Nat.mod_eq_of_lt (by omega)
        rw [e2, getD_eq c r (L - i) (by omega)]
        exact hne _ _ _ _ (by omega)
  -- both appear in the enumerated list
  have hm1 : walkList f1 a ∈ (List.range (R + 1)).flatMap (layer nbrs r) :=
    List.mem_flatMap.2 ⟨a, List.mem_range.2 (by omega), hW1⟩
  have hm2 : walkList f2 (L - a) ∈ (List.range (R + 1)).flatMap (layer nbrs r) :=
    List.mem_flatMap.2 ⟨L - a, List.mem_range.2 (by omega), hW2⟩
  have hnodup : (((List.range (R + 1)).flatMap (layer nbrs r)).map (fun w => enc (w.headD r))).Nodup :=
    (allDistinct_sound _ _ hchk).1
  have heq := nodup_map_inj (fun w => enc (w.headD r)) _ hnodup _ hm1 _ hm2 (by
    obtain ⟨t1, e1⟩ := walkList_head f1 a
    obtain ⟨t2, e2⟩ := walkList_head f2 (L - a)
    simp only [e1, e2, List.headD_cons]
    congr 1
    show c.getD a r = c.getD ((L - (L - a)) % L) r
    have : (L - (L - a)) % L = a := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [this])
  -- but the two walks differ
  by_cases hab : a = L - a
  · have hl1 := walkList_length f1 a
    have key : (walkList f1 a)[a - 1]'(by omega) = (walkList f2 (L - a))[a - 1]'(by
        rw [walkList_length]; omega) := by
      simp only [heq]
    rw [walkList_getElem, walkList_getElem] at key
    have e1 : a - (a - 1) = 1 := by omega
    have e2 : L - a - (a - 1) = 1 := by omega
    simp only [e1, e2, f1, f2] at key
    have e3 : (L - 1) % L = L - 1 := Nat.mod_eq_of_lt (by omega)
    rw [e3, getD_eq c r 1 (by omega), getD_eq c r (L - 1) (by omega)] at key
    exact hne 1 (L - 1) (by omega) (by omega) (by omega) key
  · have := congrArg List.length heq
    rw [walkList_length, walkList_length] at this
    omega

end Walks

/-! ## Part C. 2×2 matrices modulo p -/

def P : Nat := 13

structure Mat where
  (a b c d : Nat)
deriving DecidableEq

def mmul (x y : Mat) : Mat :=
  ⟨(x.a * y.a + x.b * y.c) % P, (x.a * y.b + x.b * y.d) % P,
   (x.c * y.a + x.d * y.c) % P, (x.c * y.b + x.d * y.d) % P⟩

theorem mod_lin (X Y z w : Nat) : ((X % P) * z + (Y % P) * w) % P = (X * z + Y * w) % P := by
  simp [Nat.add_mod, Nat.mul_mod]
theorem mod_lin' (x y C D : Nat) : (x * (C % P) + y * (D % P)) % P = (x * C + y * D) % P := by
  simp [Nat.add_mod, Nat.mul_mod]

theorem mmul_assoc (x y z : Mat) : mmul (mmul x y) z = mmul x (mmul y z) := by
  obtain ⟨a, b, c, d⟩ := x
  obtain ⟨e, f, g, h⟩ := y
  obtain ⟨i, j, k, l⟩ := z
  simp only [mmul, Mat.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [mod_lin, mod_lin'] <;> congr 1 <;> grind

def one : Mat := ⟨1, 0, 0, 1⟩
def Mat.ok (x : Mat) : Prop := x.a < P ∧ x.b < P ∧ x.c < P ∧ x.d < P

theorem one_mmul (x : Mat) (hx : x.ok) : mmul one x = x := by
  obtain ⟨a, b, c, d⟩ := x
  obtain ⟨ha, hb, hc, hd⟩ := hx
  simp only [mmul, one, Mat.mk.injEq, Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add]
  exact ⟨Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd⟩

theorem mmul_one (x : Mat) (hx : x.ok) : mmul x one = x := by
  obtain ⟨a, b, c, d⟩ := x
  obtain ⟨ha, hb, hc, hd⟩ := hx
  simp only [mmul, one, Mat.mk.injEq, Nat.mul_one, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
  exact ⟨Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hd⟩

theorem mmul_ok (x y : Mat) : (mmul x y).ok := by
  have hP : 0 < P := by decide
  exact ⟨Nat.mod_lt _ hP, Nat.mod_lt _ hP, Nat.mod_lt _ hP, Nat.mod_lt _ hP⟩

/-- adjugate; the inverse of a matrix of determinant 1 -/
def minv (x : Mat) : Mat := ⟨x.d, (P - x.b) % P, (P - x.c) % P, x.a⟩

/-! ## Part D. The voltage lift -/

/-- vertex of the lift: base vertex `u` and matrix `m` -/
structure V where
  (u : Nat) (m : Mat)
deriving DecidableEq

/-- number of base vertices -/
def NB : Nat := 2

/-- darts of the base multigraph: `darts u` lists the pairs (head, voltage) of the darts at `u` -/
def darts : Nat → List (Nat × Mat)
  | 0 => [(0, ⟨0, 9, 10, 2⟩), (0, ⟨2, 4, 3, 0⟩), (1, ⟨1, 0, 0, 1⟩), (1, ⟨1, 4, 4, 4⟩), (1, ⟨9, 11, 1, 10⟩), (1, ⟨5, 4, 9, 10⟩)]
  | 1 => [(1, ⟨1, 0, 8, 1⟩), (1, ⟨1, 0, 5, 1⟩), (0, ⟨1, 0, 0, 1⟩), (0, ⟨4, 9, 9, 1⟩), (0, ⟨10, 2, 12, 9⟩), (0, ⟨10, 9, 4, 5⟩)]
  | _ => []

/-- the six neighbours of a vertex -/
def nbrs (v : V) : List V := (darts v.u).map (fun t => ⟨t.1, mmul v.m t.2⟩)
def adjV (x y : V) : Bool := decide (y ∈ nbrs x)

def det1 (x : Mat) : Bool := (x.a * x.d) % P == (x.b * x.c + 1) % P
def valid (v : V) : Bool :=
  decide (v.u < NB) && decide (v.m.a < P) && decide (v.m.b < P) && decide (v.m.c < P) &&
    decide (v.m.d < P) && det1 v.m
def enc (v : V) : Nat := v.u * 28561 + ((v.m.a * 13 + v.m.b) * 13 + v.m.c) * 13 + v.m.d
def decV (n : Nat) : V :=
  ⟨n / 28561, ⟨n / 2197 % 13, n / 169 % 13, n / 13 % 13, n % 13⟩⟩
/-- all vertices: `{0,…,NB-1} × SL(2,p)`, ordered by `enc` -/
@[irreducible] def verts : List V := ((List.range 57122).map decV).filter valid

/-! ### Finite checks (kernel computations) -/

def dartsOK : Bool :=
  (List.range NB).all (fun u => (darts u).length == 6 &&
    (darts u).all (fun t => decide (t.1 < NB) &&
      (darts t.1).any (fun s => s.1 == u && mmul t.2 s.2 == one)))

theorem dartsOK_ok : dartsOK = true := by decide +kernel

def localOK (v : V) : Bool :=
  (nbrs v).all valid && decide ((v :: nbrs v).Nodup) &&
    (mmul (minv v.m) v.m == one) && (mmul v.m (minv v.m) == one)

/-- the `j`-th block of the vertex enumeration (2-dimensional slices of the tuple range) -/
def chunk (j : Nat) : List V :=
  ((List.range 2197).map (fun n => decV (j * 2197 + n))).filter valid

/-- expected block sizes -/
def lens : List Nat := [156, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 156, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169, 169]

def chunkCheck (j : Nat) : Bool := ((chunk j).length == lens.getD j 0) && (chunk j).all localOK

theorem cc_0 : chunkCheck 0 = true := by decide +kernel
theorem cc_1 : chunkCheck 1 = true := by decide +kernel
theorem cc_2 : chunkCheck 2 = true := by decide +kernel
theorem cc_3 : chunkCheck 3 = true := by decide +kernel
theorem cc_4 : chunkCheck 4 = true := by decide +kernel
theorem cc_5 : chunkCheck 5 = true := by decide +kernel
theorem cc_6 : chunkCheck 6 = true := by decide +kernel
theorem cc_7 : chunkCheck 7 = true := by decide +kernel
theorem cc_8 : chunkCheck 8 = true := by decide +kernel
theorem cc_9 : chunkCheck 9 = true := by decide +kernel
theorem cc_10 : chunkCheck 10 = true := by decide +kernel
theorem cc_11 : chunkCheck 11 = true := by decide +kernel
theorem cc_12 : chunkCheck 12 = true := by decide +kernel
theorem cc_13 : chunkCheck 13 = true := by decide +kernel
theorem cc_14 : chunkCheck 14 = true := by decide +kernel
theorem cc_15 : chunkCheck 15 = true := by decide +kernel
theorem cc_16 : chunkCheck 16 = true := by decide +kernel
theorem cc_17 : chunkCheck 17 = true := by decide +kernel
theorem cc_18 : chunkCheck 18 = true := by decide +kernel
theorem cc_19 : chunkCheck 19 = true := by decide +kernel
theorem cc_20 : chunkCheck 20 = true := by decide +kernel
theorem cc_21 : chunkCheck 21 = true := by decide +kernel
theorem cc_22 : chunkCheck 22 = true := by decide +kernel
theorem cc_23 : chunkCheck 23 = true := by decide +kernel
theorem cc_24 : chunkCheck 24 = true := by decide +kernel
theorem cc_25 : chunkCheck 25 = true := by decide +kernel

theorem allChunks : ∀ j, j < 26 → chunkCheck j = true := by
  intro j hj
  match j, hj with
  | 0, _ => exact cc_0
  | 1, _ => exact cc_1
  | 2, _ => exact cc_2
  | 3, _ => exact cc_3
  | 4, _ => exact cc_4
  | 5, _ => exact cc_5
  | 6, _ => exact cc_6
  | 7, _ => exact cc_7
  | 8, _ => exact cc_8
  | 9, _ => exact cc_9
  | 10, _ => exact cc_10
  | 11, _ => exact cc_11
  | 12, _ => exact cc_12
  | 13, _ => exact cc_13
  | 14, _ => exact cc_14
  | 15, _ => exact cc_15
  | 16, _ => exact cc_16
  | 17, _ => exact cc_17
  | 18, _ => exact cc_18
  | 19, _ => exact cc_19
  | 20, _ => exact cc_20
  | 21, _ => exact cc_21
  | 22, _ => exact cc_22
  | 23, _ => exact cc_23
  | 24, _ => exact cc_24
  | 25, _ => exact cc_25
  | _ + 26, h => omega

/-- the local girth check at the roots `(u, 1)` -/
theorem root_0 : allDistinct (headCodes nbrs enc ⟨0, one⟩ 4) 0 = true := by decide +kernel
theorem root_1 : allDistinct (headCodes nbrs enc ⟨1, one⟩ 4) 0 = true := by decide +kernel

/-! ### Consequences of the finite checks -/

theorem decV_enc (v : V) (h : v.m.ok) : decV (enc v) = v := by
  obtain ⟨u, ⟨a, b, c, d⟩⟩ := v
  obtain ⟨ha, hb, hc, hd⟩ := h
  simp only [P] at ha hb hc hd
  simp only [decV, enc, V.mk.injEq, Mat.mk.injEq]
  omega

theorem enc_decV (n : Nat) : enc (decV n) = n := by
  simp only [decV, enc]
  omega

theorem valid_spec (v : V) (h : valid v = true) : v.u < NB ∧ v.m.ok := by
  simp only [valid, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2⟩

theorem mem_verts (v : V) : v ∈ verts ↔ valid v = true := by
  unfold verts
  constructor
  · intro h; exact (List.mem_filter.1 h).2
  · intro h
    obtain ⟨hu, hm⟩ := valid_spec v h
    refine List.mem_filter.2 ⟨List.mem_map.2 ⟨enc v, List.mem_range.2 ?_, decV_enc v hm⟩, h⟩
    obtain ⟨u, ⟨a, b, c, d⟩⟩ := v
    obtain ⟨ha, hb, hc, hd⟩ := hm
    simp only [P] at ha hb hc hd
    simp only [NB] at hu
    simp only [enc]
    omega

theorem verts_nodup : verts.Nodup := by
  unfold verts
  apply List.Pairwise.filter
  apply List.Pairwise.map _ _ List.nodup_range
  intro x y hxy e
  apply hxy
  rw [← enc_decV x, ← enc_decV y, e]

theorem split_range {α : Type} (f : Nat → α) (p : α → Bool) (S : Nat) : ∀ k,
    ((List.range (k * S)).map f).filter p =
      (List.range k).flatMap (fun j => ((List.range S).map (fun n => f (j * S + n))).filter p)
  | 0 => by simp
  | k + 1 => by
    rw [Nat.succ_mul, List.range_add, List.map_append, List.filter_append, split_range f p S k,
      List.range_succ, List.flatMap_append, List.flatMap_singleton, List.map_map]
    rfl

theorem verts_eq : verts = (List.range 26).flatMap chunk := by
  unfold verts chunk
  have e : 57122 = 26 * 2197 := by decide
  rw [e]
  exact split_range decV valid 2197 26

theorem verts_length : verts.length = 4368 := by
  rw [verts_eq, List.length_flatMap]
  rw [List.map_congr_left (g := fun j => lens.getD j 0) (fun j hj => by
    have := allChunks j (List.mem_range.1 hj)
    simp only [chunkCheck, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1)]
  decide

theorem localOK_of_mem (v : V) (h : v ∈ verts) : localOK v = true := by
  rw [verts_eq, List.mem_flatMap] at h
  obtain ⟨j, hj, hv⟩ := h
  have := allChunks j (List.mem_range.1 hj)
  simp only [chunkCheck, Bool.and_eq_true, List.all_eq_true] at this
  exact this.2 v hv

theorem localOK_spec (v : V) (h : v ∈ verts) :
    (∀ y ∈ nbrs v, y ∈ verts) ∧ (v :: nbrs v).Nodup ∧
      mmul (minv v.m) v.m = one ∧ mmul v.m (minv v.m) = one := by
  have h' := localOK_of_mem v h
  simp only [localOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
  exact ⟨fun y hy => (mem_verts y).2 (h'.1.1.1 y hy), h'.1.1.2, h'.1.2, h'.2⟩

theorem mem_nbrs {x y : V} : y ∈ nbrs x ↔ ∃ t ∈ darts x.u, y = ⟨t.1, mmul x.m t.2⟩ := by
  simp only [nbrs, List.mem_map]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, rfl⟩

theorem darts_spec (u : Nat) (hu : u < NB) :
    (darts u).length = 6 ∧ ∀ t ∈ darts u, t.1 < NB ∧ ∃ s ∈ darts t.1, s.1 = u ∧ mmul t.2 s.2 = one := by
  have h := dartsOK_ok
  simp only [dartsOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.any_eq_true] at h
  obtain ⟨h1, h2⟩ := h u hu
  exact ⟨h1, fun t ht => ⟨(h2 t ht).1, (h2 t ht).2⟩⟩

/-- adjacency is symmetric on all vertices with entries `< p` (algebraic argument) -/
theorem nbrs_symm (x y : V) (hu : x.u < NB) (hm : x.m.ok) (hy : y ∈ nbrs x) : x ∈ nbrs y := by
  obtain ⟨t, ht, rfl⟩ := mem_nbrs.1 hy
  obtain ⟨_, s, hs, hsu, hts⟩ := (darts_spec x.u hu).2 t ht
  refine mem_nbrs.2 ⟨s, hs, ?_⟩
  show x = ⟨s.1, mmul (mmul x.m t.2) s.2⟩
  rw [mmul_assoc, hts, mmul_one x.m hm, hsu]

theorem nbrs_u (x y : V) (hu : x.u < NB) (hy : y ∈ nbrs x) : y.u < NB := by
  obtain ⟨t, ht, rfl⟩ := mem_nbrs.1 hy
  exact ((darts_spec x.u hu).2 t ht).1

/-- left multiplication by `B` is a graph homomorphism -/
def lmul (B : Mat) (x : V) : V := ⟨x.u, mmul B x.m⟩

theorem lmul_nbrs (B : Mat) (x y : V) (hy : y ∈ nbrs x) : lmul B y ∈ nbrs (lmul B x) := by
  obtain ⟨t, ht, rfl⟩ := mem_nbrs.1 hy
  refine mem_nbrs.2 ⟨t, ht, ?_⟩
  simp only [lmul, mmul_assoc]

theorem lmul_inj (M : Mat) (hM : mmul M (minv M) = one) (x y : V) (hx : x.m.ok) (hy : y.m.ok)
    (e : lmul (minv M) x = lmul (minv M) y) : x = y := by
  simp only [lmul, V.mk.injEq] at e
  obtain ⟨e1, e2⟩ := e
  have : mmul M (mmul (minv M) x.m) = mmul M (mmul (minv M) y.m) := by rw [e2]
  rw [← mmul_assoc, ← mmul_assoc, hM, one_mmul _ hx, one_mmul _ hy] at this
  obtain ⟨u, m⟩ := x
  obtain ⟨u', m'⟩ := y
  simp only at e1 this
  rw [e1, this]

theorem isCycle_map {α β : Type} (adj : α → α → Bool) (adj' : β → β → Bool) (f : α → β)
    (c : List α) (hc : IsCycle adj c)
    (hinj : ∀ x ∈ c, ∀ y ∈ c, f x = f y → x = y)
    (hhom : ∀ x ∈ c, ∀ y ∈ c, adj x y = true → adj' (f x) (f y) = true) :
    IsCycle adj' (c.map f) := by
  obtain ⟨h3, hnd, hcyc⟩ := hc
  refine ⟨by simpa using h3, ?_, ?_⟩
  · have hnd' : List.Pairwise (fun x y => x ≠ y) c := hnd
    rw [List.pairwise_iff_getElem] at hnd'
    show List.Pairwise (fun x y => x ≠ y) (c.map f)
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij e
    simp only [List.getElem_map] at e
    have hi' : i < c.length := by simpa using hi
    have hj' : j < c.length := by simpa using hj
    exact hnd' i j hi' hj' hij (hinj _ (List.getElem_mem _) _ (List.getElem_mem _) e)
  · intro i hi
    simp only [List.length_map, List.getElem_map]
    have hi' : i < c.length := by simpa using hi
    exact hhom _ (List.getElem_mem _) _ (List.getElem_mem _) (hcyc i hi')

/-! ## Part E. The graph on `Fin 4368` -/

def vx (i : Fin 4368) : V := verts[i.1]'(by rw [verts_length]; exact i.2)

def adjF (i j : Fin 4368) : Bool := adjV (vx i) (vx j)

theorem vx_mem (i : Fin 4368) : vx i ∈ verts := List.getElem_mem _

theorem vx_inj (i j : Fin 4368) (e : vx i = vx j) : i = j := by
  apply Fin.ext
  exact (List.Nodup.getElem_inj verts_nodup).1 e

theorem map_vx : (List.finRange 4368).map vx = verts := by
  apply List.ext_getElem
  · simp [verts_length]
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_finRange, vx]
    rfl

theorem simple : IsSimpleGraph adjF := by
  constructor
  · intro i j
    have hi := (mem_verts _).1 (vx_mem i)
    have hj := (mem_verts _).1 (vx_mem j)
    have si := valid_spec _ hi
    have sj := valid_spec _ hj
    simp only [adjF, adjV]
    apply Bool.eq_iff_iff.2
    simp only [decide_eq_true_eq]
    exact ⟨nbrs_symm _ _ si.1 si.2, nbrs_symm _ _ sj.1 sj.2⟩
  · intro i
    have := (localOK_spec (vx i) (vx_mem i)).2.1
    simp only [adjF, adjV, decide_eq_false_iff_not]
    exact (List.nodup_cons.1 this).1

theorem regular : IsRegular adjF 6 := by
  intro i
  let v := vx i
  have hv := localOK_spec v (vx_mem i)
  have hval := valid_spec v ((mem_verts _).1 (vx_mem i))
  unfold degree
  have e1 : ((List.finRange 4368).filter (fun w => adjF i w)).length =
      (verts.filter (fun y => adjV v y)).length := by
    have hf : (fun w => adjF i w) = ((fun y => adjV v y) ∘ vx) := rfl
    rw [← map_vx, List.filter_map, List.length_map, hf]
  rw [e1]
  have hperm : (verts.filter (fun y => adjV v y)).Perm (nbrs v) := by
    apply (List.perm_ext_iff_of_nodup (List.Pairwise.filter _ verts_nodup) (List.nodup_cons.1 hv.2.1).2).2
    intro y
    simp only [List.mem_filter, adjV, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨hv.1 y h, h⟩⟩
  rw [hperm.length_eq]
  simp only [nbrs, List.length_map]
  exact (darts_spec v.u hval.1).1

theorem no_short_cycles (c : List (Fin 4368)) (hc : IsCycle adjF c) : 9 ≤ c.length := by
  apply Nat.le_of_not_lt
  intro hlt
  have h3 := hc.1
  -- transport to the lift
  have hc1 : IsCycle adjV (c.map vx) :=
    isCycle_map adjF adjV vx c hc (fun x _ y _ e => vx_inj x y e) (fun x _ y _ h => h)
  have hall : ∀ x ∈ c.map vx, x ∈ verts := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hx
    exact vx_mem i
  have hlen1 : 0 < (c.map vx).length := by simp; omega
  have hlen8 : (c.map vx).length < 9 := by simpa using hlt
  generalize c.map vx = cv at hc1 hall hlen1 hlen8
  obtain ⟨v0, hv0e⟩ : ∃ v0, cv[0]'hlen1 = v0 := ⟨_, rfl⟩
  have hv0 : v0 ∈ verts := by rw [← hv0e]; exact hall _ (List.getElem_mem _)
  have hs0 := localOK_spec v0 hv0
  have hval0 := valid_spec v0 ((mem_verts _).1 hv0)
  have hc2 : IsCycle adjV (cv.map (lmul (minv v0.m))) := by
    apply isCycle_map adjV adjV _ _ hc1
    · intro x hx y hy e
      exact lmul_inj v0.m hs0.2.2.2 x y (valid_spec _ ((mem_verts _).1 (hall x hx))).2
        (valid_spec _ ((mem_verts _).1 (hall y hy))).2 e
    · intro x _ y _ h
      simp only [adjV, decide_eq_true_eq] at h ⊢
      exact lmul_nbrs _ x y h
  have hr : (cv.map (lmul (minv v0.m))).getD 0 ⟨v0.u, one⟩ = ⟨v0.u, one⟩ := by
    rw [getD_eq _ _ 0 (by simpa using hlen1), List.getElem_map, hv0e]
    simp only [lmul]
    rw [hs0.2.2.1]
  have hgood : ∀ x ∈ cv.map (lmul (minv v0.m)), x.u < NB ∧ x.m.ok := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact ⟨(valid_spec _ ((mem_verts _).1 (hall y hy))).1, mmul_ok _ _⟩
  have hsym : ∀ x ∈ cv.map (lmul (minv v0.m)), ∀ y ∈ cv.map (lmul (minv v0.m)),
      adjV x y = true → adjV y x = true := by
    intro x hx y _ h
    simp only [adjV, decide_eq_true_eq] at h ⊢
    exact nbrs_symm x y (hgood x hx).1 (hgood x hx).2 h
  have hroot : allDistinct (headCodes nbrs enc ⟨v0.u, one⟩ 4) 0 = true := by
    have hu := hval0.1
    simp only [NB] at hu
    rcases v0 with ⟨u, m⟩
    simp only at hu ⊢
    match u, hu with
    | 0, _ => exact root_0
    | 1, _ => exact root_1
    | _ + 2, h => omega
  exact no_short_cycle nbrs enc adjV (fun x y h => by simpa [adjV] using h) _ 4 hroot _ hc2 hsym hr
    (by simp; omega)

/-- an explicit cycle of length 9 in the lift -/
def witnessV : List V := [⟨0, ⟨1, 0, 0, 1⟩⟩, ⟨0, ⟨0, 9, 10, 2⟩⟩, ⟨0, ⟨12, 5, 7, 3⟩⟩, ⟨0, ⟨11, 1, 4, 4⟩⟩, ⟨1, ⟨9, 1, 1, 6⟩⟩, ⟨1, ⟨1, 1, 5, 6⟩⟩, ⟨0, ⟨1, 1, 9, 10⟩⟩, ⟨0, ⟨5, 4, 9, 10⟩⟩, ⟨1, ⟨5, 4, 9, 10⟩⟩]

instance decIsCycle {α : Type} [DecidableEq α] (adj : α → α → Bool) (c : List α) :
    Decidable (IsCycle adj c) := by
  unfold IsCycle; infer_instance

theorem witnessV_isCycle : IsCycle adjV witnessV := by decide +kernel

theorem witnessV_valid : witnessV.all valid = true := by decide +kernel

theorem lift_list : ∀ cv : List V, (∀ v ∈ cv, v ∈ verts) → ∃ c : List (Fin 4368), c.map vx = cv
  | [], _ => ⟨[], rfl⟩
  | v :: cv, h => by
    obtain ⟨c, hc⟩ := lift_list cv (fun w hw => h w (List.mem_cons_of_mem _ hw))
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 (h v (List.mem_cons_self))
    refine ⟨⟨i, by rw [← verts_length]; exact hi⟩ :: c, ?_⟩
    simp only [List.map_cons, hc]
    rw [← e]
    rfl

theorem exists_cycle : ∃ c, IsCycle adjF c ∧ c.length = 9 := by
  obtain ⟨c, hc⟩ := lift_list witnessV (fun v hv => (mem_verts v).2
    ((List.all_eq_true.1 witnessV_valid) v hv))
  have hcyc := witnessV_isCycle
  rw [← hc] at hcyc
  obtain ⟨h3, hnd, hstep⟩ := hcyc
  refine ⟨c, ⟨by simpa using h3, List.Pairwise.of_map vx (fun a b h e => h (congrArg vx e)) hnd, ?_⟩, ?_⟩
  · intro i hi
    have := hstep i (by simpa using hi)
    simp only [List.getElem_map, List.length_map] at this
    exact this
  · have := congrArg List.length hc
    simp only [List.length_map] at this
    rw [this]; rfl

/-! ## Main theorem -/

theorem main : ∃ adj : Fin 4368 → Fin 4368 → Bool,
    IsSimpleGraph adj ∧ IsRegular adj 6 ∧ HasGirth adj 9 :=
  ⟨adjF, simple, regular, ⟨exists_cycle, no_short_cycles⟩⟩

end Cage

#print axioms Cage.main
