import Mathlib

/-!
# A new lower bound for the cap set capacity  (B05, October 14 2026)

Main results (at the end of the file):
* `main_cap_648 : ∃ A : Finset (Fin 648 → ZMod 3), IsCap A ∧ (2220334 : ℝ) ^ 648 < A.card * (1000000 : ℝ) ^ 648`,
  i.e. a cap set in `F_3^648` of size `> (2220334/1000000)^648`;
* `main_capacity k` : caps in `F_3^(648 k)` of size `> (2220334/1000000)^(648 k)` for all `k ≥ 1`
  (so the cap-set capacity is at least `2220334/1000000`);
* `admissible_new` : the new symmetric admissible set in `{0,1,2}^27` (rows `rowsR`).
`IsCap A := ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = 0 → x = y ∧ y = z`.
Proof chain: type-level criterion (`admissible_of_rowsOK`), bitset checker soundness (`rowsOK_of_check`),
Edel's extended product (`ext_isCap`, `card_ext`), Edel's recursion (`ext_extendable`), the
Calderbank–Fishburn collection (`CF_extendable`), the count (`card_ext_rows`, `Mfinal_bound`).
`native_decide` is used for `rows_nodup`, `rows_chkP`, `rows_chkT`, `cf_checks`, `CF_card`.
-/

/-!
# Symmetric admissible sets: the type-level reduction

Vectors of `{0,1,2}^(3g)` are written in blocks: `Fin g → Fin 3 → Fin 3`.
A *row* `t : Fin g → Fin 7` stands for the product of the cyclic-rotation orbits of the blocks
`tri (t i)`; a set of rows `R` stands for the union `expandAll R` of these products.
We prove: if the weight profiles of distinct rows are incomparable and every three distinct rows have
a block whose type triple is "always good", then `expandAll R` is an admissible set in the sense of
Edel / Tyrrell (Discrete Analysis 2023:20, Def. 2.5), and compute its cardinality.
-/

namespace CapB05

/-- The seven block types 000, 001, 002, 012, 021, 111, 222 (FunSearch's `TRIPLES`). -/
def tri : Fin 7 → Fin 3 → Fin 3
  | 0 => ![0, 0, 0]
  | 1 => ![0, 0, 1]
  | 2 => ![0, 0, 2]
  | 3 => ![0, 1, 2]
  | 4 => ![0, 2, 1]
  | 5 => ![1, 1, 1]
  | 6 => ![2, 2, 2]

/-- cyclic rotation of a block -/
def rot (r : Fin 3) (u : Fin 3 → Fin 3) : Fin 3 → Fin 3 := fun k => u (k + r)

/-- the orbit of the block of type `t` under cyclic rotations -/
def orb (t : Fin 7) : Finset (Fin 3 → Fin 3) := Finset.univ.image (fun r : Fin 3 => rot r (tri t))

/-- `(a,b,c)` is good: as a multiset it is `{0,1,2}`, `{0,0,1}` or `{0,0,2}`. -/
def Good (a b c : Fin 3) : Prop :=
  (a = 0 ∧ b = 0 ∧ c ≠ 0) ∨ (a = 0 ∧ b ≠ 0 ∧ c = 0) ∨ (a ≠ 0 ∧ b = 0 ∧ c = 0) ∨
  (a ≠ b ∧ b ≠ c ∧ a ≠ c)

instance (a b c : Fin 3) : Decidable (Good a b c) := by unfold Good; infer_instance

/-- block vectors: `{0,1,2}^(3g)` written as `g` blocks of length 3 -/
abbrev BVec (g : ℕ) := Fin g → Fin 3 → Fin 3

/-- Admissible set (Edel 2004; Tyrrell 2023, Def. 2.5), for vectors written in blocks. -/
def IsAdmissible {g : ℕ} (S : Finset (BVec g)) : Prop :=
  (∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      (∃ i k, v i k = 0 ∧ w i k ≠ 0) ∧ (∃ i k, v i k ≠ 0 ∧ w i k = 0)) ∧
  (∀ u ∈ S, ∀ v ∈ S, ∀ w ∈ S, u ≠ v → u ≠ w → v ≠ w → ∃ i k, Good (u i k) (v i k) (w i k))

/-- number of nonzero entries of a block type -/
def wt (t : Fin 7) : ℕ := (Finset.univ.filter (fun k => tri t k ≠ 0)).card

/-- a type triple is *always good*: every choice of rotations has a good coordinate -/
def Good3 (a b c : Fin 7) : Prop :=
  ∀ u ∈ orb a, ∀ v ∈ orb b, ∀ w ∈ orb c, ∃ k, Good (u k) (v k) (w k)

instance (a b c : Fin 7) : Decidable (Good3 a b c) := by unfold Good3; infer_instance

/-- expansion of one row -/
def expand {g : ℕ} (t : Fin g → Fin 7) : Finset (BVec g) := Fintype.piFinset (fun i => orb (t i))

/-- expansion of a set of rows -/
def expandAll {g : ℕ} (R : Finset (Fin g → Fin 7)) : Finset (BVec g) := R.biUnion expand

/-- the type-level conditions -/
def RowsOK {g : ℕ} (R : Finset (Fin g → Fin 7)) : Prop :=
  (∀ t ∈ R, ∀ t' ∈ R, t ≠ t' → ∃ i, wt (t' i) < wt (t i)) ∧
  (∀ t ∈ R, ∀ t' ∈ R, ∀ t'' ∈ R, t ≠ t' → t ≠ t'' → t' ≠ t'' → ∃ i, Good3 (t i) (t' i) (t'' i))

/-! ### finite facts about single blocks (all by `decide`) -/

lemma good_perm12 (a b c : Fin 3) : Good a b c → Good b a c := by revert a b c; decide
lemma good_perm23 (a b c : Fin 3) : Good a b c → Good a c b := by revert a b c; decide

/-- two different rotations of one type: some coordinate is zero in the first and not in the second -/
lemma orb_pair (t : Fin 7) : ∀ u ∈ orb t, ∀ v ∈ orb t, u ≠ v → ∃ k, u k = 0 ∧ v k ≠ 0 := by
  revert t; decide

/-- three rotations of one type, not all equal, have a good coordinate -/
lemma orb_triple (t : Fin 7) : ∀ u ∈ orb t, ∀ v ∈ orb t, ∀ w ∈ orb t, (u ≠ v ∨ v ≠ w) →
    ∃ k, Good (u k) (v k) (w k) := by
  revert t; decide

/-- a block of larger weight has a nonzero coordinate where the lighter block is zero -/
lemma orb_heavier (a b : Fin 7) : wt b < wt a → ∀ u ∈ orb a, ∀ v ∈ orb b, ∃ k, u k ≠ 0 ∧ v k = 0 := by
  revert a b; decide

/-- two rotations of a type `a` and one rotation of a heavier type `b` have a good coordinate -/
lemma orb_two_one (a b : Fin 7) : wt a < wt b → ∀ u ∈ orb a, ∀ u' ∈ orb a, ∀ v ∈ orb b,
    ∃ k, Good (u k) (u' k) (v k) := by
  revert a b; decide

/-- the weight of a block is determined by its orbit -/
lemma orb_wt (a b : Fin 7) : ∀ u ∈ orb a, u ∈ orb b → wt a = wt b := by
  revert a b; decide

lemma orb_card (t : Fin 7) : (orb t).card = if wt t = 0 ∨ wt t = 3 then 1 else 3 := by
  revert t; decide

/-! ### the reduction -/

lemma mem_expand {g : ℕ} {t : Fin g → Fin 7} {v : BVec g} : v ∈ expand t ↔ ∀ i, v i ∈ orb (t i) := by
  simp [expand, Fintype.mem_piFinset]

theorem admissible_of_rowsOK {g : ℕ} (R : Finset (Fin g → Fin 7)) (h : RowsOK R) :
    IsAdmissible (expandAll R) := by
  obtain ⟨hP, hT⟩ := h
  constructor
  · intro v hv w hw hvw
    simp only [expandAll, Finset.mem_biUnion] at hv hw
    obtain ⟨t, ht, hvt⟩ := hv
    obtain ⟨t', ht', hwt⟩ := hw
    rw [mem_expand] at hvt hwt
    by_cases htt : t = t'
    · subst htt
      have : ∃ i, v i ≠ w i := by
        by_contra hc; push Not at hc; exact hvw (funext hc)
      obtain ⟨i, hi⟩ := this
      obtain ⟨k, hk⟩ := orb_pair (t i) (v i) (hvt i) (w i) (hwt i) hi
      obtain ⟨k', hk'⟩ := orb_pair (t i) (w i) (hwt i) (v i) (hvt i) (Ne.symm hi)
      exact ⟨⟨i, k, hk⟩, ⟨i, k', hk'.2, hk'.1⟩⟩
    · obtain ⟨i, hi⟩ := hP t' ht' t ht (Ne.symm htt)
      obtain ⟨j, hj⟩ := hP t ht t' ht' htt
      obtain ⟨k, hk⟩ := orb_heavier (t' i) (t i) hi (w i) (hwt i) (v i) (hvt i)
      obtain ⟨k', hk'⟩ := orb_heavier (t j) (t' j) hj (v j) (hvt j) (w j) (hwt j)
      exact ⟨⟨i, k, hk.2, hk.1⟩, ⟨j, k', hk'⟩⟩
  · intro u hu v hv w hw huv huw hvw
    simp only [expandAll, Finset.mem_biUnion] at hu hv hw
    obtain ⟨t, ht, hut⟩ := hu
    obtain ⟨t', ht', hvt⟩ := hv
    obtain ⟨t'', ht'', hwt⟩ := hw
    rw [mem_expand] at hut hvt hwt
    by_cases h1 : t = t'
    · subst h1
      by_cases h2 : t = t''
      · subst h2
        have : ∃ i, u i ≠ v i := by
          by_contra hc; push Not at hc; exact huv (funext hc)
        obtain ⟨i, hi⟩ := this
        obtain ⟨k, hk⟩ := orb_triple (t i) (u i) (hut i) (v i) (hvt i) (w i) (hwt i) (Or.inl hi)
        exact ⟨i, k, hk⟩
      · -- u, v from t; w from t''
        obtain ⟨i, hi⟩ := hP t'' ht'' t ht (Ne.symm h2)
        obtain ⟨k, hk⟩ := orb_two_one (t i) (t'' i) hi (u i) (hut i) (v i) (hvt i) (w i) (hwt i)
        exact ⟨i, k, hk⟩
    · by_cases h2 : t = t''
      · subst h2
        -- u, w from t; v from t'
        obtain ⟨i, hi⟩ := hP t' ht' t ht (Ne.symm h1)
        obtain ⟨k, hk⟩ := orb_two_one (t i) (t' i) hi (u i) (hut i) (w i) (hwt i) (v i) (hvt i)
        exact ⟨i, k, good_perm23 _ _ _ hk⟩
      · by_cases h3 : t' = t''
        · subst h3
          -- v, w from t'; u from t
          obtain ⟨i, hi⟩ := hP t ht t' ht' h1
          obtain ⟨k, hk⟩ := orb_two_one (t' i) (t i) hi (v i) (hvt i) (w i) (hwt i) (u i) (hut i)
          -- hk : Good (v) (w) (u)  → Good u v w
          exact ⟨i, k, good_perm12 _ _ _ (good_perm23 _ _ _ hk)⟩
        · obtain ⟨i, hi⟩ := hT t ht t' ht' t'' ht'' h1 h2 h3
          obtain ⟨k, hk⟩ := hi (u i) (hut i) (v i) (hvt i) (w i) (hwt i)
          exact ⟨i, k, hk⟩

theorem card_expandAll {g : ℕ} (R : Finset (Fin g → Fin 7)) (h : RowsOK R) :
    (expandAll R).card = ∑ t ∈ R, ∏ i, (orb (t i)).card := by
  unfold expandAll
  rw [Finset.card_biUnion]
  · simp [expand, Fintype.card_piFinset]
  · intro t ht t' ht' htt
    rw [Function.onFun, Finset.disjoint_left]
    intro v hv hv'
    rw [mem_expand] at hv hv'
    obtain ⟨i, hi⟩ := h.1 t ht t' ht' htt
    have := orb_wt (t i) (t' i) (v i) (hv i) (hv' i)
    omega


/-! ### executable checker (bitset based) and its soundness -/

/-- bitmask of always-good type triples (bit `49a+7b+c`) -/
def G3MASK : ℕ := 34375473724993970352553239060030903765326522595768790177655346323678939469540016871467797844225621758

def good3b (a b c : Fin 7) : Bool := Nat.testBit G3MASK (49 * a.val + 7 * b.val + c.val)

lemma good3b_iff (a b c : Fin 7) : good3b a b c = true ↔ Good3 a b c := by
  revert a b c; decide

def decodeRow (g : ℕ) (c : ℕ) : Fin g → Fin 7 := fun i => ⟨(c / 7 ^ (i : ℕ)) % 7, Nat.mod_lt _ (by norm_num)⟩

/-- `mask P L` has bit `c` set iff `P (L[c])` -/
def mask {α : Type*} (P : α → Bool) : List α → ℕ
  | [] => 0
  | z :: zs => Nat.bit (P z) (mask P zs)

lemma testBit_mask {α : Type*} (P : α → Bool) (L : List α) (c : ℕ) :
    Nat.testBit (mask P L) c = true ↔ ∃ h : c < L.length, P (L[c]'h) = true := by
  induction L generalizing c with
  | nil => simp [mask]
  | cons z zs ih =>
    cases c with
    | zero => simp [mask]
    | succ c => simp [mask, Nat.testBit_bit_succ, ih]

/-- conjunction of masks over a list of groups -/
def andMasks {g : ℕ} (M : Fin g → ℕ) (acc : ℕ) : List (Fin g) → ℕ
  | [] => acc
  | i :: is => andMasks M (acc &&& M i) is

lemma testBit_andMasks {g : ℕ} (M : Fin g → ℕ) (acc : ℕ) (l : List (Fin g)) (c : ℕ) :
    Nat.testBit (andMasks M acc l) c = true ↔
      (Nat.testBit acc c = true ∧ ∀ i ∈ l, Nat.testBit (M i) c = true) := by
  induction l generalizing acc with
  | nil => simp [andMasks]
  | cons i is ih =>
    simp only [andMasks, ih, Nat.testBit_land, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    tauto

def badMask {g : ℕ} (L : List (Fin g → Fin 7)) (i : Fin g) (t1 t2 : Fin 7) : ℕ :=
  mask (fun z : Fin g → Fin 7 => !good3b t1 t2 (z i)) L

/-- table of all bad masks, index `49 i + 7 t1 + t2` -/
def buildTab {g : ℕ} (L : List (Fin g → Fin 7)) : Array ℕ :=
  (List.range (g * 49)).toArray.map
    (fun k => if h : k / 49 < g then badMask L ⟨k / 49, h⟩ ⟨(k / 7) % 7, Nat.mod_lt _ (by norm_num)⟩
      ⟨k % 7, Nat.mod_lt _ (by norm_num)⟩ else 0)

def BMof {g : ℕ} (tab : Array ℕ) (i : Fin g) (t1 t2 : Fin 7) : ℕ := tab.getD (49 * i.val + 7 * t1.val + t2.val) 0

lemma BMof_buildTab {g : ℕ} (L : List (Fin g → Fin 7)) (i : Fin g) (t1 t2 : Fin 7) :
    BMof (buildTab L) i t1 t2 = badMask L i t1 t2 := by
  have hk : 49 * i.val + 7 * t1.val + t2.val < g * 49 := by
    have := i.isLt; have := t1.isLt; have := t2.isLt; omega
  have e1 : (49 * i.val + 7 * t1.val + t2.val) / 49 = i.val := by omega
  have e2 : (49 * i.val + 7 * t1.val + t2.val) / 7 % 7 = t1.val := by omega
  have e3 : (49 * i.val + 7 * t1.val + t2.val) % 7 = t2.val := by omega
  unfold BMof buildTab
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  simp only [List.getElem?_toArray, List.getElem?_range hk, Option.map_some, Option.getD_some]
  rw [dite_cond_eq_true (eq_true (by rw [e1]; exact i.isLt))]
  congr 1
  · exact Fin.ext e1
  · exact Fin.ext e2
  · exact Fin.ext e3

/-- for the rows `x,y` at positions `a,b`: bitmask of all rows that are bad in every group,
with the bits `a` and `b` removed -/
def pairMask {g : ℕ} (full : ℕ) (tab : Array ℕ) (x y : Fin g → Fin 7) (a b : ℕ) : ℕ :=
  let m := andMasks (fun i => BMof tab i (x i) (y i)) full (List.finRange g)
  m ^^^ (m &&& (2 ^ a ||| 2 ^ b))

def chkTwith {g : ℕ} (L : List (Fin g → Fin 7)) (full : ℕ) (tab : Array ℕ) : Bool :=
  let Z := L.zipIdx
  Z.all (fun p => Z.all (fun q => p.2 == q.2 || pairMask full tab p.1 q.1 p.2 q.2 == 0))

/-- the triple check -/
def chkT {g : ℕ} (L : List (Fin g → Fin 7)) : Bool := chkTwith L (mask (fun _ => true) L) (buildTab L)

lemma chkT_sound {g : ℕ} (L : List (Fin g → Fin 7)) (h : chkT L = true) :
    ∀ t ∈ L.toFinset, ∀ t' ∈ L.toFinset, ∀ t'' ∈ L.toFinset, t ≠ t' → t ≠ t'' → t' ≠ t'' →
      ∃ i, Good3 (t i) (t' i) (t'' i) := by
  intro x hx y hy z hz hxy hxz hyz
  simp only [List.mem_toFinset] at hx hy hz
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hy
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hz
  have hab : a ≠ b := fun e => hxy (by subst e; rfl)
  have hac : a ≠ c := fun e => hxz (by subst e; rfl)
  have hbc : b ≠ c := fun e => hyz (by subst e; rfl)
  unfold chkT chkTwith at h
  simp only [List.all_eq_true] at h
  have hpa : (L[a], a) ∈ L.zipIdx := List.mem_zipIdx_iff_getElem?.mpr (by simp [ha])
  have hpb : (L[b], b) ∈ L.zipIdx := List.mem_zipIdx_iff_getElem?.mpr (by simp [hb])
  have h2 := h _ hpa _ hpb
  simp only [Bool.or_eq_true, beq_iff_eq, hab, false_or] at h2
  have hm : Nat.testBit (andMasks (fun i => BMof (buildTab L) i (L[a] i) (L[b] i))
      (mask (fun _ => true) L) (List.finRange g)) c = true := by
    rw [testBit_andMasks]
    refine ⟨(testBit_mask _ _ _).mpr ⟨hc, rfl⟩, ?_⟩
    intro i _
    rw [BMof_buildTab]
    unfold badMask
    rw [testBit_mask]
    refine ⟨hc, ?_⟩
    have hg := hcon i
    rw [← good3b_iff] at hg
    simpa using hg
  have key : Nat.testBit (pairMask (mask (fun _ => true) L) (buildTab L) L[a] L[b] a b) c = true := by
    unfold pairMask
    simp only [Nat.testBit_xor, Nat.testBit_land, Nat.testBit_lor, Nat.testBit_two_pow, hm]
    simp [hac, hbc]
  rw [h2] at key
  simp at key

def wtb (t : Fin 7) : ℕ := [0, 1, 1, 2, 2, 3, 3].getD t.val 0

lemma wtb_eq (t : Fin 7) : wtb t = wt t := by revert t; decide

def pOK {g : ℕ} (x y : Fin g → Fin 7) : Bool := (List.finRange g).any (fun i => decide (wtb (y i) < wtb (x i)))

def chkP {g : ℕ} (L : List (Fin g → Fin 7)) : Bool :=
  L.all (fun x => L.all (fun y => decide (x = y) || pOK x y))

lemma chkP_sound {g : ℕ} (L : List (Fin g → Fin 7)) (h : chkP L = true) :
    ∀ t ∈ L.toFinset, ∀ t' ∈ L.toFinset, t ≠ t' → ∃ i, wt (t' i) < wt (t i) := by
  intro t ht t' ht' hne
  simp only [List.mem_toFinset] at ht ht'
  simp only [chkP, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h t ht t' ht' with h1 | h1
  · exact absurd h1 hne
  · simp only [pOK, List.any_eq_true, List.mem_finRange, true_and, decide_eq_true_eq] at h1
    obtain ⟨i, hi⟩ := h1
    exact ⟨i, by rw [← wtb_eq, ← wtb_eq]; exact hi⟩

theorem rowsOK_of_check {g : ℕ} (L : List (Fin g → Fin 7)) (hP : chkP L = true) (hT : chkT L = true) :
    RowsOK L.toFinset := ⟨chkP_sound L hP, chkT_sound L hT⟩
section general
variable {V : Type*} [AddCommGroup V] [DecidableEq V]

/-- cap set: no solution of `x + y + z = 0` except `x = y = z` -/
def IsCap (A : Finset V) : Prop := ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y + z = 0 → x = y ∧ y = z

/-- extendable collection (Edel 2004; Tyrrell Def. 2.4) -/
structure Extendable (A : Fin 3 → Finset V) : Prop where
  cap : ∀ j, IsCap (A j)
  c1 : ∀ x ∈ A 0, ∀ y ∈ A 0, ∀ z, (z ∈ A 1 ∨ z ∈ A 2) → x + y + z ≠ 0
  c2 : ∀ x ∈ A 0, ∀ y ∈ A 1, ∀ z ∈ A 2, x + y + z ≠ 0

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- admissible set of label vectors (Tyrrell Def. 2.5) -/
def Admissible (S : Finset (ι → Fin 3)) : Prop :=
  (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → ∃ c, s c = 0 ∧ s' c ≠ 0) ∧
  (∀ s ∈ S, ∀ s' ∈ S, ∀ s'' ∈ S, s ≠ s' → s ≠ s'' → s' ≠ s'' → ∃ c, Good (s c) (s' c) (s'' c))

/-- the block `s(A) = ∏_c A_{s c}` -/
def blk (A : Fin 3 → Finset V) (s : ι → Fin 3) : Finset (ι → V) := Fintype.piFinset (fun c => A (s c))

/-- extended product `S(A0,A1,A2) = ⋃_{s∈S} s(A)` -/
def ext (S : Finset (ι → Fin 3)) (A : Fin 3 → Finset V) : Finset (ι → V) := S.biUnion (blk A)

lemma mem_blk {A : Fin 3 → Finset V} {s : ι → Fin 3} {x : ι → V} : x ∈ blk A s ↔ ∀ c, x c ∈ A (s c) := by
  simp [blk, Fintype.mem_piFinset]

/-- the two "pattern" facts used repeatedly: a coordinate with labels (0,0,≠0) or a permutation of
(0,1,2) is impossible for a solution of `x+y+z=0` -/
lemma no_sol_00n {A : Fin 3 → Finset V} (hA : Extendable A) {a b c : Fin 3} (x y z : V)
    (hx : x ∈ A a) (hy : y ∈ A b) (hz : z ∈ A c) (hg : Good a b c) : x + y + z ≠ 0 := by
  have h1 : ∀ (p q r : V) (cr : Fin 3), p ∈ A 0 → q ∈ A 0 → r ∈ A cr → cr ≠ 0 → p + q + r ≠ 0 := by
    intro p q r cr hp hq hr hcr
    apply hA.c1 p hp q hq r
    fin_cases cr
    · exact absurd rfl hcr
    · exact Or.inl hr
    · exact Or.inr hr
  have h2 : ∀ (p q r : V), p ∈ A 0 → q ∈ A 1 → r ∈ A 2 → p + q + r ≠ 0 :=
    fun p q r hp hq hr => hA.c2 p hp q hq r hr
  rcases hg with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨hab, hbc, hac⟩
  · subst ha; subst hb; exact h1 x y z c hx hy hz hc
  · subst ha; subst hc
    have := h1 x z y b hx hz hy hb
    intro h; apply this; rw [← h]; abel
  · subst hb; subst hc
    have := h1 y z x a hy hz hx ha
    intro h; apply this; rw [← h]; abel
  · -- {a,b,c} = {0,1,2}
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp at hab hbc hac
    · exact h2 x y z hx hy hz
    · intro h; exact h2 x z y hx hz hy (by rw [← h]; abel)
    · intro h; exact h2 y x z hy hx hz (by rw [← h]; abel)
    · intro h; exact h2 z x y hz hx hy (by rw [← h]; abel)
    · intro h; exact h2 y z x hy hz hx (by rw [← h]; abel)
    · intro h; exact h2 z y x hz hy hx (by rw [← h]; abel)

/-- Lemma 2.7 (Edel): the extended product of an extendable collection by an admissible set is a cap. -/
theorem ext_isCap {A : Fin 3 → Finset V} (hA : Extendable A) {S : Finset (ι → Fin 3)}
    (hS : Admissible S) : IsCap (ext S A) := by
  intro x hx y hy z hz hsum
  simp only [ext, Finset.mem_biUnion] at hx hy hz
  obtain ⟨s, hs, hxs⟩ := hx
  obtain ⟨s', hs', hys⟩ := hy
  obtain ⟨s'', hs'', hzs⟩ := hz
  rw [mem_blk] at hxs hys hzs
  have hc : ∀ c, x c + y c + z c = 0 := fun c => by
    have := congrFun hsum c; simpa using this
  -- a good coordinate gives a contradiction
  have contra : ∀ c, Good (s c) (s' c) (s'' c) → False := fun c hg =>
    no_sol_00n hA (x c) (y c) (z c) (hxs c) (hys c) (hzs c) hg (hc c)
  by_cases h1 : s = s'
  · subst h1
    by_cases h2 : s = s''
    · subst h2
      have : ∀ c, x c = y c ∧ y c = z c := fun c =>
        hA.cap (s c) (x c) (hxs c) (y c) (hys c) (z c) (hzs c) (hc c)
      exact ⟨funext fun c => (this c).1, funext fun c => (this c).2⟩
    · obtain ⟨c, hc0, hc1⟩ := hS.1 s hs s'' hs'' h2
      exact (contra c (by rw [hc0]; left; exact ⟨rfl, rfl, hc1⟩)).elim
  · by_cases h2 : s = s''
    · subst h2
      obtain ⟨c, hc0, hc1⟩ := hS.1 s hs s' hs' h1
      exact (contra c (by rw [hc0]; right; left; exact ⟨rfl, hc1, rfl⟩)).elim
    · by_cases h3 : s' = s''
      · subst h3
        obtain ⟨c, hc0, hc1⟩ := hS.1 s' hs' s hs (Ne.symm h1)
        exact (contra c (by rw [hc0]; right; right; left; exact ⟨hc1, rfl, rfl⟩)).elim
      · obtain ⟨c, hgc⟩ := hS.2 s hs s' hs' s'' hs'' h1 h2 h3
        exact (contra c hgc).elim


/-- products of caps are caps: `blk A s` for a single label vector -/
lemma blk_isCap {A : Fin 3 → Finset V} (hA : ∀ j, IsCap (A j)) (s : ι → Fin 3) : IsCap (blk A s) := by
  intro x hx y hy z hz hsum
  rw [mem_blk] at hx hy hz
  have hc : ∀ c, x c + y c + z c = 0 := fun c => by
    have := congrFun hsum c; simpa using this
  have := fun c => hA (s c) (x c) (hx c) (y c) (hy c) (z c) (hz c) (hc c)
  exact ⟨funext fun c => (this c).1, funext fun c => (this c).2⟩

/-- Lemma 2.9 (Edel): extension by a set `T` whose label vectors all contain a zero and which satisfies
the "recursive" pair condition gives a new extendable collection `(T(A), A1^ι, A2^ι)`. -/
theorem ext_extendable {A : Fin 3 → Finset V} (hA : Extendable A) {T : Finset (ι → Fin 3)}
    (hT : Admissible T) (hz : ∀ s ∈ T, ∃ c, s c = 0)
    (hrec : ∀ s ∈ T, ∀ s' ∈ T, s ≠ s' →
      (∃ c, s c = 0 ∧ s' c = 0) ∨
      (∃ i j, ((s i = 0 ∧ s' i = 1) ∨ (s i = 1 ∧ s' i = 0)) ∧ ((s j = 0 ∧ s' j = 2) ∨ (s j = 2 ∧ s' j = 0)))) :
    Extendable (![ext T A, blk A (fun _ => 1), blk A (fun _ => 2)]) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact ext_isCap hA hT
    · exact blk_isCap hA.cap _
    · exact blk_isCap hA.cap _
  · intro x hx y hy z hzz
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at hx hy hzz
    simp only [ext, Finset.mem_biUnion] at hx hy
    obtain ⟨s, hs, hxs⟩ := hx
    obtain ⟨s', hs', hys⟩ := hy
    rw [mem_blk] at hxs hys
    intro hsum
    have hc : ∀ c, x c + y c + z c = 0 := fun c => by
      have := congrFun hsum c; simpa using this
    -- z is in A1^ι or A2^ι
    have hzc : (∀ c, z c ∈ A 1) ∨ (∀ c, z c ∈ A 2) := by
      rcases hzz with h | h
      · left; rw [mem_blk] at h; exact h
      · right; rw [mem_blk] at h; exact h
    have zero_case : ∀ c, s c = 0 → s' c = 0 → False := by
      intro c h0 h0'
      have hx0 : x c ∈ A 0 := by rw [← h0]; exact hxs c
      have hy0 : y c ∈ A 0 := by rw [← h0']; exact hys c
      rcases hzc with h | h
      · exact hA.c1 _ hx0 _ hy0 _ (Or.inl (h c)) (hc c)
      · exact hA.c1 _ hx0 _ hy0 _ (Or.inr (h c)) (hc c)
    by_cases hss : s = s'
    · subst hss
      obtain ⟨c, hc0⟩ := hz s hs
      exact zero_case c hc0 hc0
    · rcases hrec s hs s' hs' hss with ⟨c, h0, h0'⟩ | ⟨i, j, hi, hj⟩
      · exact zero_case c h0 h0'
      · rcases hzc with h | h
        · -- use coordinate j: labels {0,2} and z_j ∈ A1
          rcases hj with ⟨h0, h2⟩ | ⟨h2, h0⟩
          · have hx0 : x j ∈ A 0 := by rw [← h0]; exact hxs j
            have hy2 : y j ∈ A 2 := by rw [← h2]; exact hys j
            exact hA.c2 _ hx0 _ (h j) _ hy2 (by rw [← hc j]; abel)
          · have hy0 : y j ∈ A 0 := by rw [← h0]; exact hys j
            have hx2 : x j ∈ A 2 := by rw [← h2]; exact hxs j
            exact hA.c2 _ hy0 _ (h j) _ hx2 (by rw [← hc j]; abel)
        · rcases hi with ⟨h0, h1⟩ | ⟨h1, h0⟩
          · have hx0 : x i ∈ A 0 := by rw [← h0]; exact hxs i
            have hy1 : y i ∈ A 1 := by rw [← h1]; exact hys i
            exact hA.c2 _ hx0 _ hy1 _ (h i) (hc i)
          · have hy0 : y i ∈ A 0 := by rw [← h0]; exact hys i
            have hx1 : x i ∈ A 1 := by rw [← h1]; exact hxs i
            exact hA.c2 _ hy0 _ hx1 _ (h i) (by rw [← hc i]; abel)
  · intro x hx y hy z hzz
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at hx hy hzz
    simp only [ext, Finset.mem_biUnion] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    rw [mem_blk] at hxs hy hzz
    intro hsum
    obtain ⟨c, hc0⟩ := hz s hs
    have hx0 : x c ∈ A 0 := by rw [← hc0]; exact hxs c
    exact hA.c2 _ hx0 _ (hy c) _ (hzz c) (by have := congrFun hsum c; simpa using this)

/-- disjointness of the blocks and the cardinality formula (Tyrrell Lemma 2.11, general weights) -/
theorem card_ext {A : Fin 3 → Finset V} (hA : Extendable A) (h3 : ∀ v : V, v + v + v = 0)
    {S : Finset (ι → Fin 3)} (hS : Admissible S) :
    (ext S A).card = ∑ s ∈ S, ∏ c, (A (s c)).card := by
  unfold ext
  rw [Finset.card_biUnion]
  · simp [blk, Fintype.card_piFinset]
  · intro s hs s' hs' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    rw [mem_blk] at hx hx'
    obtain ⟨c, hc0, hc1⟩ := hS.1 s hs s' hs' hne
    have hx0 : x c ∈ A 0 := by rw [← hc0]; exact hx c
    have hxn : x c ∈ A 1 ∨ x c ∈ A 2 := by
      rcases (show ∀ l : Fin 3, l ≠ 0 → l = 1 ∨ l = 2 by decide) (s' c) hc1 with h | h
      · left; rw [← h]; exact hx' c
      · right; rw [← h]; exact hx' c
    exact hA.c1 _ hx0 _ hx0 _ hxn (h3 _)

end general


/-! ### the base collection of Calderbank–Fishburn / Edel in `F_3^6` -/

abbrev V6 := Fin 6 → ZMod 3

/-! The Calderbank–Fishburn collection, listed explicitly: `A0` = the 12 vectors of weight 1;
`A1 = D ∪ R`, `A2 = D' ∪ R` where `D` (resp. `D'`) are the weight-3 vectors whose support is
(resp. is not) a block of the (6,3,2)-design {012,013,024,035,045,125,134,145,234,235}, and `R` the
weight-6 vectors with an even number of 1s.  (Generated by `src/` scripts; only the explicit lists matter.) -/

def CF0L : List V6 := [
  ![0, 0, 0, 0, 0, 1],
  ![0, 0, 0, 0, 0, 2],
  ![0, 0, 0, 0, 1, 0],
  ![0, 0, 0, 0, 2, 0],
  ![0, 0, 0, 1, 0, 0],
  ![0, 0, 0, 2, 0, 0],
  ![0, 0, 1, 0, 0, 0],
  ![0, 0, 2, 0, 0, 0],
  ![0, 1, 0, 0, 0, 0],
  ![0, 2, 0, 0, 0, 0],
  ![1, 0, 0, 0, 0, 0],
  ![2, 0, 0, 0, 0, 0]]

def CF1L : List V6 := [
  ![0, 0, 1, 1, 0, 1],
  ![0, 0, 1, 1, 0, 2],
  ![0, 0, 1, 1, 1, 0],
  ![0, 0, 1, 1, 2, 0],
  ![0, 0, 1, 2, 0, 1],
  ![0, 0, 1, 2, 0, 2],
  ![0, 0, 1, 2, 1, 0],
  ![0, 0, 1, 2, 2, 0],
  ![0, 0, 2, 1, 0, 1],
  ![0, 0, 2, 1, 0, 2],
  ![0, 0, 2, 1, 1, 0],
  ![0, 0, 2, 1, 2, 0],
  ![0, 0, 2, 2, 0, 1],
  ![0, 0, 2, 2, 0, 2],
  ![0, 0, 2, 2, 1, 0],
  ![0, 0, 2, 2, 2, 0],
  ![0, 1, 0, 0, 1, 1],
  ![0, 1, 0, 0, 1, 2],
  ![0, 1, 0, 0, 2, 1],
  ![0, 1, 0, 0, 2, 2],
  ![0, 1, 0, 1, 1, 0],
  ![0, 1, 0, 1, 2, 0],
  ![0, 1, 0, 2, 1, 0],
  ![0, 1, 0, 2, 2, 0],
  ![0, 1, 1, 0, 0, 1],
  ![0, 1, 1, 0, 0, 2],
  ![0, 1, 2, 0, 0, 1],
  ![0, 1, 2, 0, 0, 2],
  ![0, 2, 0, 0, 1, 1],
  ![0, 2, 0, 0, 1, 2],
  ![0, 2, 0, 0, 2, 1],
  ![0, 2, 0, 0, 2, 2],
  ![0, 2, 0, 1, 1, 0],
  ![0, 2, 0, 1, 2, 0],
  ![0, 2, 0, 2, 1, 0],
  ![0, 2, 0, 2, 2, 0],
  ![0, 2, 1, 0, 0, 1],
  ![0, 2, 1, 0, 0, 2],
  ![0, 2, 2, 0, 0, 1],
  ![0, 2, 2, 0, 0, 2],
  ![1, 0, 0, 0, 1, 1],
  ![1, 0, 0, 0, 1, 2],
  ![1, 0, 0, 0, 2, 1],
  ![1, 0, 0, 0, 2, 2],
  ![1, 0, 0, 1, 0, 1],
  ![1, 0, 0, 1, 0, 2],
  ![1, 0, 0, 2, 0, 1],
  ![1, 0, 0, 2, 0, 2],
  ![1, 0, 1, 0, 1, 0],
  ![1, 0, 1, 0, 2, 0],
  ![1, 0, 2, 0, 1, 0],
  ![1, 0, 2, 0, 2, 0],
  ![1, 1, 0, 1, 0, 0],
  ![1, 1, 0, 2, 0, 0],
  ![1, 1, 1, 0, 0, 0],
  ![1, 1, 2, 0, 0, 0],
  ![1, 2, 0, 1, 0, 0],
  ![1, 2, 0, 2, 0, 0],
  ![1, 2, 1, 0, 0, 0],
  ![1, 2, 2, 0, 0, 0],
  ![2, 0, 0, 0, 1, 1],
  ![2, 0, 0, 0, 1, 2],
  ![2, 0, 0, 0, 2, 1],
  ![2, 0, 0, 0, 2, 2],
  ![2, 0, 0, 1, 0, 1],
  ![2, 0, 0, 1, 0, 2],
  ![2, 0, 0, 2, 0, 1],
  ![2, 0, 0, 2, 0, 2],
  ![2, 0, 1, 0, 1, 0],
  ![2, 0, 1, 0, 2, 0],
  ![2, 0, 2, 0, 1, 0],
  ![2, 0, 2, 0, 2, 0],
  ![2, 1, 0, 1, 0, 0],
  ![2, 1, 0, 2, 0, 0],
  ![2, 1, 1, 0, 0, 0],
  ![2, 1, 2, 0, 0, 0],
  ![2, 2, 0, 1, 0, 0],
  ![2, 2, 0, 2, 0, 0],
  ![2, 2, 1, 0, 0, 0],
  ![2, 2, 2, 0, 0, 0],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 2, 2],
  ![1, 1, 1, 2, 1, 2],
  ![1, 1, 1, 2, 2, 1],
  ![1, 1, 2, 1, 1, 2],
  ![1, 1, 2, 1, 2, 1],
  ![1, 1, 2, 2, 1, 1],
  ![1, 1, 2, 2, 2, 2],
  ![1, 2, 1, 1, 1, 2],
  ![1, 2, 1, 1, 2, 1],
  ![1, 2, 1, 2, 1, 1],
  ![1, 2, 1, 2, 2, 2],
  ![1, 2, 2, 1, 1, 1],
  ![1, 2, 2, 1, 2, 2],
  ![1, 2, 2, 2, 1, 2],
  ![1, 2, 2, 2, 2, 1],
  ![2, 1, 1, 1, 1, 2],
  ![2, 1, 1, 1, 2, 1],
  ![2, 1, 1, 2, 1, 1],
  ![2, 1, 1, 2, 2, 2],
  ![2, 1, 2, 1, 1, 1],
  ![2, 1, 2, 1, 2, 2],
  ![2, 1, 2, 2, 1, 2],
  ![2, 1, 2, 2, 2, 1],
  ![2, 2, 1, 1, 1, 1],
  ![2, 2, 1, 1, 2, 2],
  ![2, 2, 1, 2, 1, 2],
  ![2, 2, 1, 2, 2, 1],
  ![2, 2, 2, 1, 1, 2],
  ![2, 2, 2, 1, 2, 1],
  ![2, 2, 2, 2, 1, 1],
  ![2, 2, 2, 2, 2, 2]]

def CF2L : List V6 := [
  ![0, 0, 0, 1, 1, 1],
  ![0, 0, 0, 1, 1, 2],
  ![0, 0, 0, 1, 2, 1],
  ![0, 0, 0, 1, 2, 2],
  ![0, 0, 0, 2, 1, 1],
  ![0, 0, 0, 2, 1, 2],
  ![0, 0, 0, 2, 2, 1],
  ![0, 0, 0, 2, 2, 2],
  ![0, 0, 1, 0, 1, 1],
  ![0, 0, 1, 0, 1, 2],
  ![0, 0, 1, 0, 2, 1],
  ![0, 0, 1, 0, 2, 2],
  ![0, 0, 2, 0, 1, 1],
  ![0, 0, 2, 0, 1, 2],
  ![0, 0, 2, 0, 2, 1],
  ![0, 0, 2, 0, 2, 2],
  ![0, 1, 0, 1, 0, 1],
  ![0, 1, 0, 1, 0, 2],
  ![0, 1, 0, 2, 0, 1],
  ![0, 1, 0, 2, 0, 2],
  ![0, 1, 1, 0, 1, 0],
  ![0, 1, 1, 0, 2, 0],
  ![0, 1, 1, 1, 0, 0],
  ![0, 1, 1, 2, 0, 0],
  ![0, 1, 2, 0, 1, 0],
  ![0, 1, 2, 0, 2, 0],
  ![0, 1, 2, 1, 0, 0],
  ![0, 1, 2, 2, 0, 0],
  ![0, 2, 0, 1, 0, 1],
  ![0, 2, 0, 1, 0, 2],
  ![0, 2, 0, 2, 0, 1],
  ![0, 2, 0, 2, 0, 2],
  ![0, 2, 1, 0, 1, 0],
  ![0, 2, 1, 0, 2, 0],
  ![0, 2, 1, 1, 0, 0],
  ![0, 2, 1, 2, 0, 0],
  ![0, 2, 2, 0, 1, 0],
  ![0, 2, 2, 0, 2, 0],
  ![0, 2, 2, 1, 0, 0],
  ![0, 2, 2, 2, 0, 0],
  ![1, 0, 0, 1, 1, 0],
  ![1, 0, 0, 1, 2, 0],
  ![1, 0, 0, 2, 1, 0],
  ![1, 0, 0, 2, 2, 0],
  ![1, 0, 1, 0, 0, 1],
  ![1, 0, 1, 0, 0, 2],
  ![1, 0, 1, 1, 0, 0],
  ![1, 0, 1, 2, 0, 0],
  ![1, 0, 2, 0, 0, 1],
  ![1, 0, 2, 0, 0, 2],
  ![1, 0, 2, 1, 0, 0],
  ![1, 0, 2, 2, 0, 0],
  ![1, 1, 0, 0, 0, 1],
  ![1, 1, 0, 0, 0, 2],
  ![1, 1, 0, 0, 1, 0],
  ![1, 1, 0, 0, 2, 0],
  ![1, 2, 0, 0, 0, 1],
  ![1, 2, 0, 0, 0, 2],
  ![1, 2, 0, 0, 1, 0],
  ![1, 2, 0, 0, 2, 0],
  ![2, 0, 0, 1, 1, 0],
  ![2, 0, 0, 1, 2, 0],
  ![2, 0, 0, 2, 1, 0],
  ![2, 0, 0, 2, 2, 0],
  ![2, 0, 1, 0, 0, 1],
  ![2, 0, 1, 0, 0, 2],
  ![2, 0, 1, 1, 0, 0],
  ![2, 0, 1, 2, 0, 0],
  ![2, 0, 2, 0, 0, 1],
  ![2, 0, 2, 0, 0, 2],
  ![2, 0, 2, 1, 0, 0],
  ![2, 0, 2, 2, 0, 0],
  ![2, 1, 0, 0, 0, 1],
  ![2, 1, 0, 0, 0, 2],
  ![2, 1, 0, 0, 1, 0],
  ![2, 1, 0, 0, 2, 0],
  ![2, 2, 0, 0, 0, 1],
  ![2, 2, 0, 0, 0, 2],
  ![2, 2, 0, 0, 1, 0],
  ![2, 2, 0, 0, 2, 0],
  ![1, 1, 1, 1, 1, 1],
  ![1, 1, 1, 1, 2, 2],
  ![1, 1, 1, 2, 1, 2],
  ![1, 1, 1, 2, 2, 1],
  ![1, 1, 2, 1, 1, 2],
  ![1, 1, 2, 1, 2, 1],
  ![1, 1, 2, 2, 1, 1],
  ![1, 1, 2, 2, 2, 2],
  ![1, 2, 1, 1, 1, 2],
  ![1, 2, 1, 1, 2, 1],
  ![1, 2, 1, 2, 1, 1],
  ![1, 2, 1, 2, 2, 2],
  ![1, 2, 2, 1, 1, 1],
  ![1, 2, 2, 1, 2, 2],
  ![1, 2, 2, 2, 1, 2],
  ![1, 2, 2, 2, 2, 1],
  ![2, 1, 1, 1, 1, 2],
  ![2, 1, 1, 1, 2, 1],
  ![2, 1, 1, 2, 1, 1],
  ![2, 1, 1, 2, 2, 2],
  ![2, 1, 2, 1, 1, 1],
  ![2, 1, 2, 1, 2, 2],
  ![2, 1, 2, 2, 1, 2],
  ![2, 1, 2, 2, 2, 1],
  ![2, 2, 1, 1, 1, 1],
  ![2, 2, 1, 1, 2, 2],
  ![2, 2, 1, 2, 1, 2],
  ![2, 2, 1, 2, 2, 1],
  ![2, 2, 2, 1, 1, 2],
  ![2, 2, 2, 1, 2, 1],
  ![2, 2, 2, 2, 1, 1],
  ![2, 2, 2, 2, 2, 2]]

def CF : Fin 3 → Finset V6 := ![CF0L.toFinset, CF1L.toFinset, CF2L.toFinset]

/-- fast criterion for caps in characteristic 3 -/
lemma isCap_of_pairs {V : Type*} [AddCommGroup V] [DecidableEq V] (h3 : ∀ v : V, v + v + v = 0)
    (A : Finset V) (h : ∀ x ∈ A, ∀ y ∈ A, -(x + y) ∈ A → x = y) : IsCap A := by
  intro x hx y hy z hz hsum
  have hz' : z = -(x + y) := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum
  have hxy : x = y := h x hx y hy (hz' ▸ hz)
  subst hxy
  refine ⟨rfl, ?_⟩
  rw [hz']; symm; rw [neg_eq_iff_add_eq_zero]; exact h3 x

lemma h3_V6 : ∀ v : V6, v + v + v = 0 := by
  intro v; funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize v i = a
  revert a; decide

def cfCapOK (L : List V6) : Bool := L.all (fun x => L.all (fun y => !(decide (-(x + y) ∈ L)) || decide (x = y)))
def cfC1OK : Bool := CF0L.all (fun x => CF0L.all (fun y => !(decide (-(x + y) ∈ CF1L)) && !(decide (-(x + y) ∈ CF2L))))
def cfC2OK : Bool := CF0L.all (fun x => CF1L.all (fun y => !(decide (-(x + y) ∈ CF2L))))

lemma cf_checks : cfCapOK CF0L = true ∧ cfCapOK CF1L = true ∧ cfCapOK CF2L = true ∧ cfC1OK = true ∧
    cfC2OK = true := by native_decide

lemma CF_card : (CF 0).card = 12 ∧ (CF 1).card = 112 ∧ (CF 2).card = 112 := by native_decide

lemma cap_of_cfCapOK (L : List V6) (h : cfCapOK L = true) : IsCap L.toFinset := by
  apply isCap_of_pairs h3_V6
  intro x hx y hy hm
  simp only [List.mem_toFinset] at hx hy hm
  simp only [cfCapOK, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq] at h
  rcases h x hx y hy with h1 | h1
  · exact absurd hm h1
  · exact h1

lemma CF_extendable : Extendable CF := by
  obtain ⟨h0, h1, h2, hc1, hc2⟩ := cf_checks
  refine ⟨?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact cap_of_cfCapOK _ h0
    · exact cap_of_cfCapOK _ h1
    · exact cap_of_cfCapOK _ h2
  · intro x hx y hy z hz hsum
    have hz' : z = -(x + y) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum
    simp only [CF, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, List.mem_toFinset] at hx hy hz
    simp only [cfC1OK, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hc1
    obtain ⟨n1, n2⟩ := hc1 x hx y hy
    rcases hz with hz | hz
    · exact n1 (hz' ▸ hz)
    · exact n2 (hz' ▸ hz)
  · intro x hx y hy z hz hsum
    have hz' : z = -(x + y) := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum
    simp only [CF, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, List.mem_toFinset] at hx hy hz
    simp only [cfC2OK, List.all_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hc2
    exact hc2 x hx y hy (hz' ▸ hz)

/-! ### the recursively admissible set `Ĩ(4,3)` and the collection in `F_3^24` -/

/-- `Ĩ(4,3)` (Edel; Tyrrell Lemma 2.12): one zero; entries before it are 1, after it 2 -/
def Itil : Finset (Fin 4 → Fin 3) := {![1, 1, 1, 0], ![1, 1, 0, 2], ![1, 0, 2, 2], ![0, 2, 2, 2]}

lemma Itil_adm : Admissible Itil := by
  unfold Admissible
  constructor
  · decide
  · decide
lemma Itil_zero : ∀ s ∈ Itil, ∃ c, s c = 0 := by decide
lemma Itil_rec : ∀ s ∈ Itil, ∀ s' ∈ Itil, s ≠ s' →
    (∃ c, s c = 0 ∧ s' c = 0) ∨
    (∃ i j, ((s i = 0 ∧ s' i = 1) ∨ (s i = 1 ∧ s' i = 0)) ∧ ((s j = 0 ∧ s' j = 2) ∨ (s j = 2 ∧ s' j = 0))) := by
  decide

abbrev V24 := Fin 4 → V6

def E2 : Fin 3 → Finset V24 := ![ext Itil CF, blk CF (fun _ => 1), blk CF (fun _ => 2)]

lemma E2_extendable : Extendable E2 := ext_extendable CF_extendable Itil_adm Itil_zero Itil_rec

lemma h3_V24 : ∀ v : V24, v + v + v = 0 := by
  intro v; funext j; simp only [Pi.add_apply, Pi.zero_apply]; exact h3_V6 (v j)

/-! ### flattening block vectors and the final count -/

def flat {g : ℕ} (v : BVec g) : Fin g × Fin 3 → Fin 3 := fun p => v p.1 p.2

lemma flat_inj {g : ℕ} : Function.Injective (@flat g) := by
  intro v w h; funext i k; exact congrFun h (i, k)

def flatE {g : ℕ} : BVec g ↪ (Fin g × Fin 3 → Fin 3) := ⟨flat, flat_inj⟩

lemma adm_flat {g : ℕ} (S : Finset (BVec g)) (h : IsAdmissible S) : Admissible (S.map flatE) := by
  constructor
  · intro s hs s' hs' hne
    simp only [Finset.mem_map] at hs hs'
    obtain ⟨v, hv, rfl⟩ := hs
    obtain ⟨w, hw, rfl⟩ := hs'
    have hvw : v ≠ w := fun e => hne (by rw [e])
    obtain ⟨⟨i, k, h1⟩, -⟩ := h.1 v hv w hw hvw
    exact ⟨(i, k), h1⟩
  · intro s hs s' hs' s'' hs'' h1 h2 h3
    simp only [Finset.mem_map] at hs hs' hs''
    obtain ⟨u, hu, rfl⟩ := hs
    obtain ⟨v, hv, rfl⟩ := hs'
    obtain ⟨w, hw, rfl⟩ := hs''
    obtain ⟨i, k, hk⟩ := h.2 u hu v hv w hw (fun e => h1 (by rw [e])) (fun e => h2 (by rw [e]))
      (fun e => h3 (by rw [e]))
    exact ⟨(i, k), hk⟩

/-- number of nonzero coordinates of an orbit element equals the weight of the type -/
lemma orb_nnz (t : Fin 7) : ∀ u ∈ orb t, (Finset.univ.filter (fun k => u k ≠ 0)).card = wt t := by
  revert t; decide

lemma orb_nz (t : Fin 7) : ∀ u ∈ orb t, (Finset.univ.filter (fun k => u k = 0)).card = 3 - wt t := by
  revert t; decide

lemma prod_block (f : Fin 3 → ℕ) (hf : f 2 = f 1) (t : Fin 7) (u : Fin 3 → Fin 3) (hu : u ∈ orb t) :
    ∏ k, f (u k) = f 0 ^ (3 - wt t) * f 1 ^ wt t := by
  have h1 : ∀ k, f (u k) = if u k = 0 then f 0 else f 1 := by
    intro k
    rcases (show ∀ l : Fin 3, l = 0 ∨ l = 1 ∨ l = 2 by decide) (u k) with h | h | h <;> simp [h, hf]
  rw [Finset.prod_congr rfl (fun k _ => h1 k), Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have hn := orb_nnz t u hu
  have hz : (Finset.univ.filter (fun k => u k = 0)).card = 3 - wt t := orb_nz t u hu
  rw [hz, hn]

/-- the weighted size of the extended product over an expanded row set -/
theorem card_ext_rows {V : Type*} [AddCommGroup V] [DecidableEq V] {A : Fin 3 → Finset V}
    (hA : Extendable A) (h3 : ∀ v : V, v + v + v = 0) (h12 : (A 2).card = (A 1).card)
    {g : ℕ} (R : Finset (Fin g → Fin 7)) (hR : RowsOK R) :
    (ext ((expandAll R).map flatE) A).card =
      ∑ t ∈ R, ∏ i, ((orb (t i)).card * ((A 0).card ^ (3 - wt (t i)) * (A 1).card ^ wt (t i))) := by
  rw [card_ext hA h3 (adm_flat _ (admissible_of_rowsOK R hR)), Finset.sum_map]
  unfold expandAll
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro t _
    have : ∀ v ∈ expand t, ∏ c, (A (flatE v c)).card =
        ∏ i, ((A 0).card ^ (3 - wt (t i)) * (A 1).card ^ wt (t i)) := by
      intro v hv
      rw [mem_expand] at hv
      rw [Fintype.prod_prod_type]
      apply Finset.prod_congr rfl
      intro i _
      exact prod_block (fun l => (A l).card) h12 (t i) (v i) (hv i)
    rw [Finset.sum_congr rfl this, Finset.sum_const, smul_eq_mul]
    conv_rhs => rw [Finset.prod_mul_distrib]
    congr 1
    simp [expand, Fintype.card_piFinset]
  · intro t ht t' ht' htt
    rw [Function.onFun, Finset.disjoint_left]
    intro v hv hv'
    rw [mem_expand] at hv hv'
    obtain ⟨i, hi⟩ := hR.1 t ht t' ht' htt
    have := orb_wt (t i) (t' i) (v i) (hv i) (hv' i)
    omega

/-- the certified rows, encoded in base 7 (digit i = type of block i) -/
def codesR : List ℕ := [
22417088,
24117454,
22732580,
22352716,
9029913,
38114121,
22446698,
36148407,
38385460,
20501755,
11247507,
35824134,
8699456,
20228953,
21869660,
35865656,
35829937,
22458866,
38379850,
36115037,
36189758,
35870425,
36189574,
34143553,
38431018,
20541914,
20210417,
22783617,
33430340,
38935282,
22783738,
36065935,
38386246,
26529950,
8882654,
31707488,
7284381,
38884058,
8648004,
35635556,
26856976,
20497069,
10882555,
31713853,
30112389,
9029115,
22732172,
10769702,
8700291,
22417855,
22412136,
23746559,
22173117,
10929105,
26854482,
22436751,
34151020,
24104960,
36189777,
33909055,
8653021,
36144139,
10574635,
34143439,
10937091,
36206810,
33988172,
24536469,
8652025,
21824839,
2940615,
21824706,
24660311,
20461988,
24117435,
7000963,
22739277,
36112637,
38879126,
24574869,
8971472,
38889171,
22139251,
8973074,
32722569,
34447533,
9012956,
38383738,
22737188,
31712922,
36059437,
36189903,
20549205,
8971339,
39204975,
26530797,
30103492,
38093084,
38424417,
38889530,
32078805,
24299475,
24424293,
38386234,
10300807,
22458584,
26530965,
11208154,
8693623,
20548274,
24676280,
8692843,
20457169,
21869508,
10665759,
24579706,
7326080,
37243491,
38422805,
20181757,
22739258,
26849890,
16693641,
30066770,
24666107,
7320151,
22457767,
20177916,
26901438,
8935569,
8883433,
38059610,
24530902,
18809965,
33908827,
20497249,
26583757,
30066903,
22214486,
22783605,
36195687,
26584389,
32722450,
8655014,
11253773,
10339928,
35870852,
10924089,
38430934,
30385172,
24294638,
20182422,
24299323,
30102561,
20548407,
24267542,
7000230,
10339909,
20457036,
9018789,
35008893,
10574673,
4803645,
24328268,
38430922,
35882330,
22470297,
38093996,
22738082,
10642454,
24294619,
26570571,
35589769,
38378786,
10665911,
20418770,
11325236,
34313205,
22855633,
24302331,
27243501,
22465215,
11319536,
35857886,
20231359,
38878328,
10301871,
29503772,
36189170,
11254102,
24659590,
35869837,
26564397,
31759624,
38385303,
39204520,
6501849,
36109172,
26584408,
26852424,
8882635,
7045849,
31985871,
10683646,
35328226,
20231340,
8932237,
35829739,
38819553,
7242878,
35326527,
30431722,
30060253,
24340257,
38386575,
38385399,
34313338,
8932256,
20501090,
37288977,
38105756,
2916836,
33914798,
24346755,
38431055,
18895857,
8966635,
20210569,
31707355,
24302312,
7241168,
24613952,
24329085,
36206962,
38064272,
20181624,
11206822,
26855800,
9012861,
31706557,
30378655,
20559626,
8680932,
35382452,
10883240,
22105868,
38936080,
11248192,
20181738,
35828941,
11248325,
22464284,
26837999,
30059322,
20548286,
35641058,
38378882,
33498657,
10301283,
24618808,
20452153,
20231492,
24349077,
20559512,
40032179,
8680970,
38117661,
32078026,
22465203,
38935119,
38379729,
32025757,
26895574,
22452872,
31712941,
22418749,
22783762,
32026555,
8687257,
40149189,
32132181,
11320448,
11207685,
37242560,
38923027,
31755356,
11247603,
31988384,
6182516,
36148388,
10340061,
36127593,
35824279,
8686537,
30111381,
39254255,
33993788,
35831911,
32032388,
11207799,
10340023,
11248600,
8648317,
22736402,
20419568,
7006747,
7371699,
20541890,
35858665,
32025738,
18569767,
36109305,
38111601,
30099355,
10300826,
38883944,
26849283,
7280461,
22172186,
22149867,
22466804,
33908808,
34306840,
39443927,
21830425,
10917232,
22416936,
35589937,
36205898,
20457132,
38935149,
31985852,
40142833,
22172851,
20223367,
36151244,
31712124,
33791661,
38060396,
35629543,
8967223,
30112522,
7407621,
10609526,
24579554,
24299342,
9030027,
24335240,
18894686,
36206943,
26529969,
38889511,
10682487,
33663617,
32266100,
32310004,
22738917,
24614540,
3264981,
26534654,
22419717,
8652006,
35830796,
20541757,
35046999,
24677211,
22139106,
38064253,
22736421,
3207357,
18575353,
20211500,
20541769,
8966557,
24333854,
37281662,
22172984,
38105901,
26856995,
35594641,
8889019,
8701760,
10334211,
38384505,
32261053,
35588922,
33913939,
38065268,
23795932,
35623369,
20558581,
11209336,
7046437,
10608841,
8701855,
10923254,
8687942,
24677230,
10501904,
38890594,
32072307,
26576584,
24617368,
31753107,
11319517,
20177634,
22731626,
35825065,
24340238,
22777917,
11326965,
35595355,
30065839,
38386367,
34306821,
8681901,
22850066,
22738929,
20183479,
9028963,
10609507,
10888420,
32244350,
29867360,
8693528,
7046582,
10340859,
31746457,
8648042,
24535538,
20500957,
33680290,
22738143,
2889087,
22731602,
22149410,
20229037,
20496271,
30111591,
20183418,
31707222,
26504554,
20558695,
5538615,
10295354,
10576108,
20542688,
8680837,
34314288,
38113988,
38425348,
38386594,
20503586,
21870572,
20503927,
10300959,
8654672,
10608919,
8967242,
22413200,
30430791,
26855716,
34440584,
40144420,
10887337,
22464272,
36190017,
22458458,
20542460,
36189970,
8889038,
8652120,
24660586,
34314155,
20177869,
31759605,
20182688,
36134110,
2924006,
35596615,
35635129,
22458698,
36936161,
24335716,
26530538,
26853987,
36059418,
8699438,
8935588,
10346426,
24618675,
20541853,
26576157,
22777221,
4811470,
35320694,
22849135,
7365182,
22139353,
10937072,
20223253,
7052366,
7000818,
20184253,
31713074,
31759472,
24677344,
22172053,
26854006,
24328135,
22418665,
8882521,
38431865,
33912943,
30339553,
8701893,
10928252,
38936061,
26895901,
33679492,
10346578,
22778199,
35628871,
22453348,
22466690,
34423803,
11320467,
36968109,
21870458,
24059341,
8922535,
31758674,
30386103,
24537400,
10883648,
20230005,
38111685,
30111458,
33668972,
24301136,
11254955,
8647890,
30378788,
30339686,
24579687,
21876025,
20458604,
34424650,
40150965,
37236841,
8972354,
11197178,
38889987,
26895497,
38379897,
30379719,
39197527,
11327098,
38060564,
35831930,
40142985,
38026640,
10916168,
36188486,
22417753,
32078938,
38431825,
10923749,
22413247,
8464209,
20413165,
18901203,
11320600,
9013269,
36060349,
38883925,
34773597,
32338816,
33869720,
22418019,
20418618,
20231473,
24530769,
33669105,
10928954,
22412965,
22412232,
7320296,
37288179,
22419596,
11205382,
24537267,
31713872,
33913057,
22139125,
36206012,
10294442,
20177489,
22173098,
16655127,
20223488,
8653089,
8470137,
26582086,
26563599,
22777791,
29274615,
40142852,
21824041,
30430714,
9019624,
27394928,
31986788,
30033177,
7040851,
32313189,
20559379,
10923273,
9236294,
24621664,
7039484,
10347490,
22104139,
26504279,
32077874,
11197766,
33908124,
22737998,
24343379,
20457193,
37242427,
11320581,
7004934,
36144398,
6811285,
21869527,
36149984,
26854120,
38884077,
9013107,
24529838,
10340840,
33877289,
8681749,
10682631,
8883452,
31706538,
26577989,
30025729,
22739050,
8701741,
35595439,
33668174,
22412148,
20217541,
8883566,
22418786,
38094015,
22854867,
36066068,
33915913,
20211367,
8687923,
20542868,
7033746,
11326053,
31752176,
38385779,
11210181,
22139365,
36060501,
38431853,
22457888,
11254024,
34314136,
10340042,
8890083,
22195491,
36195748,
22419925,
24537419,
11319631,
21824972,
32026821,
10682715,
7007923,
20183322,
35876415,
8974850,
24269223,
38378943,
26569899,
35870444,
21876044,
10682138,
8889152,
38928613,
24378674,
26849302,
22458439,
35643361,
33985052,
26895749,
20183334,
7241947,
22446565,
22731481,
10883335,
9011637,
26895642,
34149139,
8890102,
24619739,
10888466,
38384669,
14700503,
3262551,
22132934,
8653819,
26564530,
22195510,
22139533,
36151263,
10665892,
11207753,
22732153,
22457851,
33914007,
10642587,
7248266,
8692939,
38770893,
22777100,
28620453,
1293543,
33359798,
35829074,
33505995,
20176962,
10643518,
8974005,
22139486,
20465320,
10346559,
10889150,
36109153,
36066885,
39316058,
40142966,
35863453,
38114140,
24536336,
31706424,
22784548,
20503719,
21830558,
24300406,
34144484,
24329199,
30379593,
8922782,
24537286,
11326186,
33915705,
35858684,
37236043,
21870325,
20542441,
22445900,
32026802,
10294290,
8967650,
38106015,
32720373,
38105775,
24301155,
20229884,
33680258,
10574654,
8949897,
24619785,
24614559,
30032246,
24618789,
20216838,
22837857,
35593759,
34144351,
22417069,
22777245,
32078957,
36205879,
20176901,
10334323,
11326034,
22850180,
11208483,
7236361,
32072288,
8688399,
35643494,
38379470,
11209659,
26536486,
31752024,
32026688,
8681882,
9012272,
26901139,
34150887,
34144503,
26901335,
36112504,
22413067,
32072421,
11499741,
8653135,
38889303,
22731565,
38883013,
10890003,
37236974,
36092462,
33913076,
31758560,
38094148,
37282593,
36067018,
9012176,
38098784,
30065041,
11202819,
35858551,
33668041,
29507631,
20502021,
35858817,
24328287,
22445748,
34424734,
35291332,
18937353,
35996439,
24620469,
24529971,
21870439,
10916961,
10609659,
36099470,
35865315,
20496822,
10934769,
8693661,
10347509,
36144284,
22849933,
8648155,
26850298,
38065070,
37282460,
33913741,
26537662,
22778031,
8971453,
10643385,
35588838,
4785387,
10347357,
26535783,
22732412,
20417804,
10934691,
31986655,
22138422,
35634457,
24346774,
22457912,
20548431,
40144401,
26855116,
26855070,
9054674,
8973152,
22458686,
32148794,
8932351,
36127334,
8654995,
39205108,
38935130,
10770824,
8882502,
8889133,
35869898,
30431855,
7303490,
35635388,
38060137,
7054669,
24619671,
32026669,
32267570,
29491767,
23942420,
8693774,
10937224,
10934787,
31707469,
11208501,
18537182,
9012994,
26571047,
34313224,
26535149,
34423670,
18895617,
22412839,
5125539,
7275463,
36148274,
24430810,
40144581,
9018771,
8680951,
30424197,
20497081,
34144370,
38060282,
21863941,
24340826,
26582933,
24676299,
33908257,
8974347,
20468042,
8889969,
34307619,
21831489,
38379615,
20229074,
22854835,
22457755,
7034677,
18856515,
36112485,
10928270,
24536488,
20412234,
24300452,
4785520,
10609640,
32071490,
9029096,
36059570,
24579573,
35869753,
10340973,
9030046,
33498052,
18581870,
9029077,
35865334,
11201966,
20229098,
9012254,
34421360,
38105168,
8932389,
38065982,
24300338,
18530665,
10573889,
22412269,
38929563,
18809131,
20502655,
35622571,
20465187,
22195358,
24660178,
8655517,
36149338,
22856716,
20496234,
26529866,
24583019,
33669086,
35857867,
35878676,
20184265,
22195377,
35864858,
8883585,
34307752,
7407754,
37281529,
10916149,
6441530,
8971491,
22446679,
32033319,
30065972,
22295673,
20497202,
31713055,
33876358,
24349210,
36967094,
8882616,
39198591,
5157100,
34424715,
22464368,
20413184,
10294309,
31752043,
32031457,
18530905,
11206689,
38064386,
10574521,
10574540,
8652158,
31986769,
30337173,
18849067,
35870570,
22418810,
34144237,
8889171,
24618656,
24676413,
10917080,
20181605,
8701874,
8457692,
33914641,
38383605,
26850179,
38879259,
8967375,
22451499,
38424501,
10294423,
22856583,
34306688,
29290083,
35825233,
10346540,
26582002,
5164053,
22778152,
20229872,
31758541,
20584305,
24529952,
26561903,
11208405,
8688740,
34150070,
20461969,
34307771,
38424562,
9601246,
36149072,
37243358,
38114007,
38100665,
34307505,
39364701,
38425336,
33912924,
20418751,
36060368,
33870651,
36149270,
35870684,
38883811,
11206803,
36099700,
10928859,
10935622,
32078824,
20503946,
38094129,
38066127,
38030756,
10888876,
20182524,
20223127,
38936050,
20549217,
38093065,
36195603,
38922687,
26894902,
32072174,
38882994,
33914737,
5641549,
35596286,
24295207,
31706405,
38878195,
20542586,
1634728,
35593626,
38805269,
22452169,
22783701,
26451569,
34143420,
20496150,
24336057,
22104272,
10619817,
26855002,
18576524,
36104365,
39204044,
38929544,
33908281,
35829055,
22849249,
26894970,
10665778,
39490843,
34425238,
38425516,
11248173,
24341253,
38888713,
20496295,
38883146,
34151001,
22736269,
35589510,
20223355,
22737284,
10889168,
26453741,
35407834,
24295634,
31714005,
23157237,
20412918,
10609621,
8922554,
35828922,
5538699,
32715933,
26849871,
38379717,
11202668,
36066866,
38883127,
20502812,
22412820,
35878657,
7235430,
7319563,
20210436,
20413051,
38928746,
22138579,
20222581,
22738119,
24328154,
10620254,
10928992,
35831582,
18855584,
24530883,
38066913,
18576284,
16648022,
7288497,
5442688,
10916263,
7327256,
22079925,
20211481,
8972422,
20176817,
35830005,
35623502,
38385315,
11319650,
18850238,
38935263,
8647909,
8412073,
32033205,
32071357,
8974328,
35824825,
38431986,
8647302,
30060386,
20502788,
35628157,
20177736,
35824806,
21870591,
38112532,
22445881,
11500653,
22849116,
31713986,
36144158,
26568077,
40134468,
37235910,
10609772,
26537643,
38093217,
10346445,
36060235,
20177748,
8652139,
10295373,
26583169,
34149937,
34150868,
10682619,
23027898,
22732400,
11201984,
35622438,
26564416,
20502667,
32078007,
20413032,
11246968,
26576176,
22732298,
30338769,
33913843,
26902266,
10916282,
36148255,
24335259,
35324829,
8647224,
26849199,
20222424,
20501953,
22464429,
8688418,
35641905,
39198458,
26563466,
8973170,
20558562,
20211234,
8967337,
34423784,
31759491,
35372993,
20223535,
33668155,
30059455,
38379489,
38819698,
36188402,
35634541,
38105872,
5118434,
10573688,
8681768,
36206696,
24676432,
10340992,
26536467,
24349058,
38065336,
31752157,
33909188,
22855785,
24530750,
30108273,
4921246,
38105229,
10922582,
22736288,
20182620,
22777184,
22104253,
36104449,
24536355,
8927551,
10890848,
36189874,
8935721,
8932370,
30425205,
24666088,
20235013,
37275943,
10318697,
39181490,
11206670,
30026660,
24574850,
38383586,
8680818,
30099579,
38093882,
39197660,
33914774,
29615254,
30430924,
26534673,
24701991,
18849998,
21824022,
22196441,
38820040,
32033338,
33908953,
26533091,
35858798,
38060156,
10295240,
11202706,
10890345,
38431079,
36189086,
24620488,
18902134,
38055837,
21876158,
26575485,
26534787,
26575569,
35864167,
22416955,
30106005,
3118520,
34143572,
34314269,
36196534,
10347376,
10882651,
38424405,
8927455,
20542821,
9028982,
36066999,
26584522,
24295226,
39364568,
3175884,
10887489,
24659571,
32077893,
11326167,
8647320,
21824953,
34306707,
32261984,
37288046,
33090770,
11209678,
38093198,
33915572,
22446812,
24569871,
20500938,
33668839,
26894818,
24349191,
36150915,
10882633,
24614692,
20418637,
26502873,
36099451,
36973611,
21829640,
27289953,
38890575,
22138555,
24329066,
26576416,
8653837,
20503598,
22464405,
22727853,
22732533,
11247585,
10665873,
36150129,
8653790,
32032407,
24613971,
38424538,
24569852,
11499718,
36206031,
10666842,
32658149,
35042162,
22138434,
20558714,
7365770,
20211348,
22418653,
10294404,
26535737,
21876177,
26563485,
8972468,
24660159,
38100170,
22466671,
11499494,
32032255,
26536383,
11248287,
20223108,
34431755,
10301757,
30386236,
10642435,
20210550,
20412101,
10921868,
22737086,
20496841,
20177508,
35824218,
11206784,
35876354,
38099498,
22777088,
20461855,
8692921,
38425469,
20216850,
33913874,
37241629,
33668953,
10334570,
22417951,
38378919,
20412120,
9281913,
35830735,
38375170,
24335735,
10889072,
10883373,
8971358,
8966653,
30104941,
10934440,
33914653,
10887356,
32072440,
30424274,
27649515,
38034153,
33431271,
11500672,
38084068,
20559645,
22138518,
7381891,
10666823,
36143467,
5175946,
32306672,
33668022,
9054801,
34447514,
34150089,
34314265,
31707336,
20222436,
20496138,
38384601,
36143612,
9012842,
10334342,
34149956,
36060482,
38425234,
35320010,
10666690,
20542700,
24583038,
10928174,
34424582,
11202554,
24111477,
20548370,
38928632,
24582886,
26530557,
38067242,
20496967,
31750556,
24340845,
20228941,
11319669,
32773935,
24299456,
26567405,
22849268,
24529819,
11201349,
35630019,
10643499,
36206829,
26893549,
23853556,
35996458,
21823889,
38059549,
20222520,
20184613,
22196308,
10937205,
18582801,
10592181,
38889663,
29615235,
35876270,
20183455,
7285165,
38100987,
20419701,
8967488,
36066087,
36109286,
10295221,
38383719,
38928765,
5123222,
32025890,
10917099,
24093656,
33869865,
10888352,
30424407,
21823908,
20218017,
32071509,
35830651,
24677363,
38066066,
22778019,
27289120,
35864839,
30385305,
30105074,
38064405,
22466823,
11201888,
33908136,
38384403,
10883486,
38425089,
10300921,
32032274,
20502751,
32071376,
11248438,
35824951,
38100189,
34307638,
8699360,
20222557,
11202573,
8956414,
8888221,
33909235,
22850047,
38929696,
9018693,
10917213,
10300009,
35877201,
8693936,
38106183,
38105084,
32314120,
33993776,
32025871,
36059551,
31758693,
18529734,
10887451,
34313357,
20176938,
33679017,
4587672,
36149174,
18536251,
22850199,
26901419,
26582105,
38425108,
26910048,
38378798,
22445767,
20412253,
22452181,
24329218,
26535669,
31755375,
30350024,
36190185,
24295359,
686235,
8693509,
35857753,
34423651,
36231590,
9029894,
22737986,
24064844,
36104510,
35640974,
22446831,
9555627,
7324267,
10643366,
22212086,
26965271,
26569185,
26537314,
31746438,
29507650,
22731469,
11254120,
10608937,
10916301,
20184386,
38059465,
4674339,
22412293,
26856647,
26855819,
38936213,
36065137,
37289110,
10887470,
31986636,
26451702,
22413079,
20176805,
10301738,
22458819,
35857734,
24621645,
10937186,
36065954,
31753088,
10929267,
40151098,
20218339,
20467574,
21877108,
23029112,
21876975,
21831356,
35241627,
36114892,
22215476,
38804181,
10642568,
23029317,
36114872,
20467555,
24080264,
38111746,
21829608,
20417820,
22451467,
20216136,
20584273,
22212200,
22196422,
38936194,
10642549,
21877089,
20465301,
22856697,
21831470,
20419682,
38100646,
22453329,
20217998,
10924070,
22855766,
21830882,
22172167,
21869641,
20501071,
22212067,
21863922,
20452134,
23029093,
22452853,
20217522,
22196289,
21876956,
20465168,
22856564,
32033186,
38890442,
21831337,
20419549,
20184594,
22172965,
20559493,
21824820,
22104120,
20461836,
21830406,
22172034,
24585292,
8937975,
10520381,
8889950,
23865139,
26587873,
11499513,
26570590,
10666709,
24582905,
11326984,
27274581,
8927533,
24585272,
22150658,
20501857,
22784669,
20549338,
22465336,
22784536,
22419584,
10685877,
22777772,
31752841,
8937956,
38890431,
3173498,
10682601,
33908220,
38929677,
10923730,
10682468,
30425338,
29479386,
36115213,
38890461,
33909067,
33915584,
21878241,
38923046,
33498297,
38098816,
22737352,
20457048,
33625522]

def rowsR : List (Fin 9 → Fin 7) := codesR.map (decodeRow 9)

/-! ### the certified data: checks -/

theorem rows_nodup : rowsR.Nodup := by native_decide
theorem rows_chkP : chkP rowsR = true := by native_decide
theorem rows_chkT : chkT rowsR = true := by native_decide

theorem rows_ok : RowsOK rowsR.toFinset := rowsOK_of_check rowsR rows_chkP rows_chkT

/-- **The new admissible set** (in block form, `{0,1,2}^27`). -/
theorem admissible_new : IsAdmissible (expandAll rowsR.toFinset) :=
  admissible_of_rowsOK _ rows_ok

/-! ### sizes of the collections -/

lemma CF_card_of (l : Fin 3) : (CF l).card = if l = 0 then 12 else 112 := by
  obtain ⟨h0, h1, h2⟩ := CF_card
  fin_cases l <;> simp [h0, h1, h2]

lemma E2_card0 : (E2 0).card = 4 * 12 * 112 ^ 3 := by
  show (ext Itil CF).card = _
  have h3 : ∀ v : V6, v + v + v = 0 := h3_V6
  rw [card_ext CF_extendable h3 Itil_adm]
  simp only [CF_card_of]
  decide

lemma E2_card1 : (E2 1).card = 112 ^ 4 := by
  show (blk CF (fun _ => 1)).card = _
  simp [blk, Fintype.card_piFinset, CF_card_of]

lemma E2_card2 : (E2 2).card = 112 ^ 4 := by
  show (blk CF (fun _ => 2)).card = _
  simp [blk, Fintype.card_piFinset, CF_card_of]

/-! ### the final count -/

def ocb (t : Fin 7) : ℕ := if wtb t = 0 ∨ wtb t = 3 then 1 else 3

def rowTerm {g : ℕ} (t : Fin g → Fin 7) : ℕ :=
  ∏ i, (ocb (t i) * ((4 * 12 * 112 ^ 3) ^ (3 - wtb (t i)) * (112 ^ 4) ^ wtb (t i)))

lemma rowTerm_eq {g : ℕ} (t : Fin g → Fin 7) :
    ∏ i, ((orb (t i)).card * ((4 * 12 * 112 ^ 3) ^ (3 - wt (t i)) * (112 ^ 4) ^ wt (t i))) = rowTerm t := by
  unfold rowTerm
  apply Finset.prod_congr rfl
  intro i _
  rw [orb_card, ← wtb_eq]
  rfl

/-- the size of the final cap set in `F_3^648` -/
def Mfinal : ℕ := (rowsR.map rowTerm).sum

theorem Mfinal_bound : 2220334 ^ 648 < Mfinal * 1000000 ^ 648 := by decide +kernel

/-- **Main theorem.**  There is a cap set `A` in `F_3^648` (written as `(Fin 9 × Fin 3) → Fin 4 → Fin 6 → ZMod 3`,
i.e. `27 · 4 · 6 = 648` coordinates) with `|A|^(1/648) > 2220334 / 1000000`. -/
lemma sum_rowTerm {g : ℕ} (L : List (Fin g → Fin 7)) :
    (L.map (fun t => ∏ i, ((orb (t i)).card * ((4 * 12 * 112 ^ 3) ^ (3 - wt (t i)) * (112 ^ 4) ^ wt (t i))))).sum
      = (L.map rowTerm).sum := by
  congr 1
  exact List.map_congr_left (fun t _ => rowTerm_eq t)

lemma card_final : (ext ((expandAll rowsR.toFinset).map flatE) E2).card = Mfinal := by
  rw [card_ext_rows E2_extendable h3_V24 (by rw [E2_card1, E2_card2]) _ rows_ok, E2_card0, E2_card1,
    List.sum_toFinset _ rows_nodup, sum_rowTerm]
  rfl

theorem main_cap : ∃ A : Finset (Fin 9 × Fin 3 → Fin 4 → Fin 6 → ZMod 3),
    IsCap A ∧ (2220334 : ℝ) ^ 648 < (A.card : ℝ) * (1000000 : ℝ) ^ 648 := by
  refine ⟨ext ((expandAll rowsR.toFinset).map flatE) E2, ext_isCap E2_extendable (adm_flat _ admissible_new), ?_⟩
  have h1 : ((2220334 ^ 648 : ℕ) : ℝ) < ((Mfinal * 1000000 ^ 648 : ℕ) : ℝ) := Nat.cast_lt.mpr Mfinal_bound
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat] at h1
  rw [card_final]
  exact h1

/-- Products: for every `k ≥ 1` there is a cap set in `F_3^(648 k)` of size `> (2220334/1000000)^(648 k)`;
hence the cap-set capacity is at least `2220334/1000000`. -/
theorem main_capacity (k : ℕ) (hk : 1 ≤ k) : ∃ B : Finset (Fin k → Fin 9 × Fin 3 → Fin 4 → Fin 6 → ZMod 3),
    IsCap B ∧ (2220334 : ℝ) ^ (648 * k) < (B.card : ℝ) * (1000000 : ℝ) ^ (648 * k) := by
  obtain ⟨A, hA, hcard⟩ := main_cap
  refine ⟨Fintype.piFinset (fun _ => A), ?_, ?_⟩
  · intro x hx y hy z hz hsum
    rw [Fintype.mem_piFinset] at hx hy hz
    have hc : ∀ c, x c + y c + z c = 0 := fun c => by have := congrFun hsum c; simpa using this
    have := fun c => hA (x c) (hx c) (y c) (hy c) (z c) (hz c) (hc c)
    exact ⟨funext fun c => (this c).1, funext fun c => (this c).2⟩
  · rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    push_cast
    rw [pow_mul, pow_mul, ← mul_pow]
    have h0 : (0 : ℝ) ≤ (2220334 : ℝ) ^ 648 := by positivity
    exact pow_lt_pow_left₀ hcard h0 (by omega)


/-! ### the same statement in `F_3^648 = Fin 648 → ZMod 3` -/

noncomputable def idxE : Fin 648 ≃ (Fin 9 × Fin 3) × Fin 4 × Fin 6 :=
  Fintype.equivOfCardEq (by simp)

noncomputable def toFlat (v : Fin 9 × Fin 3 → Fin 4 → Fin 6 → ZMod 3) : Fin 648 → ZMod 3 :=
  fun j => v (idxE j).1 (idxE j).2.1 (idxE j).2.2

lemma toFlat_injective : Function.Injective toFlat := by
  intro v w h
  funext p a b
  have := congrFun h (idxE.symm (p, a, b))
  simpa [toFlat] using this

lemma toFlat_add (v w : Fin 9 × Fin 3 → Fin 4 → Fin 6 → ZMod 3) : toFlat (v + w) = toFlat v + toFlat w := rfl

lemma toFlat_zero : toFlat 0 = 0 := rfl

/-- **Main theorem, flat form.**  There is a cap set in `F_3^648` of size `> (2220334/1000000)^648`. -/
theorem main_cap_648 : ∃ A : Finset (Fin 648 → ZMod 3),
    IsCap A ∧ (2220334 : ℝ) ^ 648 < (A.card : ℝ) * (1000000 : ℝ) ^ 648 := by
  obtain ⟨A, hA, hcard⟩ := main_cap
  refine ⟨A.map ⟨toFlat, toFlat_injective⟩, ?_, ?_⟩
  · intro x hx y hy z hz hsum
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx hy hz
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨z', hz', rfl⟩ := hz
    have h0 : x' + y' + z' = 0 := by
      apply toFlat_injective
      rw [toFlat_add, toFlat_add, toFlat_zero]; exact hsum
    obtain ⟨h1, h2⟩ := hA x' hx' y' hy' z' hz' h0
    exact ⟨by rw [h1], by rw [h2]⟩
  · rw [Finset.card_map]; exact hcard

#print axioms admissible_new
#print axioms main_cap
#print axioms main_capacity
#print axioms main_cap_648

end CapB05
