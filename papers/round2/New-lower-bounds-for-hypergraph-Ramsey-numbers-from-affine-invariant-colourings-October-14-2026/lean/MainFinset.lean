import Mathlib

/-! Finset-form restatements (with Mathlib) of R(4,5;3) ≥ 38 and R(5,5;3) ≥ 98; the colourings and kernel checks are the same as in Main.lean. -/
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace R453

/-- `Fmask` encodes the colour of the triples `{0, d₁, d₂}` (0 < d₁ < d₂ < 37): bit `d₁*37+d₂` (1 = red). -/
def Fmask : Nat := 0x40000000030000000004000000001000000001a00000002000000000b200000006c80000001c20000003300000000116000000e4c0000006178000001b428000001d28000004501800004d4ce000038a4e00000e8b0400008a8b40000104a26000096aa380015740e4000500d9a8004c103c400275bc0000102833ec00015a40f804ab92260007cd258c00d4050e6805328dc04821aeb081e188b1a5d00000000000

/-- The colouring of the triple `x < y < z` of `{0,…,36}`: the colour of `{0, y-x, z-x}`
(true = red). It is translation invariant by construction. -/
def col (x y z : Nat) : Bool := Fmask.testBit ((y - x) * 37 + (z - x))

/-- pruned search: no red `K_4^(3)` containing the vertex 0 -/
def chkRed : Bool :=
  (List.range 37).all fun v1 => v1 == 0 || ((List.range 37).all fun v2 => !(v1 < v2 && col 0 v1 v2) || ((List.range 37).all fun v3 => !(v2 < v3 && col 0 v1 v3 && col 0 v2 v3 && col v1 v2 v3)))

/-- pruned search: no blue `K_5^(3)` containing the vertex 0 -/
def chkBlue : Bool :=
  (List.range 37).all fun v1 => v1 == 0 || ((List.range 37).all fun v2 => !(v1 < v2 && !(col 0 v1 v2)) || ((List.range 37).all fun v3 => !(v2 < v3 && !(col 0 v1 v3) && !(col 0 v2 v3) && !(col v1 v2 v3)) || ((List.range 37).all fun v4 => !(v3 < v4 && !(col 0 v1 v4) && !(col 0 v2 v4) && !(col 0 v3 v4) && !(col v1 v2 v4) && !(col v1 v3 v4) && !(col v2 v3 v4)))))

theorem chkRed_ok : chkRed = true := by decide +kernel
theorem chkBlue_ok : chkBlue = true := by decide +kernel

end R453
namespace R453

theorem noRed0 (x1 x2 x3 : Nat) (h1 : 0 < x1) (h2 : x1 < x2) (h3 : x2 < x3) (hn : x3 < 37)
    (r0 : col 0 x1 x2 = true) (r1 : col 0 x1 x3 = true) (r2 : col 0 x2 x3 = true) (r3 : col x1 x2 x3 = true) : False := by
  have hc := chkRed_ok
  unfold chkRed at hc
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at hc
  rcases hc x1 (by omega) with h | h
  · omega
  rcases h x2 (by omega) with h | h
  · simp_all
  rcases h x3 (by omega) with h | h
  all_goals simp_all

theorem noBlue0 (x1 x2 x3 x4 : Nat) (h1 : 0 < x1) (h2 : x1 < x2) (h3 : x2 < x3) (h4 : x3 < x4) (hn : x4 < 37)
    (r0 : col 0 x1 x2 = false) (r1 : col 0 x1 x3 = false) (r2 : col 0 x1 x4 = false) (r3 : col 0 x2 x3 = false) (r4 : col 0 x2 x4 = false) (r5 : col 0 x3 x4 = false) (r6 : col x1 x2 x3 = false) (r7 : col x1 x2 x4 = false) (r8 : col x1 x3 x4 = false) (r9 : col x2 x3 x4 = false) : False := by
  have hc := chkBlue_ok
  unfold chkBlue at hc
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at hc
  rcases hc x1 (by omega) with h | h
  · omega
  rcases h x2 (by omega) with h | h
  · simp_all
  rcases h x3 (by omega) with h | h
  · simp_all
  rcases h x4 (by omega) with h | h
  all_goals simp_all

/-- translation: the colour of `x<y<z` only depends on `y-x, z-x` -/
theorem col_shift (a x y z : Nat) (hx : a ≤ x) (hxy : x < y) (hyz : y < z) :
    col (x - a) (y - a) (z - a) = col x y z := by
  unfold col
  rw [show y - a - (x - a) = y - x by omega, show z - a - (x - a) = z - x by omega]

/-- `col` (a colouring of the triples `x<y<z` of `{0,…,N-1}`) contains a `K_4^(3)` of colour `χ`:
4 vertices all of whose triples have colour `χ`. -/
def HasMonoK4 (N : Nat) (col : Nat → Nat → Nat → Bool) (χ : Bool) : Prop :=
  ∃ a b c d : Nat, a < b ∧ b < c ∧ c < d ∧ d < N ∧ col a b c = χ ∧ col a b d = χ ∧ col a c d = χ ∧ col b c d = χ

/-- `col` (a colouring of the triples `x<y<z` of `{0,…,N-1}`) contains a `K_5^(3)` of colour `χ`:
5 vertices all of whose triples have colour `χ`. -/
def HasMonoK5 (N : Nat) (col : Nat → Nat → Nat → Bool) (χ : Bool) : Prop :=
  ∃ a b c d e : Nat, a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < N ∧ col a b c = χ ∧ col a b d = χ ∧ col a b e = χ ∧ col a c d = χ ∧ col a c e = χ ∧ col a d e = χ ∧ col b c d = χ ∧ col b c e = χ ∧ col b d e = χ ∧ col c d e = χ

theorem noRedK : ¬ HasMonoK4 37 col true := by
  rintro ⟨a, b, c, d, l0, l1, l2, hn, h0, h1, h2, h3⟩
  have s0 := col_shift a a b c (by omega) (by omega) (by omega)
  have s1 := col_shift a a b d (by omega) (by omega) (by omega)
  have s2 := col_shift a a c d (by omega) (by omega) (by omega)
  have s3 := col_shift a b c d (by omega) (by omega) (by omega)
  simp only [Nat.sub_self] at s0 s1 s2 s3
  exact noRed0 (b - a) (c - a) (d - a) (by omega) (by omega) (by omega) (by omega) (by rw [s0, h0]) (by rw [s1, h1]) (by rw [s2, h2]) (by rw [s3, h3])

theorem noBlueK : ¬ HasMonoK5 37 col false := by
  rintro ⟨a, b, c, d, e, l0, l1, l2, l3, hn, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have s0 := col_shift a a b c (by omega) (by omega) (by omega)
  have s1 := col_shift a a b d (by omega) (by omega) (by omega)
  have s2 := col_shift a a b e (by omega) (by omega) (by omega)
  have s3 := col_shift a a c d (by omega) (by omega) (by omega)
  have s4 := col_shift a a c e (by omega) (by omega) (by omega)
  have s5 := col_shift a a d e (by omega) (by omega) (by omega)
  have s6 := col_shift a b c d (by omega) (by omega) (by omega)
  have s7 := col_shift a b c e (by omega) (by omega) (by omega)
  have s8 := col_shift a b d e (by omega) (by omega) (by omega)
  have s9 := col_shift a c d e (by omega) (by omega) (by omega)
  simp only [Nat.sub_self] at s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
  exact noBlue0 (b - a) (c - a) (d - a) (e - a) (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [s0, h0]) (by rw [s1, h1]) (by rw [s2, h2]) (by rw [s3, h3]) (by rw [s4, h4]) (by rw [s5, h5]) (by rw [s6, h6]) (by rw [s7, h7]) (by rw [s8, h8]) (by rw [s9, h9])

/-- **R(4,5;3) ≥ 38**: there is a red/blue colouring of the triples of `{0,…,36}` with no red
`K_4^(3)` and no blue `K_5^(3)`. -/
theorem main : ∃ col : Nat → Nat → Nat → Bool, ¬ HasMonoK4 37 col true ∧ ¬ HasMonoK5 37 col false :=
  ⟨col, noRedK, noBlueK⟩

end R453

namespace R453
open Finset

/-- the colouring as a function on 3-subsets of `Fin 37` (value on sets of other sizes irrelevant) -/
noncomputable def colSet (t : Finset (Fin 37)) : Bool :=
  if h : t.card = 3 then col (t.orderEmbOfFin h 0).val (t.orderEmbOfFin h 1).val (t.orderEmbOfFin h 2).val
  else false

lemma colSet_eq {x y z : Fin 37} (hxy : x < y) (hyz : y < z) : colSet {x, y, z} = col x.val y.val z.val := by
  have hc : ({x, y, z} : Finset (Fin 37)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (ne_of_lt hyz)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ne_of_lt hxy, ne_of_lt (hxy.trans hyz)⟩
  have hg : (![x, y, z] : Fin 3 → Fin 37) = ({x, y, z} : Finset (Fin 37)).orderEmbOfFin hc := by
    apply Finset.orderEmbOfFin_unique hc
    · intro i; fin_cases i <;> simp
    · rw [Fin.strictMono_iff_lt_succ]
      intro i
      fin_cases i
      · simpa using hxy
      · simpa using hyz
  unfold colSet
  rw [dif_pos hc, ← hg]
  rfl

lemma trip_of {k : ℕ} (T : Finset (Fin 37)) (hT : T.card = k) (i j l : Fin k) (hij : i < j) (hjl : j < l) :
    ({T.orderEmbOfFin hT i, T.orderEmbOfFin hT j, T.orderEmbOfFin hT l} : Finset (Fin 37)) ∈ T.powersetCard 3 ∧
    colSet {T.orderEmbOfFin hT i, T.orderEmbOfFin hT j, T.orderEmbOfFin hT l} =
      col (T.orderEmbOfFin hT i).val (T.orderEmbOfFin hT j).val (T.orderEmbOfFin hT l).val := by
  set f := T.orderEmbOfFin hT
  have hm : StrictMono f := f.strictMono
  refine ⟨?_, colSet_eq (hm hij) (hm hjl)⟩
  rw [Finset.mem_powersetCard]
  refine ⟨?_, ?_⟩
  · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> exact Finset.orderEmbOfFin_mem T hT _
  · rw [Finset.card_insert_of_notMem, Finset.card_pair (ne_of_lt (hm hjl))]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ne_of_lt (hm hij), ne_of_lt ((hm hij).trans (hm hjl))⟩

/-- **R(4,5;3) ≥ 38**, in the language of finite sets: a red/blue colouring of the 3-subsets of `Fin 37`
such that every 4-subset contains a blue 3-subset and every 5-subset contains a red 3-subset. -/
theorem main_finset : ∃ c : Finset (Fin 37) → Bool,
    (∀ S : Finset (Fin 37), S.card = 4 → ∃ t ∈ S.powersetCard 3, c t = false) ∧
    (∀ T : Finset (Fin 37), T.card = 5 → ∃ t ∈ T.powersetCard 3, c t = true) := by
  refine ⟨colSet, fun S hS => ?_, fun T hT => ?_⟩
  · by_contra h
    simp only [not_exists, not_and, Bool.not_eq_false] at h
    set f := S.orderEmbOfFin hS
    have hm : StrictMono f := f.strictMono
    have e : ∀ i j l : Fin 4, i < j → j < l → col (f i).val (f j).val (f l).val = true := by
      intro i j l hij hjl
      rw [← (trip_of S hS i j l hij hjl).2]
      exact h _ (trip_of S hS i j l hij hjl).1
    exact noRedK ⟨(f 0).val, (f 1).val, (f 2).val, (f 3).val, hm (by decide), hm (by decide), hm (by decide),
      (f 3).isLt, e 0 1 2 (by decide) (by decide), e 0 1 3 (by decide) (by decide),
      e 0 2 3 (by decide) (by decide), e 1 2 3 (by decide) (by decide)⟩
  · by_contra h
    simp only [not_exists, not_and, Bool.not_eq_true] at h
    set f := T.orderEmbOfFin hT
    have hm : StrictMono f := f.strictMono
    have e : ∀ i j l : Fin 5, i < j → j < l → col (f i).val (f j).val (f l).val = false := by
      intro i j l hij hjl
      rw [← (trip_of T hT i j l hij hjl).2]
      exact h _ (trip_of T hT i j l hij hjl).1
    exact noBlueK ⟨(f 0).val, (f 1).val, (f 2).val, (f 3).val, (f 4).val, hm (by decide), hm (by decide),
      hm (by decide), hm (by decide), (f 4).isLt,
      e 0 1 2 (by decide) (by decide), e 0 1 3 (by decide) (by decide), e 0 1 4 (by decide) (by decide),
      e 0 2 3 (by decide) (by decide), e 0 2 4 (by decide) (by decide), e 0 3 4 (by decide) (by decide),
      e 1 2 3 (by decide) (by decide), e 1 2 4 (by decide) (by decide), e 1 3 4 (by decide) (by decide),
      e 2 3 4 (by decide) (by decide)⟩

end R453

#print axioms R453.main_finset

namespace R553

/-- `Fmask` encodes the colour of the triples `{0, d₁, d₂}` (0 < d₁ < d₂ < 97): bit `d₁*97+d₂` (1 = red). -/
def Fmask : Nat := 0x28000000000000000000000012000000000000000000000000000000000000000000000001800000000000000000000003b800000000000000000000013200000000000000000000004100000000000000000000002040000000000000000000002aa80000000000000000000017fa0000000000000000000002da000000000000000000000500a00000000000000000000171d000000000000000000000f4bc0000000000000000000049490000000000000000000028914000000000000000000026aac80000000000000000001212120000000000000000000b28a6800000000000000000072e74e0000000000000000003bb1bb8000000000000000001cd86ce000000000000000000ef777b8000000000000000001d3fcb8000000000000000000bbefba0000000000000000019e9e5e6000000000000000004e20239000000000000000005e67e67a000000000000000024d60d64800000000000000000a8b4540000000000000000035ce39d6000000000000000072126484e0000000000000000c30c61860000000000000001d343f0b2e0000000000000009bab06aec8000000000000001549e792a8000000000000003afb9b3beb800000000000001be208411f6000000000000004b826320e900000000000000088c76e3110000000000000031c992932718000000000000051c32d30e2800000000000005439d8dce150000000000000273ae4275ce4000000000000159db405b7350000000000000a8f268593c54000000000000563cd0059e350000000000002bef1c038f7d400000000000151fcf6de7f15000000000000ace9f003e5cd400000000000874e37df63970800000000003e72d97e9b4e7c0000000000019f3f5b5f9f30000000000019c2807338050e60000000000d07f98770cff058000000000223e6b2f4d67c440000000002e9f8b0821a3f2e8000000001537f64c0c9bfb2a0000000004f70785dd0f07790000000005d9a1b1998d859ba000000001aebec5a0b46faeb0000000007600ff8cc7fc01b800000000a2919a31462cc4a28000000048e6feec9377f67120000000016cf43d29785e6d000000001e901a2dcced16025e000000054ba049adac902e95000000004b26c0edb70364d200000002be2960b405a0d28fa8000001dac4c02b03500c8d6e000000fe436c0355601b613f8000007760e512a6548a706ee000003ad3d9b1caa71b3796b8000014c2b01bfedff60350ca00000aeee4b05f8fd0693bba800000ba457ee924977ea25d0000015995517a5b4bd15533500000a1f53c1d2492e0f2be1400005bfd2ba89a2c8aea5fed0000706d5c226fff6443ab60e00006b1da2927abc928b71ac0001710e2054ff3fca811c23a000a983a168fedbf8b42e0ca8001387f7a2177ee845efe1c8001e0fc92fa41104be927e0f00198c4939be0481f67248c66008c4afe83e9b6cbe0bfa9188021a07bdc12fff483bde058400cee8bf07e5014fc1fa2ee6015137846a94bf4a55887b22a098f43f93d84010de4fe178c802c3c79853aff5ca19e3c3400ccd0fe596c8026d34fe16660000000000000000000000000

/-- The colouring of the triple `x < y < z` of `{0,…,96}`: the colour of `{0, y-x, z-x}`
(true = red). It is translation invariant by construction. -/
def col (x y z : Nat) : Bool := Fmask.testBit ((y - x) * 97 + (z - x))

/-- pruned search: no red `K_5^(3)` containing the vertex 0 -/
def chkRed : Bool :=
  (List.range 97).all fun v1 => v1 == 0 || ((List.range 97).all fun v2 => !(v1 < v2 && col 0 v1 v2) || ((List.range 97).all fun v3 => !(v2 < v3 && col 0 v1 v3 && col 0 v2 v3 && col v1 v2 v3) || ((List.range 97).all fun v4 => !(v3 < v4 && col 0 v1 v4 && col 0 v2 v4 && col 0 v3 v4 && col v1 v2 v4 && col v1 v3 v4 && col v2 v3 v4))))

/-- pruned search: no blue `K_5^(3)` containing the vertex 0 -/
def chkBlue : Bool :=
  (List.range 97).all fun v1 => v1 == 0 || ((List.range 97).all fun v2 => !(v1 < v2 && !(col 0 v1 v2)) || ((List.range 97).all fun v3 => !(v2 < v3 && !(col 0 v1 v3) && !(col 0 v2 v3) && !(col v1 v2 v3)) || ((List.range 97).all fun v4 => !(v3 < v4 && !(col 0 v1 v4) && !(col 0 v2 v4) && !(col 0 v3 v4) && !(col v1 v2 v4) && !(col v1 v3 v4) && !(col v2 v3 v4)))))

theorem chkRed_ok : chkRed = true := by decide +kernel
theorem chkBlue_ok : chkBlue = true := by decide +kernel

end R553
namespace R553

theorem noRed0 (x1 x2 x3 x4 : Nat) (h1 : 0 < x1) (h2 : x1 < x2) (h3 : x2 < x3) (h4 : x3 < x4) (hn : x4 < 97)
    (r0 : col 0 x1 x2 = true) (r1 : col 0 x1 x3 = true) (r2 : col 0 x1 x4 = true) (r3 : col 0 x2 x3 = true) (r4 : col 0 x2 x4 = true) (r5 : col 0 x3 x4 = true) (r6 : col x1 x2 x3 = true) (r7 : col x1 x2 x4 = true) (r8 : col x1 x3 x4 = true) (r9 : col x2 x3 x4 = true) : False := by
  have hc := chkRed_ok
  unfold chkRed at hc
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at hc
  rcases hc x1 (by omega) with h | h
  · omega
  rcases h x2 (by omega) with h | h
  · simp_all
  rcases h x3 (by omega) with h | h
  · simp_all
  rcases h x4 (by omega) with h | h
  all_goals simp_all

theorem noBlue0 (x1 x2 x3 x4 : Nat) (h1 : 0 < x1) (h2 : x1 < x2) (h3 : x2 < x3) (h4 : x3 < x4) (hn : x4 < 97)
    (r0 : col 0 x1 x2 = false) (r1 : col 0 x1 x3 = false) (r2 : col 0 x1 x4 = false) (r3 : col 0 x2 x3 = false) (r4 : col 0 x2 x4 = false) (r5 : col 0 x3 x4 = false) (r6 : col x1 x2 x3 = false) (r7 : col x1 x2 x4 = false) (r8 : col x1 x3 x4 = false) (r9 : col x2 x3 x4 = false) : False := by
  have hc := chkBlue_ok
  unfold chkBlue at hc
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at hc
  rcases hc x1 (by omega) with h | h
  · omega
  rcases h x2 (by omega) with h | h
  · simp_all
  rcases h x3 (by omega) with h | h
  · simp_all
  rcases h x4 (by omega) with h | h
  all_goals simp_all

/-- translation: the colour of `x<y<z` only depends on `y-x, z-x` -/
theorem col_shift (a x y z : Nat) (hx : a ≤ x) (hxy : x < y) (hyz : y < z) :
    col (x - a) (y - a) (z - a) = col x y z := by
  unfold col
  rw [show y - a - (x - a) = y - x by omega, show z - a - (x - a) = z - x by omega]

/-- `col` (a colouring of the triples `x<y<z` of `{0,…,N-1}`) contains a `K_5^(3)` of colour `χ`:
5 vertices all of whose triples have colour `χ`. -/
def HasMonoK5 (N : Nat) (col : Nat → Nat → Nat → Bool) (χ : Bool) : Prop :=
  ∃ a b c d e : Nat, a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < N ∧ col a b c = χ ∧ col a b d = χ ∧ col a b e = χ ∧ col a c d = χ ∧ col a c e = χ ∧ col a d e = χ ∧ col b c d = χ ∧ col b c e = χ ∧ col b d e = χ ∧ col c d e = χ

theorem noRedK : ¬ HasMonoK5 97 col true := by
  rintro ⟨a, b, c, d, e, l0, l1, l2, l3, hn, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have s0 := col_shift a a b c (by omega) (by omega) (by omega)
  have s1 := col_shift a a b d (by omega) (by omega) (by omega)
  have s2 := col_shift a a b e (by omega) (by omega) (by omega)
  have s3 := col_shift a a c d (by omega) (by omega) (by omega)
  have s4 := col_shift a a c e (by omega) (by omega) (by omega)
  have s5 := col_shift a a d e (by omega) (by omega) (by omega)
  have s6 := col_shift a b c d (by omega) (by omega) (by omega)
  have s7 := col_shift a b c e (by omega) (by omega) (by omega)
  have s8 := col_shift a b d e (by omega) (by omega) (by omega)
  have s9 := col_shift a c d e (by omega) (by omega) (by omega)
  simp only [Nat.sub_self] at s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
  exact noRed0 (b - a) (c - a) (d - a) (e - a) (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [s0, h0]) (by rw [s1, h1]) (by rw [s2, h2]) (by rw [s3, h3]) (by rw [s4, h4]) (by rw [s5, h5]) (by rw [s6, h6]) (by rw [s7, h7]) (by rw [s8, h8]) (by rw [s9, h9])

theorem noBlueK : ¬ HasMonoK5 97 col false := by
  rintro ⟨a, b, c, d, e, l0, l1, l2, l3, hn, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have s0 := col_shift a a b c (by omega) (by omega) (by omega)
  have s1 := col_shift a a b d (by omega) (by omega) (by omega)
  have s2 := col_shift a a b e (by omega) (by omega) (by omega)
  have s3 := col_shift a a c d (by omega) (by omega) (by omega)
  have s4 := col_shift a a c e (by omega) (by omega) (by omega)
  have s5 := col_shift a a d e (by omega) (by omega) (by omega)
  have s6 := col_shift a b c d (by omega) (by omega) (by omega)
  have s7 := col_shift a b c e (by omega) (by omega) (by omega)
  have s8 := col_shift a b d e (by omega) (by omega) (by omega)
  have s9 := col_shift a c d e (by omega) (by omega) (by omega)
  simp only [Nat.sub_self] at s0 s1 s2 s3 s4 s5 s6 s7 s8 s9
  exact noBlue0 (b - a) (c - a) (d - a) (e - a) (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [s0, h0]) (by rw [s1, h1]) (by rw [s2, h2]) (by rw [s3, h3]) (by rw [s4, h4]) (by rw [s5, h5]) (by rw [s6, h6]) (by rw [s7, h7]) (by rw [s8, h8]) (by rw [s9, h9])

/-- **R(5,5;3) ≥ 98**: there is a red/blue colouring of the triples of `{0,…,96}` with no red
`K_5^(3)` and no blue `K_5^(3)`. -/
theorem main : ∃ col : Nat → Nat → Nat → Bool, ¬ HasMonoK5 97 col true ∧ ¬ HasMonoK5 97 col false :=
  ⟨col, noRedK, noBlueK⟩

end R553

namespace R553
open Finset

/-- the colouring as a function on 3-subsets of `Fin 97` (value on sets of other sizes irrelevant) -/
noncomputable def colSet (t : Finset (Fin 97)) : Bool :=
  if h : t.card = 3 then col (t.orderEmbOfFin h 0).val (t.orderEmbOfFin h 1).val (t.orderEmbOfFin h 2).val
  else false

lemma colSet_eq {x y z : Fin 97} (hxy : x < y) (hyz : y < z) : colSet {x, y, z} = col x.val y.val z.val := by
  have hc : ({x, y, z} : Finset (Fin 97)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair (ne_of_lt hyz)]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨ne_of_lt hxy, ne_of_lt (hxy.trans hyz)⟩
  have hg : (![x, y, z] : Fin 3 → Fin 97) = ({x, y, z} : Finset (Fin 97)).orderEmbOfFin hc := by
    apply Finset.orderEmbOfFin_unique hc
    · intro i; fin_cases i <;> simp
    · rw [Fin.strictMono_iff_lt_succ]
      intro i
      fin_cases i
      · simpa using hxy
      · simpa using hyz
  unfold colSet
  rw [dif_pos hc, ← hg]
  rfl

/-- **R(5,5;3) ≥ 97+1**, in the language of finite sets: a red/blue colouring of the 3-subsets of
`Fin 97` such that every 5-subset contains a red and a blue 3-subset. -/
theorem main_finset : ∃ c : Finset (Fin 97) → Bool, ∀ T : Finset (Fin 97), T.card = 5 →
    (∃ t ∈ T.powersetCard 3, c t = true) ∧ (∃ t ∈ T.powersetCard 3, c t = false) := by
  refine ⟨colSet, fun T hT => ?_⟩
  set f := T.orderEmbOfFin hT
  have hm : StrictMono f := f.strictMono
  have mem : ∀ i, f i ∈ T := fun i => Finset.orderEmbOfFin_mem T hT i
  have trip : ∀ i j k : Fin 5, i < j → j < k → ({f i, f j, f k} : Finset (Fin 97)) ∈ T.powersetCard 3 ∧
      colSet {f i, f j, f k} = col (f i).val (f j).val (f k).val := by
    intro i j k hij hjk
    refine ⟨?_, colSet_eq (hm hij) (hm hjk)⟩
    rw [Finset.mem_powersetCard]
    refine ⟨?_, ?_⟩
    · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> exact mem _
    · rw [Finset.card_insert_of_notMem, Finset.card_pair (ne_of_lt (hm hjk))]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ne_of_lt (hm hij), ne_of_lt ((hm hij).trans (hm hjk))⟩
  have lt : ∀ i j : Fin 5, i < j → (f i).val < (f j).val := fun i j h => hm h
  have bound : (f 4).val < 97 := (f 4).isLt
  -- if every triple of T had colour χ we would get a monochromatic K₅
  have key : ∀ χ : Bool, (∀ t ∈ T.powersetCard 3, colSet t = χ) → HasMonoK5 97 col χ := by
    intro χ hall
    have e : ∀ i j k : Fin 5, i < j → j < k → col (f i).val (f j).val (f k).val = χ := by
      intro i j k hij hjk
      rw [← (trip i j k hij hjk).2]
      exact hall _ (trip i j k hij hjk).1
    exact ⟨(f 0).val, (f 1).val, (f 2).val, (f 3).val, (f 4).val, lt 0 1 (by decide), lt 1 2 (by decide),
      lt 2 3 (by decide), lt 3 4 (by decide), bound,
      e 0 1 2 (by decide) (by decide), e 0 1 3 (by decide) (by decide), e 0 1 4 (by decide) (by decide),
      e 0 2 3 (by decide) (by decide), e 0 2 4 (by decide) (by decide), e 0 3 4 (by decide) (by decide),
      e 1 2 3 (by decide) (by decide), e 1 2 4 (by decide) (by decide), e 1 3 4 (by decide) (by decide),
      e 2 3 4 (by decide) (by decide)⟩
  constructor
  · by_contra h
    simp only [not_exists, not_and, Bool.not_eq_true] at h
    exact noBlueK (key false h)
  · by_contra h
    simp only [not_exists, not_and, Bool.not_eq_false] at h
    exact noRedK (key true h)

end R553

#print axioms R553.main_finset
#print axioms R453.main
#print axioms R553.main
