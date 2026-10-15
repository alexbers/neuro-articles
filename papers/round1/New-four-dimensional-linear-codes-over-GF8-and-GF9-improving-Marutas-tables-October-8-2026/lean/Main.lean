/-!
# A06: new linear codes improving Maruta's tables of `n_q(4,d)`  (q = 8, 9)

Self-contained Lean 4 (core only, no Mathlib).

For each field `GF(q)` (namespace `Q<q>`), `IsCode L n d` says: the explicit list `L` of `n` vectors of
`GF(q)^4` (the columns of a `4 × n` generator matrix) is such that every nonzero message
`u ∈ GF(q)^4` yields a codeword `(u · c)_{c ∈ L}` of Hamming weight at least `d`; i.e. the row space is a
linear `[n, 4, ≥ d]_q` code (of dimension exactly 4).  The fields are realised as
`GF(9) = F₃[i]/(i²+1)` and `GF(8) = F₂[x]/(x³+x+1)` (and `GF(7) = Fin 7` if present); the theorems
`GF<q>_is_field` check the field axioms.  The main theorems `Q<q>.main<q>` list the new `(n, d)` pairs.
-/

-- elaborate declarations sequentially (keeps the number of threads, hence address space, small)
set_option Elab.async false

namespace Q8


/-! ## 1. The field GF(8) = F₂[x]/(x³ + x + 1) -/

/-- `⟨c₀, c₁, c₂⟩ : GF8` is the element `c₀ + c₁ x + c₂ x²` of `F₂[x]/(x³ + x + 1)`. -/
structure GF8 where
  c0 : Bool
  c1 : Bool
  c2 : Bool
deriving DecidableEq, Repr

namespace GF8
instance : OfNat GF8 0 := ⟨⟨false, false, false⟩⟩
instance : OfNat GF8 1 := ⟨⟨true, false, false⟩⟩
instance : Add GF8 := ⟨fun a b => ⟨a.c0 ^^ b.c0, a.c1 ^^ b.c1, a.c2 ^^ b.c2⟩⟩
/-- polynomial product reduced with `x³ = x + 1`, `x⁴ = x² + x` -/
instance : Mul GF8 := ⟨fun a b =>
  let d0 := a.c0 && b.c0
  let d1 := (a.c0 && b.c1) ^^ (a.c1 && b.c0)
  let d2 := (a.c0 && b.c2) ^^ (a.c1 && b.c1) ^^ (a.c2 && b.c0)
  let d3 := (a.c1 && b.c2) ^^ (a.c2 && b.c1)
  let d4 := a.c2 && b.c2
  ⟨d0 ^^ d3, d1 ^^ d3 ^^ d4, d2 ^^ d4⟩⟩
/-- inverse `a⁻¹ = a⁶` (the multiplicative group has order 7) -/
def inv (a : GF8) : GF8 := a * a * a * a * a * a
instance decForall (P : GF8 → Prop) [DecidablePred P] : Decidable (∀ x, P x) :=
  decidable_of_iff (∀ a b c : Bool, P ⟨a, b, c⟩) ⟨fun h x => h x.c0 x.c1 x.c2, fun h a b c => h ⟨a, b, c⟩⟩
end GF8

/-- Sanity check: `GF8` is a field with 8 elements (all axioms verified exhaustively;
in characteristic 2 every element is its own additive inverse). -/
theorem GF8_is_field :
    (∀ x y z : GF8, (x + y) + z = x + (y + z)) ∧ (∀ x y : GF8, x + y = y + x) ∧
    (∀ x : GF8, x + 0 = x) ∧ (∀ x : GF8, x + x = 0) ∧
    (∀ x y z : GF8, (x * y) * z = x * (y * z)) ∧ (∀ x y : GF8, x * y = y * x) ∧
    (∀ x : GF8, x * 1 = x) ∧ (∀ x y z : GF8, x * (y + z) = x * y + x * z) ∧ (1 : GF8) ≠ 0 ∧
    (∀ x : GF8, x ≠ 0 → ∃ y, x * y = 1) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, fun x hx => ⟨GF8.inv x, ?_⟩⟩
  have h : ∀ x : GF8, x ≠ 0 → x * GF8.inv x = 1 := by decide
  exact h x hx

/-! ## 2. Codes -/

/-- vectors of GF(8)^4 (messages and generator-matrix columns) -/
abbrev Vec4 := GF8 × GF8 × GF8 × GF8

/-- `u · c` -/
def dot (u c : Vec4) : GF8 := u.1 * c.1 + u.2.1 * c.2.1 + u.2.2.1 * c.2.2.1 + u.2.2.2 * c.2.2.2

/-- the codeword `u G` of message `u`, where the generator matrix `G` has the columns `L` -/
def codeword (L : List Vec4) (u : Vec4) : List GF8 := L.map (dot u)

/-- Hamming weight -/
def wt (v : List GF8) : Nat := v.countP (fun x => decide (x ≠ 0))

/-- `IsCode L n d`: the 4 × n matrix with columns `L` generates a linear `[n, 4, ≥ d]` code over GF(8):
it has `n` columns and every nonzero message gives a codeword of weight `≥ d`
(in particular `u ↦ u G` is injective, so the code has dimension exactly 4). -/
def IsCode (L : List Vec4) (n d : Nat) : Prop :=
  L.length = n ∧ ∀ u : Vec4, u ≠ (0, 0, 0, 0) → d ≤ wt (codeword L u)

/-- digit `0..7` ↦ GF(8) element with coefficient bits of `d` -/
def ofDigit (d : Nat) : GF8 := ⟨d % 2 == 1, d / 2 % 2 == 1, d / 4 % 2 == 1⟩

/-- column encoded in base 8 as `d₀ + 8 d₁ + 64 d₂ + 512 d₃` ↦ `(d₀, d₁, d₂, d₃)` -/
def ofCode (m : Nat) : Vec4 := (ofDigit (m % 8), ofDigit (m / 8 % 8), ofDigit (m / 64 % 8), ofDigit (m / 512 % 8))

/-! ## 3. Bit-sliced evaluation (proof machinery) -/

/-- a GF(8)-vector stored as three bit masks (bit `c` of `pᵢ` = coefficient of `xⁱ` in coordinate `c`) -/
structure V8 where
  p0 : Nat
  p1 : Nat
  p2 : Nat

def V8.get (x : V8) (c : Nat) : GF8 := ⟨x.p0.testBit c, x.p1.testBit c, x.p2.testBit c⟩

def V8.add (x y : V8) : V8 := ⟨x.p0 ^^^ y.p0, x.p1 ^^^ y.p1, x.p2 ^^^ y.p2⟩

def sel (b : Bool) (X : Nat) : Nat := if b then X else 0

theorem testBit_sel (b : Bool) (X c : Nat) : (sel b X).testBit c = (b && X.testBit c) := by
  cases b <;> simp [sel]

def V8.smul (s : GF8) (x : V8) : V8 :=
  ⟨sel s.c0 x.p0 ^^^ sel s.c1 x.p2 ^^^ sel s.c2 x.p1,
   sel s.c0 x.p1 ^^^ sel s.c1 x.p0 ^^^ sel s.c1 x.p2 ^^^ sel s.c2 x.p1 ^^^ sel s.c2 x.p2,
   sel s.c0 x.p2 ^^^ sel s.c1 x.p1 ^^^ sel s.c2 x.p0 ^^^ sel s.c2 x.p2⟩

theorem V8.add_spec (x y : V8) (c : Nat) : (x.add y).get c = x.get c + y.get c := by
  simp only [V8.add, V8.get, Nat.testBit_xor]; rfl

theorem smul_bool : ∀ s0 s1 s2 a b e : Bool,
    (⟨(s0 && a) ^^ (s1 && e) ^^ (s2 && b),
      (s0 && b) ^^ (s1 && a) ^^ (s1 && e) ^^ (s2 && b) ^^ (s2 && e),
      (s0 && e) ^^ (s1 && b) ^^ (s2 && a) ^^ (s2 && e)⟩ : GF8) = ⟨s0, s1, s2⟩ * ⟨a, b, e⟩ := by decide

theorem V8.smul_spec (s : GF8) (x : V8) (c : Nat) : (x.smul s).get c = s * x.get c := by
  simp only [V8.smul, V8.get, Nat.testBit_xor, testBit_sel]
  exact smul_bool _ _ _ _ _ _

/-- bit-sliced form of a coordinate bit along a list of columns (column `c` ↦ bit `c`) -/
def mkb (f : Vec4 → Bool) : List Vec4 → Nat
  | [] => 0
  | p :: ps => 2 * mkb f ps + (if f p then 1 else 0)

theorem mkb_spec (f : Vec4 → Bool) (L : List Vec4) (c : Nat) (hc : c < L.length) :
    (mkb f L).testBit c = f L[c] := by
  induction L generalizing c with
  | nil => simp at hc
  | cons p ps ih =>
    cases c with
    | zero =>
      simp only [mkb, Nat.testBit_zero, List.getElem_cons_zero]
      cases f p <;> simp <;> omega
    | succ c =>
      have hc' : c < ps.length := by simp at hc; omega
      have e1 : (2 * mkb f ps + (if f p then 1 else 0)) / 2 = mkb f ps := by split <;> omega
      simp only [mkb, Nat.testBit_succ, e1, List.getElem_cons_succ]
      exact ih c hc'

def mk8 (f : Vec4 → GF8) (L : List Vec4) : V8 :=
  ⟨mkb (fun p => (f p).c0) L, mkb (fun p => (f p).c1) L, mkb (fun p => (f p).c2) L⟩

theorem mk8_spec (f : Vec4 → GF8) (L : List Vec4) (c : Nat) (hc : c < L.length) :
    (mk8 f L).get c = f L[c] := by
  simp only [mk8, V8.get, mkb_spec _ L c hc]

/-- the four rows of the generator matrix with columns `L`, bit-sliced -/
def rows (L : List Vec4) : V8 × V8 × V8 × V8 :=
  (mk8 (fun p => p.1) L, mk8 (fun p => p.2.1) L, mk8 (fun p => p.2.2.1) L, mk8 (fun p => p.2.2.2) L)

/-- bit-sliced codeword -/
def cwOf (R : V8 × V8 × V8 × V8) (u : Vec4) : V8 :=
  (((R.1.smul u.1).add (R.2.1.smul u.2.1)).add (R.2.2.1.smul u.2.2.1)).add (R.2.2.2.smul u.2.2.2)

theorem cw_spec (L : List Vec4) (u : Vec4) (c : Nat) (hc : c < L.length) :
    (cwOf (rows L) u).get c = dot u L[c] := by
  simp only [cwOf, rows, V8.add_spec, V8.smul_spec, mk8_spec _ L c hc, dot]

/-- support mask of a bit-sliced GF(8) vector -/
def nz (x : V8) : Nat := x.p0 ||| x.p1 ||| x.p2

theorem nz_bool : ∀ a b e : Bool, (a || b || e) = decide ((⟨a, b, e⟩ : GF8) ≠ 0) := by decide

theorem nz_spec (x : V8) (c : Nat) : (nz x).testBit c = decide (x.get c ≠ 0) := by
  simp only [nz, V8.get, Nat.testBit_or]
  exact nz_bool _ _ _

/-- number of set bits among the lowest `m` bits -/
def pc : Nat → Nat → Nat
  | _, 0 => 0
  | x, m + 1 => x % 2 + pc (x / 2) m

theorem countP_eq_pc {α : Type} (p : α → Bool) (L : List α) (X : Nat)
    (h : ∀ c (hc : c < L.length), X.testBit c = p L[c]) : L.countP p = pc X L.length := by
  induction L generalizing X with
  | nil => rfl
  | cons a L ih =>
    have h0 := h 0 (by simp)
    have ht : ∀ c (hc : c < L.length), (X / 2).testBit c = p L[c] := by
      intro c hc
      rw [Nat.testBit_div_two]
      exact h (c + 1) (by simp; omega)
    rw [List.countP_cons, ih (X / 2) ht]
    simp only [List.length_cons, pc]
    simp only [Nat.testBit_zero, List.getElem_cons_zero] at h0
    cases hp : p a <;> rw [hp] at h0 <;> simp at h0 <;> simp <;> omega

theorem wt_eq (L : List Vec4) (u : Vec4) : wt (codeword L u) = pc (nz (cwOf (rows L) u)) L.length := by
  have := countP_eq_pc (fun x : GF8 => decide (x ≠ 0)) (codeword L u) (nz (cwOf (rows L) u)) (by
    intro c hc
    have hc' : c < L.length := by simpa [codeword] using hc
    rw [nz_spec, cw_spec L u c hc']
    simp [codeword])
  simpa [wt, codeword] using this

/-! ## 4. The finite check -/

/-- the check performed for one message (bit-sliced rows `R` precomputed) -/
def checkR (R : V8 × V8 × V8 × V8) (n d : Nat) (u : Vec4) : Bool := decide (d ≤ pc (nz (cwOf R u)) n)

/-- all 8 elements of GF(8) -/
def allGF8 : List GF8 := [⟨false, false, false⟩, ⟨true, false, false⟩, ⟨false, true, false⟩,
  ⟨true, true, false⟩, ⟨false, false, true⟩, ⟨true, false, true⟩, ⟨false, true, true⟩, ⟨true, true, true⟩]

theorem mem_allGF8 : ∀ x : GF8, x ∈ allGF8 := by decide

/-- the (8^4-1)/(8-1) = 585 normalised nonzero messages (first nonzero coordinate equal to 1) -/
def projMsgs : List Vec4 :=
  (allGF8.flatMap fun b => allGF8.flatMap fun c => allGF8.map fun d => ((1 : GF8), b, c, d)) ++
  (allGF8.flatMap fun c => allGF8.map fun d => ((0 : GF8), (1 : GF8), c, d)) ++
  (allGF8.map fun d => ((0 : GF8), (0 : GF8), (1 : GF8), d)) ++ [((0 : GF8), (0 : GF8), (0 : GF8), (1 : GF8))]

/-- Boolean certificate: all normalised messages give weight `≥ d` -/
def certify (L : List Vec4) (n d : Nat) : Bool :=
  L.length == n && (let R := rows L; projMsgs.all (checkR R n d))

/-! ## 5. Soundness of the check (projective reduction) -/

def smul4 (s : GF8) (u : Vec4) : Vec4 := (s * u.1, s * u.2.1, s * u.2.2.1, s * u.2.2.2)

theorem gf8_distrib : ∀ x y z : GF8, x * (y + z) = x * y + x * z := by decide
theorem gf8_assoc : ∀ x y z : GF8, (x * y) * z = x * (y * z) := by decide
theorem gf8_nz : ∀ s x : GF8, s ≠ 0 → (s * x ≠ 0 ↔ x ≠ 0) := by decide
theorem gf8_inv : ∀ x : GF8, x ≠ 0 → GF8.inv x * x = 1 := by decide
theorem gf8_inv_nz : ∀ x : GF8, x ≠ 0 → GF8.inv x ≠ 0 := by decide
theorem gf8_zero_mul : ∀ x : GF8, x * 0 = 0 := by decide

theorem dot_smul (s : GF8) (u c : Vec4) : dot (smul4 s u) c = s * dot u c := by
  simp only [dot, smul4, gf8_distrib, gf8_assoc]

theorem wt_smul (L : List Vec4) (s : GF8) (hs : s ≠ 0) (u : Vec4) :
    wt (codeword L (smul4 s u)) = wt (codeword L u) := by
  unfold wt codeword
  rw [List.countP_map, List.countP_map]
  apply List.countP_congr
  intro x _
  simp only [Function.comp, dot_smul, decide_eq_true_eq]
  exact gf8_nz s _ hs

theorem isCode_of_certify (L : List Vec4) (n d : Nat) (h : certify L n d = true) : IsCode L n d := by
  simp only [certify, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hlen, hall⟩ := h
  have hall' := List.all_eq_true.mp hall
  have sound : ∀ u ∈ projMsgs, d ≤ wt (codeword L u) := by
    intro u hu
    have := hall' u hu
    rw [wt_eq, hlen]
    simpa [checkR] using this
  have H1 : ∀ b c e : GF8, d ≤ wt (codeword L (1, b, c, e)) := fun b c e => sound _ (by
    simp [projMsgs, List.mem_flatMap, List.mem_map, mem_allGF8])
  have H2 : ∀ c e : GF8, d ≤ wt (codeword L (0, 1, c, e)) := fun c e => sound _ (by
    simp [projMsgs, List.mem_flatMap, List.mem_map, mem_allGF8])
  have H3 : ∀ e : GF8, d ≤ wt (codeword L (0, 0, 1, e)) := fun e => sound _ (by
    simp [projMsgs, List.mem_flatMap, List.mem_map, mem_allGF8])
  have H4 : d ≤ wt (codeword L (0, 0, 0, 1)) := sound _ (by
    simp [projMsgs, List.mem_flatMap, List.mem_map, mem_allGF8])
  refine ⟨hlen, ?_⟩
  intro u hu
  obtain ⟨u1, u2, u3, u4⟩ := u
  by_cases h1 : u1 = 0
  · subst h1
    by_cases h2 : u2 = 0
    · subst h2
      by_cases h3 : u3 = 0
      · subst h3
        have h4 : u4 ≠ 0 := fun h => hu (by rw [h])
        rw [← wt_smul L (GF8.inv u4) (gf8_inv_nz u4 h4)]
        simpa [smul4, gf8_zero_mul, gf8_inv u4 h4] using H4
      · rw [← wt_smul L (GF8.inv u3) (gf8_inv_nz u3 h3)]
        simpa [smul4, gf8_zero_mul, gf8_inv u3 h3] using H3 (GF8.inv u3 * u4)
    · rw [← wt_smul L (GF8.inv u2) (gf8_inv_nz u2 h2)]
      simpa [smul4, gf8_zero_mul, gf8_inv u2 h2] using H2 (GF8.inv u2 * u3) (GF8.inv u2 * u4)
  · rw [← wt_smul L (GF8.inv u1) (gf8_inv_nz u1 h1)]
    simpa [smul4, gf8_inv u1 h1] using H1 (GF8.inv u1 * u2) (GF8.inv u1 * u3) (GF8.inv u1 * u4)

/-! ### Puncturing -/

theorem countP_drop_ge {α : Type} (p : α → Bool) (l : List α) (t : Nat) :
    l.countP p ≤ (l.drop t).countP p + t := by
  have h := List.take_append_drop t l
  have h1 : l.countP p = (l.take t).countP p + (l.drop t).countP p := by
    conv => lhs; rw [← h]
    rw [List.countP_append]
  have h2 : (l.take t).countP p ≤ t := by
    have := List.countP_le_length (p := p) (l := l.take t)
    have := List.length_take_le t l
    omega
  omega

/-- Puncturing: deleting the first `t` columns of an `[n, 4, ≥ d]` code gives an
`[n - t, 4, ≥ d - t]` code (for `t < d` this is again a 4-dimensional code). -/
theorem isCode_drop (L : List Vec4) (n d t : Nat) (h : IsCode L n d) :
    IsCode (L.drop t) (n - t) (d - t) := by
  refine ⟨by simp [h.1], fun u hu => ?_⟩
  have h1 := h.2 u hu
  have h2 := countP_drop_ge (fun x : GF8 => decide (x ≠ 0)) (codeword L u) t
  have h3 : codeword (L.drop t) u = (codeword L u).drop t := by simp [codeword, List.map_drop]
  unfold wt at *
  rw [h3]; omega

/-! ## 6. The new codes -/

/-- generator-matrix columns of the new `[395, 4, 344]_8` code (base-8 codes, see `ofCode`) -/
def C_395_344 : List Vec4 := ([
  1, 25, 33, 41, 57, 64, 73, 81, 97, 113, 121, 136, 137, 145, 161, 169, 177, 185, 193, 200,
  225, 249, 257, 264, 273, 281, 289, 305, 321, 328, 345, 393, 401, 409, 417, 425, 433, 449, 456, 457,
  473, 489, 505, 513, 520, 521, 529, 537, 545, 553, 561, 577, 584, 585, 601, 609, 633, 641, 648, 649,
  657, 665, 673, 697, 705, 712, 713, 729, 745, 753, 761, 776, 777, 801, 809, 825, 833, 840, 841, 857,
  865, 873, 881, 889, 897, 904, 913, 921, 937, 945, 977, 985, 993, 1001, 1017, 1032, 1033, 1041, 1049, 1057,
  1065, 1081, 1088, 1105, 1113, 1121, 1129, 1137, 1160, 1161, 1177, 1193, 1201, 1209, 1217, 1224, 1225, 1233, 1241, 1249,
  1265, 1273, 1281, 1288, 1289, 1305, 1313, 1321, 1329, 1337, 1345, 1353, 1361, 1377, 1385, 1393, 1417, 1449, 1457, 1473,
  1489, 1497, 1505, 1513, 1521, 1553, 1569, 1577, 1585, 1601, 1608, 1617, 1625, 1633, 1641, 1649, 1657, 1665, 1672, 1689,
  1713, 1721, 1729, 1736, 1737, 1753, 1761, 1769, 1777, 1785, 1793, 1800, 1801, 1809, 1817, 1833, 1841, 1857, 1864, 1865,
  1873, 1881, 1889, 1905, 1913, 1921, 1928, 1929, 1937, 1945, 1961, 1985, 1993, 2001, 2017, 2033, 2049, 2056, 2057, 2065,
  2073, 2097, 2105, 2112, 2113, 2121, 2129, 2145, 2177, 2184, 2185, 2193, 2201, 2209, 2217, 2241, 2248, 2249, 2257, 2265,
  2281, 2289, 2329, 2337, 2345, 2353, 2361, 2369, 2385, 2393, 2401, 2409, 2417, 2425, 2433, 2440, 2441, 2457, 2473, 2481,
  2497, 2504, 2513, 2529, 2537, 2545, 2553, 2561, 2568, 2569, 2585, 2593, 2609, 2617, 2624, 2625, 2632, 2633, 2641, 2657,
  2665, 2673, 2681, 2696, 2697, 2705, 2713, 2729, 2737, 2745, 2760, 2777, 2785, 2793, 2809, 2817, 2824, 2825, 2833, 2849,
  2857, 2865, 2873, 2881, 2888, 2889, 2905, 2913, 2921, 2929, 2952, 2953, 2985, 2993, 3009, 3017, 3025, 3033, 3041, 3065,
  3080, 3081, 3105, 3113, 3121, 3129, 3136, 3137, 3144, 3145, 3161, 3169, 3177, 3185, 3201, 3208, 3217, 3225, 3233, 3241,
  3249, 3257, 3273, 3289, 3297, 3305, 3313, 3321, 3329, 3337, 3353, 3361, 3369, 3377, 3393, 3400, 3401, 3409, 3417, 3425,
  3433, 3457, 3465, 3481, 3489, 3505, 3528, 3537, 3545, 3561, 3577, 3585, 3592, 3593, 3601, 3617, 3633, 3641, 3648, 3649,
  3656, 3657, 3665, 3673, 3689, 3705, 3713, 3721, 3745, 3753, 3761, 3777, 3784, 3785, 3793, 3801, 3809, 3833, 3841, 3848,
  3865, 3881, 3889, 3897, 3913, 3921, 3937, 3953, 3969, 3976, 3977, 3985, 4009, 4017, 4040] : List Nat).map ofCode

theorem C_395_344_cert : certify C_395_344 395 344 = true := by decide +kernel

theorem C_395_344_isCode : IsCode C_395_344 395 344 := isCode_of_certify _ _ _ C_395_344_cert

/-- generator-matrix columns of the new `[422, 4, 368]_8` code (base-8 codes, see `ofCode`) -/
def C_422_368 : List Vec4 := ([
  1, 9, 25, 33, 41, 49, 64, 73, 81, 89, 97, 105, 113, 121, 129, 136, 153, 161, 177, 185,
  200, 233, 241, 257, 264, 265, 273, 281, 289, 297, 305, 313, 321, 329, 337, 345, 353, 361, 377, 385,
  392, 393, 401, 409, 417, 425, 433, 456, 457, 473, 481, 489, 497, 505, 512, 513, 520, 521, 537, 545,
  561, 569, 576, 584, 585, 593, 601, 609, 617, 625, 633, 649, 657, 665, 673, 681, 689, 697, 705, 712,
  713, 721, 729, 737, 745, 753, 769, 776, 785, 793, 801, 809, 825, 840, 897, 904, 905, 913, 929, 937,
  945, 953, 961, 968, 969, 977, 985, 993, 1001, 1009, 1017, 1025, 1032, 1033, 1041, 1049, 1057, 1065, 1081, 1088,
  1089, 1096, 1097, 1113, 1129, 1137, 1145, 1153, 1160, 1177, 1185, 1201, 1209, 1224, 1225, 1233, 1241, 1249, 1257, 1265,
  1273, 1281, 1288, 1289, 1297, 1305, 1313, 1329, 1345, 1353, 1369, 1385, 1393, 1401, 1409, 1416, 1425, 1433, 1441, 1449,
  1457, 1465, 1480, 1481, 1513, 1521, 1529, 1544, 1600, 1608, 1617, 1625, 1633, 1649, 1657, 1665, 1672, 1673, 1681, 1697,
  1705, 1713, 1729, 1736, 1737, 1745, 1753, 1761, 1777, 1785, 1800, 1801, 1809, 1817, 1825, 1841, 1849, 1857, 1864, 1865,
  1881, 1897, 1913, 1928, 1929, 1945, 1953, 1961, 1969, 1985, 1993, 2009, 2017, 2025, 2041, 2049, 2056, 2057, 2065, 2073,
  2105, 2113, 2120, 2129, 2137, 2145, 2161, 2177, 2193, 2201, 2217, 2233, 2241, 2249, 2273, 2289, 2312, 2313, 2329, 2337,
  2345, 2361, 2369, 2376, 2385, 2401, 2409, 2417, 2441, 2457, 2465, 2473, 2481, 2489, 2504, 2513, 2521, 2537, 2545, 2553,
  2569, 2577, 2585, 2593, 2601, 2617, 2625, 2632, 2633, 2641, 2649, 2657, 2665, 2673, 2681, 2689, 2696, 2697, 2705, 2713,
  2729, 2737, 2745, 2753, 2760, 2761, 2769, 2777, 2785, 2793, 2809, 2817, 2824, 2849, 2857, 2873, 2888, 2897, 2913, 2921,
  2929, 2937, 2945, 2952, 2953, 2961, 2969, 2977, 2993, 3016, 3017, 3033, 3041, 3057, 3065, 3080, 3081, 3089, 3097, 3113,
  3121, 3137, 3144, 3153, 3161, 3169, 3177, 3193, 3208, 3209, 3225, 3233, 3241, 3249, 3257, 3265, 3272, 3273, 3281, 3297,
  3305, 3313, 3321, 3329, 3337, 3345, 3369, 3377, 3385, 3393, 3400, 3401, 3417, 3425, 3441, 3449, 3457, 3465, 3497, 3505,
  3513, 3521, 3528, 3529, 3537, 3545, 3553, 3561, 3569, 3585, 3617, 3625, 3633, 3641, 3648, 3656, 3657, 3681, 3689, 3697,
  3720, 3721, 3729, 3737, 3745, 3753, 3761, 3769, 3785, 3793, 3801, 3809, 3817, 3825, 3833, 3841, 3849, 3857, 3865, 3873,
  3881, 3897, 3912, 3913, 3921, 3929, 3937, 3953, 3961, 3969, 3977, 3985, 4009, 4025, 4033, 4040, 4041, 4049, 4057, 4073,
  4081, 4089] : List Nat).map ofCode

theorem C_422_368_cert : certify C_422_368 422 368 = true := by decide +kernel

theorem C_422_368_isCode : IsCode C_422_368 422 368 := isCode_of_certify _ _ _ C_422_368_cert

/-- generator-matrix columns of the new `[431, 4, 376]_8` code (base-8 codes, see `ofCode`) -/
def C_431_376 : List Vec4 := ([
  1, 8, 9, 17, 25, 41, 49, 64, 65, 72, 73, 81, 89, 97, 105, 121, 129, 136, 137, 153,
  169, 177, 185, 193, 200, 201, 209, 217, 225, 241, 257, 264, 281, 289, 297, 305, 321, 328, 337, 345,
  385, 392, 393, 401, 417, 425, 433, 441, 457, 465, 473, 481, 489, 497, 505, 513, 520, 529, 537, 545,
  553, 561, 569, 576, 577, 585, 593, 601, 617, 625, 633, 641, 648, 649, 657, 665, 681, 689, 697, 705,
  712, 713, 721, 737, 753, 776, 777, 793, 801, 825, 833, 840, 841, 857, 865, 889, 897, 905, 913, 929,
  945, 953, 961, 968, 977, 985, 993, 1009, 1017, 1025, 1032, 1033, 1041, 1057, 1065, 1073, 1081, 1088, 1089, 1096,
  1097, 1105, 1113, 1121, 1129, 1137, 1161, 1177, 1201, 1209, 1217, 1224, 1225, 1233, 1241, 1257, 1265, 1273, 1281, 1288,
  1289, 1305, 1313, 1329, 1337, 1345, 1352, 1353, 1361, 1377, 1385, 1401, 1409, 1416, 1417, 1425, 1449, 1457, 1465, 1480,
  1505, 1513, 1521, 1529, 1537, 1544, 1545, 1553, 1561, 1569, 1577, 1593, 1617, 1625, 1633, 1641, 1657, 1665, 1672, 1681,
  1689, 1705, 1713, 1721, 1729, 1736, 1745, 1753, 1761, 1777, 1785, 1793, 1801, 1809, 1817, 1841, 1857, 1865, 1873, 1881,
  1897, 1905, 1913, 1921, 1928, 1929, 1953, 1961, 1969, 1985, 1992, 1993, 2001, 2025, 2033, 2041, 2056, 2057, 2073, 2081,
  2105, 2112, 2113, 2120, 2129, 2137, 2161, 2169, 2177, 2184, 2185, 2193, 2201, 2217, 2225, 2233, 2241, 2248, 2257, 2265,
  2273, 2281, 2289, 2305, 2313, 2321, 2337, 2345, 2353, 2361, 2369, 2376, 2377, 2385, 2393, 2409, 2417, 2440, 2441, 2449,
  2465, 2473, 2481, 2489, 2497, 2504, 2513, 2521, 2537, 2545, 2553, 2561, 2568, 2601, 2617, 2624, 2625, 2632, 2633, 2649,
  2657, 2665, 2689, 2697, 2705, 2713, 2729, 2737, 2745, 2753, 2761, 2769, 2777, 2785, 2809, 2817, 2824, 2825, 2841, 2849,
  2857, 2865, 2873, 2881, 2888, 2889, 2897, 2905, 2913, 2921, 2937, 2953, 2961, 2977, 2985, 3001, 3009, 3016, 3017, 3025,
  3033, 3041, 3049, 3057, 3073, 3080, 3081, 3089, 3097, 3105, 3113, 3136, 3137, 3144, 3161, 3169, 3177, 3185, 3193, 3209,
  3217, 3225, 3249, 3257, 3265, 3272, 3281, 3289, 3305, 3313, 3336, 3337, 3345, 3353, 3361, 3369, 3377, 3385, 3393, 3400,
  3401, 3409, 3433, 3441, 3449, 3457, 3465, 3473, 3489, 3497, 3505, 3513, 3529, 3537, 3545, 3553, 3561, 3585, 3592, 3593,
  3609, 3617, 3625, 3633, 3641, 3648, 3656, 3665, 3673, 3689, 3697, 3705, 3721, 3729, 3737, 3753, 3769, 3777, 3784, 3801,
  3809, 3817, 3825, 3833, 3849, 3865, 3873, 3881, 3889, 3897, 3905, 3912, 3913, 3921, 3929, 3945, 3953, 3961, 3976, 3977,
  3985, 4001, 4017, 4025, 4040, 4041, 4049, 4057, 4065, 4073, 4081] : List Nat).map ofCode

theorem C_431_376_cert : certify C_431_376 431 376 = true := by decide +kernel

theorem C_431_376_isCode : IsCode C_431_376 431 376 := isCode_of_certify _ _ _ C_431_376_cert

/-- generator-matrix columns of the new `[385, 4, 335]_8` code (base-8 codes, see `ofCode`) -/
def C_385_335 : List Vec4 := ([
  1, 8, 9, 17, 25, 41, 57, 64, 72, 73, 81, 113, 121, 136, 145, 161, 169, 177, 185, 193,
  200, 201, 209, 225, 233, 257, 273, 281, 289, 297, 305, 313, 321, 328, 353, 361, 377, 385, 409, 417,
  425, 433, 441, 449, 457, 465, 473, 489, 497, 513, 520, 521, 529, 537, 553, 569, 576, 584, 593, 601,
  609, 625, 633, 648, 649, 657, 673, 681, 689, 705, 712, 713, 721, 737, 745, 753, 761, 769, 776, 801,
  809, 817, 825, 833, 840, 841, 857, 865, 873, 889, 897, 921, 929, 937, 945, 961, 969, 977, 985, 1001,
  1032, 1033, 1041, 1057, 1081, 1088, 1096, 1097, 1113, 1121, 1137, 1145, 1169, 1177, 1185, 1201, 1209, 1217, 1225, 1233,
  1249, 1257, 1281, 1288, 1305, 1321, 1337, 1345, 1352, 1353, 1377, 1393, 1401, 1409, 1433, 1441, 1449, 1457, 1473, 1481,
  1489, 1537, 1544, 1545, 1553, 1569, 1577, 1601, 1608, 1609, 1617, 1625, 1633, 1672, 1673, 1681, 1689, 1697, 1705, 1713,
  1721, 1737, 1745, 1761, 1769, 1777, 1793, 1809, 1817, 1825, 1833, 1841, 1849, 1857, 1864, 1881, 1889, 1897, 1905, 1913,
  1945, 1961, 1969, 1985, 1992, 1993, 2001, 2025, 2033, 2041, 2056, 2057, 2073, 2089, 2105, 2112, 2113, 2120, 2121, 2129,
  2137, 2145, 2169, 2185, 2193, 2201, 2217, 2225, 2233, 2241, 2248, 2249, 2257, 2273, 2281, 2289, 2297, 2305, 2312, 2321,
  2337, 2345, 2361, 2376, 2377, 2393, 2401, 2409, 2417, 2425, 2433, 2441, 2449, 2457, 2465, 2473, 2481, 2497, 2504, 2537,
  2545, 2568, 2569, 2577, 2585, 2593, 2617, 2624, 2625, 2633, 2641, 2673, 2681, 2696, 2697, 2705, 2745, 2753, 2761, 2801,
  2824, 2833, 2841, 2849, 2865, 2873, 2881, 2888, 2889, 2913, 2929, 2937, 2945, 2953, 2969, 2977, 2993, 3009, 3016, 3025,
  3033, 3057, 3065, 3073, 3080, 3081, 3089, 3105, 3113, 3129, 3136, 3137, 3144, 3145, 3153, 3169, 3185, 3208, 3209, 3217,
  3233, 3241, 3249, 3257, 3265, 3272, 3281, 3297, 3305, 3321, 3345, 3361, 3369, 3377, 3385, 3400, 3401, 3417, 3425, 3433,
  3457, 3465, 3473, 3481, 3497, 3505, 3521, 3528, 3529, 3537, 3545, 3561, 3569, 3577, 3585, 3592, 3601, 3609, 3617, 3625,
  3641, 3648, 3649, 3656, 3657, 3665, 3673, 3681, 3697, 3705, 3720, 3721, 3729, 3745, 3753, 3761, 3784, 3785, 3809, 3817,
  3825, 3833, 3841, 3857, 3865, 3889, 3905, 3912, 3913, 3929, 3937, 3953, 3961, 3969, 3977, 4009, 4017, 4033, 4040, 4041,
  4049, 4057, 4073, 4081, 4089] : List Nat).map ofCode

theorem C_385_335_cert : certify C_385_335 385 335 = true := by decide +kernel

theorem C_385_335_isCode : IsCode C_385_335 385 335 := isCode_of_certify _ _ _ C_385_335_cert

/-- generator-matrix columns of the new `[163, 4, 140]_8` code (base-8 codes, see `ofCode`) -/
def C_163_140 : List Vec4 := ([
  1, 9, 41, 81, 97, 105, 121, 129, 137, 145, 169, 193, 209, 241, 257, 328, 361, 377, 385, 457,
  465, 497, 505, 617, 633, 648, 649, 657, 673, 769, 777, 801, 825, 840, 841, 857, 865, 881, 897, 904,
  945, 953, 968, 985, 993, 1009, 1017, 1032, 1033, 1041, 1089, 1121, 1129, 1153, 1160, 1169, 1209, 1225, 1265, 1273,
  1313, 1353, 1361, 1433, 1457, 1480, 1537, 1545, 1569, 1577, 1600, 1601, 1673, 1681, 1729, 1777, 1785, 1793, 1817, 1825,
  1881, 1889, 1905, 1913, 1945, 1961, 1993, 2017, 2041, 2056, 2073, 2081, 2089, 2112, 2113, 2129, 2169, 2217, 2233, 2241,
  2257, 2297, 2345, 2377, 2393, 2425, 2433, 2457, 2473, 2504, 2568, 2577, 2601, 2624, 2721, 2753, 2769, 2777, 2825, 2849,
  2865, 2889, 2921, 2929, 3033, 3041, 3080, 3089, 3105, 3113, 3129, 3208, 3233, 3265, 3281, 3289, 3329, 3337, 3369, 3441,
  3464, 3537, 3545, 3553, 3577, 3593, 3648, 3689, 3697, 3720, 3729, 3753, 3769, 3784, 3801, 3849, 3873, 3889, 3912, 3993,
  4009, 4041, 4081] : List Nat).map ofCode

theorem C_163_140_cert : certify C_163_140 163 140 = true := by decide +kernel

theorem C_163_140_isCode : IsCode C_163_140 163 140 := isCode_of_certify _ _ _ C_163_140_cert

/-- generator-matrix columns of the new `[259, 4, 224]_8` code (base-8 codes, see `ofCode`) -/
def C_259_224 : List Vec4 := ([
  9, 25, 49, 57, 64, 65, 72, 81, 97, 105, 129, 145, 200, 201, 217, 241, 249, 257, 264, 297,
  321, 337, 361, 369, 377, 385, 393, 401, 433, 457, 497, 513, 529, 545, 561, 577, 585, 601, 609, 633,
  641, 648, 649, 721, 737, 745, 761, 776, 801, 833, 841, 849, 857, 881, 905, 913, 921, 945, 968, 969,
  977, 985, 993, 1001, 1017, 1025, 1032, 1033, 1041, 1057, 1065, 1081, 1089, 1097, 1113, 1129, 1137, 1160, 1161, 1169,
  1177, 1185, 1201, 1209, 1224, 1225, 1233, 1249, 1273, 1288, 1289, 1329, 1409, 1416, 1417, 1433, 1449, 1457, 1473, 1489,
  1513, 1544, 1561, 1569, 1585, 1601, 1641, 1665, 1681, 1689, 1721, 1729, 1801, 1833, 1873, 1881, 1905, 1913, 1921, 1937,
  1945, 1953, 1969, 1992, 1993, 2001, 2017, 2025, 2033, 2041, 2049, 2056, 2057, 2065, 2081, 2089, 2097, 2105, 2112, 2121,
  2129, 2137, 2153, 2185, 2225, 2233, 2249, 2257, 2281, 2305, 2312, 2321, 2329, 2337, 2393, 2409, 2417, 2425, 2440, 2441,
  2449, 2457, 2465, 2473, 2489, 2504, 2561, 2568, 2577, 2585, 2624, 2713, 2729, 2737, 2753, 2777, 2785, 2793, 2817, 2824,
  2825, 2849, 2865, 2889, 2913, 2952, 2969, 2977, 2985, 3017, 3025, 3033, 3049, 3089, 3129, 3136, 3145, 3153, 3161, 3177,
  3208, 3249, 3257, 3265, 3272, 3281, 3289, 3297, 3305, 3313, 3329, 3337, 3353, 3361, 3369, 3393, 3401, 3417, 3441, 3457,
  3465, 3473, 3513, 3521, 3528, 3545, 3553, 3577, 3585, 3609, 3673, 3681, 3697, 3713, 3720, 3737, 3745, 3753, 3761, 3777,
  3784, 3793, 3809, 3817, 3833, 3849, 3873, 3881, 3905, 3921, 3961, 3976, 4040, 4041, 4049, 4057, 4065, 4081, 4089] : List Nat).map ofCode

theorem C_259_224_cert : certify C_259_224 259 224 = true := by decide +kernel

theorem C_259_224_isCode : IsCode C_259_224 259 224 := isCode_of_certify _ _ _ C_259_224_cert

/-- generator-matrix columns of the new `[407, 4, 354]_8` code (base-8 codes, see `ofCode`) -/
def C_407_354 : List Vec4 := ([
  1, 25, 33, 41, 49, 57, 65, 72, 73, 81, 89, 97, 113, 121, 129, 145, 153, 161, 177, 200,
  201, 209, 217, 225, 233, 241, 249, 257, 265, 289, 297, 305, 313, 328, 385, 393, 409, 441, 449, 456,
  473, 481, 489, 497, 505, 512, 513, 520, 521, 529, 537, 545, 561, 569, 577, 584, 585, 601, 609, 617,
  625, 633, 649, 657, 665, 673, 681, 689, 697, 705, 721, 729, 737, 745, 753, 769, 777, 785, 793, 817,
  825, 833, 841, 849, 873, 897, 904, 913, 921, 937, 945, 953, 968, 977, 985, 993, 1017, 1025, 1032, 1041,
  1049, 1057, 1065, 1073, 1096, 1097, 1105, 1113, 1121, 1129, 1137, 1145, 1153, 1177, 1185, 1193, 1201, 1217, 1224, 1233,
  1249, 1265, 1281, 1289, 1297, 1313, 1321, 1345, 1352, 1361, 1369, 1377, 1393, 1401, 1409, 1417, 1425, 1441, 1449, 1457,
  1465, 1473, 1480, 1481, 1489, 1497, 1513, 1521, 1529, 1545, 1553, 1569, 1577, 1593, 1601, 1608, 1609, 1617, 1633, 1641,
  1649, 1665, 1672, 1673, 1681, 1697, 1713, 1721, 1729, 1736, 1737, 1761, 1785, 1793, 1800, 1809, 1825, 1833, 1841, 1849,
  1864, 1865, 1873, 1889, 1897, 1913, 1921, 1961, 1969, 1977, 1985, 1993, 2001, 2009, 2017, 2025, 2041, 2065, 2089, 2097,
  2105, 2112, 2113, 2129, 2137, 2161, 2169, 2177, 2184, 2201, 2209, 2217, 2233, 2241, 2257, 2265, 2289, 2297, 2305, 2312,
  2313, 2329, 2337, 2345, 2353, 2361, 2369, 2377, 2385, 2393, 2401, 2417, 2433, 2440, 2441, 2449, 2465, 2473, 2481, 2504,
  2505, 2513, 2521, 2529, 2553, 2561, 2568, 2569, 2577, 2585, 2601, 2609, 2617, 2633, 2641, 2673, 2681, 2696, 2705, 2713,
  2721, 2729, 2737, 2745, 2753, 2760, 2761, 2769, 2777, 2785, 2793, 2809, 2817, 2824, 2825, 2833, 2841, 2849, 2865, 2873,
  2881, 2888, 2905, 2913, 2921, 2937, 2952, 2961, 2969, 2977, 2985, 2993, 3001, 3009, 3017, 3025, 3033, 3041, 3049, 3057,
  3073, 3080, 3089, 3097, 3105, 3129, 3136, 3153, 3161, 3169, 3177, 3185, 3193, 3201, 3217, 3233, 3241, 3249, 3257, 3265,
  3272, 3273, 3281, 3289, 3305, 3321, 3329, 3336, 3337, 3345, 3361, 3369, 3377, 3400, 3401, 3409, 3417, 3425, 3433, 3441,
  3449, 3457, 3464, 3465, 3481, 3489, 3497, 3505, 3513, 3521, 3537, 3553, 3569, 3585, 3592, 3601, 3609, 3617, 3625, 3633,
  3641, 3648, 3649, 3656, 3665, 3673, 3681, 3705, 3713, 3721, 3729, 3737, 3753, 3761, 3769, 3777, 3785, 3793, 3817, 3825,
  3833, 3848, 3873, 3881, 3889, 3897, 3905, 3913, 3921, 3929, 3937, 3945, 3969, 3976, 3977, 3985, 3993, 4001, 4017, 4025,
  4033, 4041, 4057, 4065, 4073, 4081, 4089] : List Nat).map ofCode

theorem C_407_354_cert : certify C_407_354 407 354 = true := by decide +kernel

theorem C_407_354_isCode : IsCode C_407_354 407 354 := isCode_of_certify _ _ _ C_407_354_cert

/-- generator-matrix columns of the new `[397, 4, 345]_8` code (base-8 codes, see `ofCode`) -/
def C_397_345 : List Vec4 := ([
  1, 17, 25, 33, 41, 57, 64, 65, 73, 81, 89, 97, 121, 137, 145, 153, 161, 177, 185, 193,
  209, 241, 249, 257, 264, 273, 289, 297, 305, 313, 321, 328, 329, 345, 353, 361, 369, 385, 393, 401,
  409, 417, 433, 441, 449, 456, 457, 465, 473, 497, 505, 513, 520, 521, 537, 545, 553, 569, 576, 577,
  584, 585, 593, 601, 609, 633, 648, 657, 665, 673, 689, 697, 705, 712, 713, 721, 737, 745, 753, 761,
  776, 785, 793, 809, 817, 825, 840, 841, 865, 873, 881, 889, 897, 905, 913, 921, 937, 961, 968, 969,
  977, 985, 1001, 1009, 1017, 1025, 1032, 1033, 1041, 1049, 1057, 1065, 1081, 1088, 1089, 1097, 1105, 1113, 1121, 1137,
  1145, 1160, 1161, 1169, 1177, 1193, 1201, 1209, 1217, 1224, 1225, 1249, 1257, 1265, 1273, 1288, 1297, 1305, 1313, 1321,
  1329, 1337, 1345, 1353, 1369, 1377, 1385, 1401, 1409, 1417, 1425, 1457, 1480, 1481, 1497, 1513, 1521, 1529, 1544, 1545,
  1553, 1561, 1577, 1593, 1600, 1601, 1608, 1625, 1633, 1649, 1657, 1689, 1697, 1705, 1713, 1721, 1729, 1736, 1737, 1745,
  1761, 1769, 1777, 1785, 1800, 1809, 1833, 1841, 1849, 1857, 1865, 1881, 1889, 1905, 1913, 1921, 1929, 1937, 1953, 1992,
  1993, 2001, 2009, 2049, 2056, 2057, 2065, 2081, 2089, 2105, 2112, 2113, 2120, 2121, 2145, 2161, 2169, 2184, 2185, 2193,
  2209, 2217, 2225, 2248, 2289, 2297, 2313, 2321, 2329, 2337, 2345, 2353, 2361, 2369, 2376, 2377, 2393, 2401, 2409, 2417,
  2433, 2449, 2457, 2465, 2504, 2505, 2513, 2521, 2537, 2545, 2553, 2561, 2568, 2569, 2577, 2585, 2593, 2601, 2617, 2624,
  2625, 2632, 2633, 2649, 2657, 2673, 2705, 2713, 2721, 2729, 2737, 2753, 2760, 2761, 2769, 2785, 2793, 2801, 2809, 2817,
  2824, 2833, 2841, 2849, 2857, 2881, 2888, 2889, 2905, 2913, 2921, 2929, 2945, 2953, 2961, 2969, 2977, 2985, 2993, 3009,
  3016, 3017, 3025, 3033, 3049, 3080, 3081, 3097, 3113, 3136, 3137, 3153, 3161, 3185, 3193, 3208, 3209, 3225, 3233, 3257,
  3272, 3273, 3281, 3297, 3305, 3313, 3321, 3329, 3336, 3345, 3353, 3361, 3369, 3385, 3393, 3400, 3425, 3433, 3441, 3449,
  3457, 3464, 3465, 3473, 3481, 3489, 3505, 3521, 3529, 3545, 3561, 3585, 3592, 3593, 3601, 3617, 3625, 3648, 3665, 3681,
  3697, 3705, 3720, 3721, 3729, 3737, 3745, 3753, 3761, 3769, 3777, 3784, 3793, 3817, 3825, 3833, 3841, 3848, 3865, 3873,
  3881, 3889, 3897, 3905, 3912, 3913, 3929, 3945, 3953, 3969, 3977, 3985, 3993, 4001, 4009, 4017, 4040] : List Nat).map ofCode

theorem C_397_345_cert : certify C_397_345 397 345 = true := by decide +kernel

theorem C_397_345_isCode : IsCode C_397_345 397 345 := isCode_of_certify _ _ _ C_397_345_cert

/-- **Main theorem (q = 8).** For each pair `(n, d)` below a linear `[n, 4, ≥ d]` code over GF(8)
exists. Each of these lengths is strictly smaller than the upper bound on `n_8(4,d)` in Maruta's table
(as of 2026-10-08):
  * `d = 137`: table `159 ≤ n ≤ 161`, new code of length `160`
  * `d = 138`: table `160 ≤ n ≤ 162`, new code of length `161`
  * `d = 139`: table `161 ≤ n ≤ 163`, new code of length `162`
  * `d = 140`: table `162 ≤ n ≤ 164`, new code of length `163`
  * `d = 221`: table `255 ≤ n ≤ 257`, new code of length `256`
  * `d = 222`: table `256 ≤ n ≤ 258`, new code of length `257`
  * `d = 223`: table `257 ≤ n ≤ 259`, new code of length `258`
  * `d = 224`: table `258 ≤ n ≤ 260`, new code of length `259`
  * `d = 329`: table `378 ≤ n ≤ 380`, new code of length `379`
  * `d = 330`: table `379 ≤ n ≤ 381`, new code of length `380`
  * `d = 331`: table `380 ≤ n ≤ 382`, new code of length `381`
  * `d = 332`: table `381 ≤ n ≤ 383`, new code of length `382`
  * `d = 333`: table `382 ≤ n ≤ 384`, new code of length `383`
  * `d = 334`: table `383 ≤ n ≤ 385`, new code of length `384`
  * `d = 335`: table `384 ≤ n ≤ 386`, new code of length `385`
  * `d = 337`: table `388 ≤ n ≤ 389`, new code of length `388` (attains the lower bound: value determined)
  * `d = 338`: table `389 ≤ n ≤ 390`, new code of length `389` (attains the lower bound: value determined)
  * `d = 339`: table `390 ≤ n ≤ 391`, new code of length `390` (attains the lower bound: value determined)
  * `d = 340`: table `391 ≤ n ≤ 392`, new code of length `391` (attains the lower bound: value determined)
  * `d = 341`: table `392 ≤ n ≤ 393`, new code of length `392` (attains the lower bound: value determined)
  * `d = 342`: table `393 ≤ n ≤ 394`, new code of length `393` (attains the lower bound: value determined)
  * `d = 343`: table `394 ≤ n ≤ 395`, new code of length `394` (attains the lower bound: value determined)
  * `d = 344`: table `395 ≤ n ≤ 396`, new code of length `395` (attains the lower bound: value determined)
  * `d = 345`: table `397 ≤ n ≤ 398`, new code of length `397` (attains the lower bound: value determined)
  * `d = 353`: table `406 ≤ n ≤ 407`, new code of length `406` (attains the lower bound: value determined)
  * `d = 354`: table `407 ≤ n ≤ 408`, new code of length `407` (attains the lower bound: value determined)
  * `d = 361`: table `415 ≤ n ≤ 416`, new code of length `415` (attains the lower bound: value determined)
  * `d = 362`: table `416 ≤ n ≤ 417`, new code of length `416` (attains the lower bound: value determined)
  * `d = 363`: table `417 ≤ n ≤ 418`, new code of length `417` (attains the lower bound: value determined)
  * `d = 364`: table `418 ≤ n ≤ 419`, new code of length `418` (attains the lower bound: value determined)
  * `d = 365`: table `419 ≤ n ≤ 420`, new code of length `419` (attains the lower bound: value determined)
  * `d = 366`: table `420 ≤ n ≤ 421`, new code of length `420` (attains the lower bound: value determined)
  * `d = 367`: table `421 ≤ n ≤ 422`, new code of length `421` (attains the lower bound: value determined)
  * `d = 368`: table `422 ≤ n ≤ 423`, new code of length `422` (attains the lower bound: value determined)
  * `d = 369`: table `424 ≤ n ≤ 425`, new code of length `424` (attains the lower bound: value determined)
  * `d = 370`: table `425 ≤ n ≤ 426`, new code of length `425` (attains the lower bound: value determined)
  * `d = 371`: table `426 ≤ n ≤ 427`, new code of length `426` (attains the lower bound: value determined)
  * `d = 372`: table `427 ≤ n ≤ 428`, new code of length `427` (attains the lower bound: value determined)
  * `d = 373`: table `428 ≤ n ≤ 429`, new code of length `428` (attains the lower bound: value determined)
  * `d = 374`: table `429 ≤ n ≤ 430`, new code of length `429` (attains the lower bound: value determined)
  * `d = 375`: table `430 ≤ n ≤ 431`, new code of length `430` (attains the lower bound: value determined)
  * `d = 376`: table `431 ≤ n ≤ 432`, new code of length `431` (attains the lower bound: value determined)
-/
theorem main8 :
    (∃ L : List Vec4, IsCode L 160 137) ∧
    (∃ L : List Vec4, IsCode L 161 138) ∧
    (∃ L : List Vec4, IsCode L 162 139) ∧
    (∃ L : List Vec4, IsCode L 163 140) ∧
    (∃ L : List Vec4, IsCode L 256 221) ∧
    (∃ L : List Vec4, IsCode L 257 222) ∧
    (∃ L : List Vec4, IsCode L 258 223) ∧
    (∃ L : List Vec4, IsCode L 259 224) ∧
    (∃ L : List Vec4, IsCode L 379 329) ∧
    (∃ L : List Vec4, IsCode L 380 330) ∧
    (∃ L : List Vec4, IsCode L 381 331) ∧
    (∃ L : List Vec4, IsCode L 382 332) ∧
    (∃ L : List Vec4, IsCode L 383 333) ∧
    (∃ L : List Vec4, IsCode L 384 334) ∧
    (∃ L : List Vec4, IsCode L 385 335) ∧
    (∃ L : List Vec4, IsCode L 388 337) ∧
    (∃ L : List Vec4, IsCode L 389 338) ∧
    (∃ L : List Vec4, IsCode L 390 339) ∧
    (∃ L : List Vec4, IsCode L 391 340) ∧
    (∃ L : List Vec4, IsCode L 392 341) ∧
    (∃ L : List Vec4, IsCode L 393 342) ∧
    (∃ L : List Vec4, IsCode L 394 343) ∧
    (∃ L : List Vec4, IsCode L 395 344) ∧
    (∃ L : List Vec4, IsCode L 397 345) ∧
    (∃ L : List Vec4, IsCode L 406 353) ∧
    (∃ L : List Vec4, IsCode L 407 354) ∧
    (∃ L : List Vec4, IsCode L 415 361) ∧
    (∃ L : List Vec4, IsCode L 416 362) ∧
    (∃ L : List Vec4, IsCode L 417 363) ∧
    (∃ L : List Vec4, IsCode L 418 364) ∧
    (∃ L : List Vec4, IsCode L 419 365) ∧
    (∃ L : List Vec4, IsCode L 420 366) ∧
    (∃ L : List Vec4, IsCode L 421 367) ∧
    (∃ L : List Vec4, IsCode L 422 368) ∧
    (∃ L : List Vec4, IsCode L 424 369) ∧
    (∃ L : List Vec4, IsCode L 425 370) ∧
    (∃ L : List Vec4, IsCode L 426 371) ∧
    (∃ L : List Vec4, IsCode L 427 372) ∧
    (∃ L : List Vec4, IsCode L 428 373) ∧
    (∃ L : List Vec4, IsCode L 429 374) ∧
    (∃ L : List Vec4, IsCode L 430 375) ∧
    (∃ L : List Vec4, IsCode L 431 376) :=
  ⟨⟨C_163_140.drop 3, isCode_drop _ _ _ 3 C_163_140_isCode⟩,
   ⟨C_163_140.drop 2, isCode_drop _ _ _ 2 C_163_140_isCode⟩,
   ⟨C_163_140.drop 1, isCode_drop _ _ _ 1 C_163_140_isCode⟩,
   ⟨C_163_140, C_163_140_isCode⟩,
   ⟨C_259_224.drop 3, isCode_drop _ _ _ 3 C_259_224_isCode⟩,
   ⟨C_259_224.drop 2, isCode_drop _ _ _ 2 C_259_224_isCode⟩,
   ⟨C_259_224.drop 1, isCode_drop _ _ _ 1 C_259_224_isCode⟩,
   ⟨C_259_224, C_259_224_isCode⟩,
   ⟨C_385_335.drop 6, isCode_drop _ _ _ 6 C_385_335_isCode⟩,
   ⟨C_385_335.drop 5, isCode_drop _ _ _ 5 C_385_335_isCode⟩,
   ⟨C_385_335.drop 4, isCode_drop _ _ _ 4 C_385_335_isCode⟩,
   ⟨C_385_335.drop 3, isCode_drop _ _ _ 3 C_385_335_isCode⟩,
   ⟨C_385_335.drop 2, isCode_drop _ _ _ 2 C_385_335_isCode⟩,
   ⟨C_385_335.drop 1, isCode_drop _ _ _ 1 C_385_335_isCode⟩,
   ⟨C_385_335, C_385_335_isCode⟩,
   ⟨C_395_344.drop 7, isCode_drop _ _ _ 7 C_395_344_isCode⟩,
   ⟨C_395_344.drop 6, isCode_drop _ _ _ 6 C_395_344_isCode⟩,
   ⟨C_395_344.drop 5, isCode_drop _ _ _ 5 C_395_344_isCode⟩,
   ⟨C_395_344.drop 4, isCode_drop _ _ _ 4 C_395_344_isCode⟩,
   ⟨C_395_344.drop 3, isCode_drop _ _ _ 3 C_395_344_isCode⟩,
   ⟨C_395_344.drop 2, isCode_drop _ _ _ 2 C_395_344_isCode⟩,
   ⟨C_395_344.drop 1, isCode_drop _ _ _ 1 C_395_344_isCode⟩,
   ⟨C_395_344, C_395_344_isCode⟩,
   ⟨C_397_345, C_397_345_isCode⟩,
   ⟨C_407_354.drop 1, isCode_drop _ _ _ 1 C_407_354_isCode⟩,
   ⟨C_407_354, C_407_354_isCode⟩,
   ⟨C_422_368.drop 7, isCode_drop _ _ _ 7 C_422_368_isCode⟩,
   ⟨C_422_368.drop 6, isCode_drop _ _ _ 6 C_422_368_isCode⟩,
   ⟨C_422_368.drop 5, isCode_drop _ _ _ 5 C_422_368_isCode⟩,
   ⟨C_422_368.drop 4, isCode_drop _ _ _ 4 C_422_368_isCode⟩,
   ⟨C_422_368.drop 3, isCode_drop _ _ _ 3 C_422_368_isCode⟩,
   ⟨C_422_368.drop 2, isCode_drop _ _ _ 2 C_422_368_isCode⟩,
   ⟨C_422_368.drop 1, isCode_drop _ _ _ 1 C_422_368_isCode⟩,
   ⟨C_422_368, C_422_368_isCode⟩,
   ⟨C_431_376.drop 7, isCode_drop _ _ _ 7 C_431_376_isCode⟩,
   ⟨C_431_376.drop 6, isCode_drop _ _ _ 6 C_431_376_isCode⟩,
   ⟨C_431_376.drop 5, isCode_drop _ _ _ 5 C_431_376_isCode⟩,
   ⟨C_431_376.drop 4, isCode_drop _ _ _ 4 C_431_376_isCode⟩,
   ⟨C_431_376.drop 3, isCode_drop _ _ _ 3 C_431_376_isCode⟩,
   ⟨C_431_376.drop 2, isCode_drop _ _ _ 2 C_431_376_isCode⟩,
   ⟨C_431_376.drop 1, isCode_drop _ _ _ 1 C_431_376_isCode⟩,
   ⟨C_431_376, C_431_376_isCode⟩⟩


end Q8

namespace Q9


/-! ## 1. The field GF(9) = F₃[i], i² = -1 -/

/-- `⟨a, b⟩ : GF9` is the element `a + b·i` of `F₃[i]/(i² + 1)`. -/
structure GF9 where
  re : Fin 3
  im : Fin 3
deriving DecidableEq, Repr

namespace GF9
instance : OfNat GF9 0 := ⟨⟨0, 0⟩⟩
instance : OfNat GF9 1 := ⟨⟨1, 0⟩⟩
instance : Add GF9 := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg GF9 := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Mul GF9 := ⟨fun x y => ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩
/-- inverse: `(a + b i)⁻¹ = (a - b i) · N` where `N = a² + b²` satisfies `N⁻¹ = N` in F₃. -/
def inv (x : GF9) : GF9 := ⟨x.re * (x.re * x.re + x.im * x.im), -x.im * (x.re * x.re + x.im * x.im)⟩
instance decForall (P : GF9 → Prop) [DecidablePred P] : Decidable (∀ x, P x) :=
  decidable_of_iff (∀ a b : Fin 3, P ⟨a, b⟩) ⟨fun h x => h x.re x.im, fun h a b => h ⟨a, b⟩⟩
end GF9

/-- Sanity check: `GF9` is a field with 9 elements (all axioms verified exhaustively). -/
theorem GF9_is_field :
    (∀ x y z : GF9, (x + y) + z = x + (y + z)) ∧ (∀ x y : GF9, x + y = y + x) ∧
    (∀ x : GF9, x + 0 = x) ∧ (∀ x : GF9, x + -x = 0) ∧
    (∀ x y z : GF9, (x * y) * z = x * (y * z)) ∧ (∀ x y : GF9, x * y = y * x) ∧
    (∀ x : GF9, x * 1 = x) ∧ (∀ x y z : GF9, x * (y + z) = x * y + x * z) ∧ (1 : GF9) ≠ 0 ∧
    (∀ x : GF9, x ≠ 0 → ∃ y, x * y = 1) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, fun x hx => ⟨GF9.inv x, ?_⟩⟩
  have h : ∀ x : GF9, x ≠ 0 → x * GF9.inv x = 1 := by decide
  exact h x hx

/-! ## 2. Codes -/

/-- vectors of GF(9)^4 (messages and generator-matrix columns) -/
abbrev Vec4 := GF9 × GF9 × GF9 × GF9

/-- `u · c` -/
def dot (u c : Vec4) : GF9 := u.1 * c.1 + u.2.1 * c.2.1 + u.2.2.1 * c.2.2.1 + u.2.2.2 * c.2.2.2

/-- the codeword `u G` of message `u`, where the generator matrix `G` has the columns `L` -/
def codeword (L : List Vec4) (u : Vec4) : List GF9 := L.map (dot u)

/-- Hamming weight -/
def wt (v : List GF9) : Nat := v.countP (fun x => decide (x ≠ 0))

/-- `IsCode L n d`: the 4 × n matrix with columns `L` generates a linear `[n, 4, ≥ d]` code over GF(9):
it has `n` columns and every nonzero message gives a codeword of weight `≥ d`
(in particular `u ↦ u G` is injective, so the code has dimension exactly 4). -/
def IsCode (L : List Vec4) (n d : Nat) : Prop :=
  L.length = n ∧ ∀ u : Vec4, u ≠ (0, 0, 0, 0) → d ≤ wt (codeword L u)

/-- digit `0..8` ↦ GF(9) element `(d mod 3) + (d div 3)·i` -/
def ofDigit (d : Nat) : GF9 := ⟨⟨d % 3, Nat.mod_lt _ (by decide)⟩, ⟨d / 3 % 3, Nat.mod_lt _ (by decide)⟩⟩

/-- column encoded in base 9 as `d₀ + 9 d₁ + 81 d₂ + 729 d₃` ↦ `(d₀, d₁, d₂, d₃)` -/
def ofCode (m : Nat) : Vec4 := (ofDigit (m % 9), ofDigit (m / 9 % 9), ofDigit (m / 81 % 9), ofDigit (m / 729 % 9))

/-! ## 3. Bit-sliced evaluation (proof machinery) -/

/-- an F₃-vector stored as two bit masks: bit `c` of `a` (resp. `b`) says coordinate `c` is 1 (resp. 2) -/
structure V3 where
  a : Nat
  b : Nat

def dec3 (p q : Bool) : Fin 3 := if p then 1 else if q then 2 else 0
def V3.get (x : V3) (c : Nat) : Fin 3 := dec3 (x.a.testBit c) (x.b.testBit c)
def V3.ok (x : V3) (c : Nat) : Prop := (x.a.testBit c && x.b.testBit c) = false

def V3.add (x y : V3) : V3 :=
  ⟨(x.a ^^^ (x.a &&& (y.a ||| y.b))) ||| (y.a ^^^ (y.a &&& (x.a ||| x.b))) ||| (x.b &&& y.b),
   (x.b ^^^ (x.b &&& (y.a ||| y.b))) ||| (y.b ^^^ (y.b &&& (x.a ||| x.b))) ||| (x.a &&& y.a)⟩

def V3.smul (s : Fin 3) (x : V3) : V3 :=
  if s.val = 0 then ⟨0, 0⟩ else if s.val = 1 then x else ⟨x.b, x.a⟩

theorem V3.add_spec (x y : V3) (c : Nat) (hx : x.ok c) (hy : y.ok c) :
    (x.add y).ok c ∧ (x.add y).get c = x.get c + y.get c := by
  unfold V3.ok at *
  simp only [V3.add, V3.get, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor] at *
  revert hx hy
  cases x.a.testBit c <;> cases x.b.testBit c <;> cases y.a.testBit c <;> cases y.b.testBit c <;> decide

theorem fin3_cases : ∀ s : Fin 3, s = 0 ∨ s = 1 ∨ s = 2 := by decide

theorem V3.smul_spec (s : Fin 3) (x : V3) (c : Nat) (hx : x.ok c) :
    (x.smul s).ok c ∧ (x.smul s).get c = s * x.get c := by
  unfold V3.ok at *
  rcases fin3_cases s with rfl | rfl | rfl
  · have e : x.smul 0 = ⟨0, 0⟩ := rfl
    rw [e]; unfold V3.get; simp only [Nat.zero_testBit]
    generalize x.a.testBit c = p at *; generalize x.b.testBit c = q at *
    revert hx; cases p <;> cases q <;> decide
  · have e : x.smul 1 = x := rfl
    rw [e]; unfold V3.get
    generalize x.a.testBit c = p at *; generalize x.b.testBit c = q at *
    revert hx; cases p <;> cases q <;> decide
  · have e : x.smul 2 = ⟨x.b, x.a⟩ := rfl
    rw [e]; unfold V3.get
    generalize x.a.testBit c = p at *; generalize x.b.testBit c = q at *
    revert hx; cases p <;> cases q <;> decide

structure V9 where
  re : V3
  im : V3

def V9.get (x : V9) (c : Nat) : GF9 := ⟨x.re.get c, x.im.get c⟩
def V9.ok (x : V9) (c : Nat) : Prop := x.re.ok c ∧ x.im.ok c
def V9.add (x y : V9) : V9 := ⟨x.re.add y.re, x.im.add y.im⟩
def V9.smul (s : GF9) (x : V9) : V9 :=
  ⟨(x.re.smul s.re).add (x.im.smul (-s.im)), (x.im.smul s.re).add (x.re.smul s.im)⟩

theorem V9.add_spec (x y : V9) (c : Nat) (hx : x.ok c) (hy : y.ok c) :
    (x.add y).ok c ∧ (x.add y).get c = x.get c + y.get c := by
  obtain ⟨h1, h2⟩ := V3.add_spec x.re y.re c hx.1 hy.1
  obtain ⟨h3, h4⟩ := V3.add_spec x.im y.im c hx.2 hy.2
  refine ⟨⟨h1, h3⟩, ?_⟩
  simp only [V9.get, V9.add, h2, h4]; rfl

theorem fin3_aux : ∀ a b c d : Fin 3, a * c + (-b) * d = a * c - b * d := by decide

theorem V9.smul_spec (s : GF9) (x : V9) (c : Nat) (hx : x.ok c) :
    (x.smul s).ok c ∧ (x.smul s).get c = s * x.get c := by
  obtain ⟨a1, a2⟩ := V3.smul_spec s.re x.re c hx.1
  obtain ⟨b1, b2⟩ := V3.smul_spec (-s.im) x.im c hx.2
  obtain ⟨c1, c2⟩ := V3.smul_spec s.re x.im c hx.2
  obtain ⟨d1, d2⟩ := V3.smul_spec s.im x.re c hx.1
  obtain ⟨e1, e2⟩ := V3.add_spec _ _ c a1 b1
  obtain ⟨f1, f2⟩ := V3.add_spec _ _ c c1 d1
  refine ⟨⟨e1, f1⟩, ?_⟩
  simp only [V9.get, V9.smul, e2, f2, a2, b2, c2, d2, fin3_aux]; rfl

/-- bit-sliced form of a coordinate function along a list of columns (column `c` ↦ bit `c`) -/
def mk3 (f : Vec4 → Fin 3) : List Vec4 → V3
  | [] => ⟨0, 0⟩
  | p :: ps => ⟨2 * (mk3 f ps).a + (if f p = 1 then 1 else 0), 2 * (mk3 f ps).b + (if f p = 2 then 1 else 0)⟩

theorem mk3_spec (f : Vec4 → Fin 3) (L : List Vec4) (c : Nat) (hc : c < L.length) :
    (mk3 f L).ok c ∧ (mk3 f L).get c = f L[c] := by
  induction L generalizing c with
  | nil => simp at hc
  | cons p ps ih =>
    cases c with
    | zero =>
      simp only [mk3, V3.ok, V3.get, Nat.testBit_zero, List.getElem_cons_zero]
      rcases h : f p with ⟨_ | _ | _ | k, hk⟩
      · simp [dec3] <;> omega
      · simp [dec3] <;> omega
      · simp [dec3] <;> omega
      · omega
    | succ c =>
      have hc' : c < ps.length := by simp at hc; omega
      obtain ⟨h1, h2⟩ := ih c hc'
      have e1 : (2 * (mk3 f ps).a + (if f p = 1 then 1 else 0)) / 2 = (mk3 f ps).a := by split <;> omega
      have e2 : (2 * (mk3 f ps).b + (if f p = 2 then 1 else 0)) / 2 = (mk3 f ps).b := by split <;> omega
      simp only [mk3, V3.ok, V3.get, Nat.testBit_succ, e1, e2, List.getElem_cons_succ] at h1 h2 ⊢
      exact ⟨h1, h2⟩

def mk9 (f g : Vec4 → Fin 3) (L : List Vec4) : V9 := ⟨mk3 f L, mk3 g L⟩

theorem mk9_spec (f g : Vec4 → Fin 3) (L : List Vec4) (c : Nat) (hc : c < L.length) :
    (mk9 f g L).ok c ∧ (mk9 f g L).get c = ⟨f L[c], g L[c]⟩ := by
  obtain ⟨a1, a2⟩ := mk3_spec f L c hc
  obtain ⟨b1, b2⟩ := mk3_spec g L c hc
  exact ⟨⟨a1, b1⟩, by simp only [mk9, V9.get, a2, b2]⟩

/-- the four rows of the generator matrix with columns `L`, bit-sliced -/
def rows (L : List Vec4) : V9 × V9 × V9 × V9 :=
  (mk9 (fun p => p.1.re) (fun p => p.1.im) L, mk9 (fun p => p.2.1.re) (fun p => p.2.1.im) L,
   mk9 (fun p => p.2.2.1.re) (fun p => p.2.2.1.im) L, mk9 (fun p => p.2.2.2.re) (fun p => p.2.2.2.im) L)

/-- bit-sliced codeword -/
def cwOf (R : V9 × V9 × V9 × V9) (u : Vec4) : V9 :=
  (((R.1.smul u.1).add (R.2.1.smul u.2.1)).add (R.2.2.1.smul u.2.2.1)).add (R.2.2.2.smul u.2.2.2)

theorem cw_spec (L : List Vec4) (u : Vec4) (c : Nat) (hc : c < L.length) :
    (cwOf (rows L) u).ok c ∧ (cwOf (rows L) u).get c = dot u L[c] := by
  obtain ⟨r0, s0⟩ := mk9_spec (fun p => p.1.re) (fun p => p.1.im) L c hc
  obtain ⟨r1, s1⟩ := mk9_spec (fun p => p.2.1.re) (fun p => p.2.1.im) L c hc
  obtain ⟨r2, s2⟩ := mk9_spec (fun p => p.2.2.1.re) (fun p => p.2.2.1.im) L c hc
  obtain ⟨r3, s3⟩ := mk9_spec (fun p => p.2.2.2.re) (fun p => p.2.2.2.im) L c hc
  obtain ⟨m0, n0⟩ := V9.smul_spec u.1 _ c r0
  obtain ⟨m1, n1⟩ := V9.smul_spec u.2.1 _ c r1
  obtain ⟨m2, n2⟩ := V9.smul_spec u.2.2.1 _ c r2
  obtain ⟨m3, n3⟩ := V9.smul_spec u.2.2.2 _ c r3
  obtain ⟨a1, a2⟩ := V9.add_spec _ _ c m0 m1
  obtain ⟨b1, b2⟩ := V9.add_spec _ _ c a1 m2
  obtain ⟨c1, c2⟩ := V9.add_spec _ _ c b1 m3
  refine ⟨c1, ?_⟩
  simp only [cwOf, rows, dot, c2, b2, a2, n0, n1, n2, n3, s0, s1, s2, s3]

/-- support mask of a bit-sliced GF(9) vector -/
def nz (x : V9) : Nat := x.re.a ||| x.re.b ||| x.im.a ||| x.im.b

theorem nz_bool : ∀ p q r s : Bool, (p && q) = false → (r && s) = false →
    (p || q || r || s) = decide ((⟨dec3 p q, dec3 r s⟩ : GF9) ≠ 0) := by decide

theorem nz_spec (x : V9) (c : Nat) (h : x.ok c) : (nz x).testBit c = decide (x.get c ≠ 0) := by
  obtain ⟨h1, h2⟩ := h
  unfold V3.ok at h1 h2
  simp only [nz, V9.get, V3.get, Nat.testBit_or]
  exact nz_bool _ _ _ _ h1 h2

/-- number of set bits among the lowest `m` bits -/
def pc : Nat → Nat → Nat
  | _, 0 => 0
  | x, m + 1 => x % 2 + pc (x / 2) m

theorem countP_eq_pc {α : Type} (p : α → Bool) (L : List α) (X : Nat)
    (h : ∀ c (hc : c < L.length), X.testBit c = p L[c]) : L.countP p = pc X L.length := by
  induction L generalizing X with
  | nil => rfl
  | cons a L ih =>
    have h0 := h 0 (by simp)
    have ht : ∀ c (hc : c < L.length), (X / 2).testBit c = p L[c] := by
      intro c hc
      rw [Nat.testBit_div_two]
      exact h (c + 1) (by simp; omega)
    rw [List.countP_cons, ih (X / 2) ht]
    simp only [List.length_cons, pc]
    simp only [Nat.testBit_zero, List.getElem_cons_zero] at h0
    cases hp : p a <;> rw [hp] at h0 <;> simp at h0 <;> simp <;> omega

theorem wt_eq (L : List Vec4) (u : Vec4) : wt (codeword L u) = pc (nz (cwOf (rows L) u)) L.length := by
  have := countP_eq_pc (fun x : GF9 => decide (x ≠ 0)) (codeword L u) (nz (cwOf (rows L) u)) (by
    intro c hc
    have hc' : c < L.length := by simpa [codeword] using hc
    obtain ⟨h1, h2⟩ := cw_spec L u c hc'
    rw [nz_spec _ _ h1, h2]
    simp [codeword])
  simpa [wt, codeword] using this

/-! ## 4. The finite check -/

/-- the check performed for one message (bit-sliced rows `R` precomputed) -/
def checkR (R : V9 × V9 × V9 × V9) (n d : Nat) (u : Vec4) : Bool := decide (d ≤ pc (nz (cwOf R u)) n)

/-- all 9 elements of GF(9) -/
def allGF9 : List GF9 := [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨2, 2⟩]

theorem mem_allGF9 : ∀ x : GF9, x ∈ allGF9 := by decide

/-- the (9^4-1)/(9-1) = 820 normalised nonzero messages (first nonzero coordinate equal to 1) -/
def projMsgs : List Vec4 :=
  (allGF9.flatMap fun b => allGF9.flatMap fun c => allGF9.map fun d => ((1 : GF9), b, c, d)) ++
  (allGF9.flatMap fun c => allGF9.map fun d => ((0 : GF9), (1 : GF9), c, d)) ++
  (allGF9.map fun d => ((0 : GF9), (0 : GF9), (1 : GF9), d)) ++ [((0 : GF9), (0 : GF9), (0 : GF9), (1 : GF9))]

/-- Boolean certificate: all normalised messages give weight `≥ d` -/
def certify (L : List Vec4) (n d : Nat) : Bool :=
  L.length == n && (let R := rows L; projMsgs.all (checkR R n d))

/-! ## 5. Soundness of the check (projective reduction) -/

def smul4 (s : GF9) (u : Vec4) : Vec4 := (s * u.1, s * u.2.1, s * u.2.2.1, s * u.2.2.2)

theorem gf9_distrib : ∀ x y z : GF9, x * (y + z) = x * y + x * z := by decide
theorem gf9_assoc : ∀ x y z : GF9, (x * y) * z = x * (y * z) := by decide
theorem gf9_nz : ∀ s x : GF9, s ≠ 0 → (s * x ≠ 0 ↔ x ≠ 0) := by decide
theorem gf9_inv : ∀ x : GF9, x ≠ 0 → GF9.inv x * x = 1 := by decide
theorem gf9_inv_nz : ∀ x : GF9, x ≠ 0 → GF9.inv x ≠ 0 := by decide
theorem gf9_zero_mul : ∀ x : GF9, x * 0 = 0 := by decide

theorem dot_smul (s : GF9) (u c : Vec4) : dot (smul4 s u) c = s * dot u c := by
  simp only [dot, smul4, gf9_distrib, gf9_assoc]

theorem wt_smul (L : List Vec4) (s : GF9) (hs : s ≠ 0) (u : Vec4) :
    wt (codeword L (smul4 s u)) = wt (codeword L u) := by
  unfold wt codeword
  rw [List.countP_map, List.countP_map]
  apply List.countP_congr
  intro x _
  simp only [Function.comp, dot_smul, decide_eq_true_eq]
  exact gf9_nz s _ hs

theorem isCode_of_certify (L : List Vec4) (n d : Nat) (h : certify L n d = true) : IsCode L n d := by
  simp only [certify, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hlen, hall⟩ := h
  have hall' := List.all_eq_true.mp hall
  have sound : ∀ u ∈ projMsgs, d ≤ wt (codeword L u) := by
    intro u hu
    have := hall' u hu
    rw [wt_eq, hlen]
    simpa [checkR] using this
  have H1 : ∀ b c e : GF9, d ≤ wt (codeword L (1, b, c, e)) := fun b c e => sound _ (by
    simp [projMsgs, List.mem_flatMap, List.mem_map, mem_allGF9])
  have H2 : ∀ c e : GF9, d ≤ wt (codeword L (0, 1, c, e)) := fun c e => sound _ (by
    simp [projMsgs, List.mem_flatMap, List.mem_map, mem_allGF9])
  have H3 : ∀ e : GF9, d ≤ wt (codeword L (0, 0, 1, e)) := fun e => sound _ (by
    simp [projMsgs, List.mem_flatMap, List.mem_map, mem_allGF9])
  have H4 : d ≤ wt (codeword L (0, 0, 0, 1)) := sound _ (by
    simp [projMsgs, List.mem_flatMap, List.mem_map, mem_allGF9])
  refine ⟨hlen, ?_⟩
  intro u hu
  obtain ⟨u1, u2, u3, u4⟩ := u
  by_cases h1 : u1 = 0
  · subst h1
    by_cases h2 : u2 = 0
    · subst h2
      by_cases h3 : u3 = 0
      · subst h3
        have h4 : u4 ≠ 0 := fun h => hu (by rw [h])
        rw [← wt_smul L (GF9.inv u4) (gf9_inv_nz u4 h4)]
        simpa [smul4, gf9_zero_mul, gf9_inv u4 h4] using H4
      · rw [← wt_smul L (GF9.inv u3) (gf9_inv_nz u3 h3)]
        simpa [smul4, gf9_zero_mul, gf9_inv u3 h3] using H3 (GF9.inv u3 * u4)
    · rw [← wt_smul L (GF9.inv u2) (gf9_inv_nz u2 h2)]
      simpa [smul4, gf9_zero_mul, gf9_inv u2 h2] using H2 (GF9.inv u2 * u3) (GF9.inv u2 * u4)
  · rw [← wt_smul L (GF9.inv u1) (gf9_inv_nz u1 h1)]
    simpa [smul4, gf9_inv u1 h1] using H1 (GF9.inv u1 * u2) (GF9.inv u1 * u3) (GF9.inv u1 * u4)

/-! ### Puncturing -/

theorem countP_drop_ge {α : Type} (p : α → Bool) (l : List α) (t : Nat) :
    l.countP p ≤ (l.drop t).countP p + t := by
  have h := List.take_append_drop t l
  have h1 : l.countP p = (l.take t).countP p + (l.drop t).countP p := by
    conv => lhs; rw [← h]
    rw [List.countP_append]
  have h2 : (l.take t).countP p ≤ t := by
    have := List.countP_le_length (p := p) (l := l.take t)
    have := List.length_take_le t l
    omega
  omega

/-- Puncturing: deleting the first `t` columns of an `[n, 4, ≥ d]` code gives an
`[n - t, 4, ≥ d - t]` code (for `t < d` this is again a 4-dimensional code). -/
theorem isCode_drop (L : List Vec4) (n d t : Nat) (h : IsCode L n d) :
    IsCode (L.drop t) (n - t) (d - t) := by
  refine ⟨by simp [h.1], fun u hu => ?_⟩
  have h1 := h.2 u hu
  have h2 := countP_drop_ge (fun x : GF9 => decide (x ≠ 0)) (codeword L u) t
  have h3 : codeword (L.drop t) u = (codeword L u).drop t := by simp [codeword, List.map_drop]
  unfold wt at *
  rw [h3]; omega

/-! ## 6. The new codes -/

/-- generator-matrix columns of the new `[468, 4, 414]_9` code (base-9 codes, see `ofCode`) -/
def C_468_414 : List Vec4 := ([
  10, 55, 64, 82, 100, 118, 127, 109, 145, 163, 171, 172, 190, 235, 217, 334, 343, 361, 370, 388,
  406, 414, 415, 442, 433, 478, 460, 469, 271, 316, 657, 694, 676, 712, 495, 505, 514, 559, 541, 586,
  604, 595, 640, 622, 631, 730, 739, 748, 775, 802, 784, 793, 819, 829, 847, 856, 838, 883, 865, 874,
  892, 900, 901, 910, 928, 937, 919, 955, 1063, 1090, 1081, 1126, 1108, 1135, 1143, 1144, 1153, 1171, 1180, 1189,
  981, 982, 1018, 1000, 1045, 1378, 1396, 1414, 1423, 1405, 1450, 1224, 1225, 1234, 1252, 1261, 1288, 1305, 1315, 1333,
  1351, 1459, 1467, 1468, 1495, 1513, 1522, 1539, 1540, 1548, 1558, 1585, 1567, 1612, 1594, 1603, 1629, 1657, 1666, 1819,
  1828, 1855, 1864, 1872, 1873, 1891, 1936, 1702, 1710, 1711, 1738, 1747, 1774, 1756, 1765, 2107, 2115, 2143, 2179, 2161,
  1963, 1981, 1990, 1999, 2026, 2034, 2071, 2053, 2098, 2089, 2917, 2925, 2935, 2953, 2944, 2980, 2997, 2998, 3006, 3016,
  3025, 3070, 3052, 3079, 3097, 3115, 3124, 3133, 3142, 3250, 3259, 3268, 3313, 3295, 3322, 3331, 3358, 3349, 3169, 3178,
  3205, 3187, 3232, 3214, 3223, 3565, 3573, 3574, 3583, 3601, 3628, 3403, 3411, 3439, 3448, 3475, 3457, 3466, 3484, 3493,
  3502, 3520, 3511, 3556, 3538, 3646, 3682, 3718, 3700, 3709, 3726, 3727, 3735, 3745, 3763, 3772, 3754, 3808, 3816, 3826,
  3844, 3835, 3880, 3862, 3871, 3979, 3988, 4015, 3997, 4024, 4033, 4059, 4069, 4087, 4096, 4078, 4123, 4114, 3889, 3898,
  3907, 3934, 3943, 4302, 4330, 4366, 4348, 4132, 4150, 4168, 4177, 4186, 4195, 4213, 4221, 4249, 4258, 4240, 4285, 4267,
  4276, 2196, 2206, 2260, 2242, 2268, 2287, 2305, 2314, 2296, 2341, 2332, 2350, 2358, 2395, 2422, 2413, 2512, 2530, 2548,
  2557, 2539, 2575, 2593, 2601, 2611, 2638, 2620, 2665, 2656, 2439, 2440, 2449, 2467, 2476, 2458, 2503, 2485, 2836, 2844,
  2845, 2872, 2908, 2890, 2899, 2682, 2683, 2692, 2710, 2719, 2701, 2728, 2755, 2763, 2773, 2791, 2800, 2809, 2818, 5833,
  5842, 5851, 5913, 5914, 5923, 5950, 5941, 5977, 5995, 6003, 6004, 6031, 6022, 6067, 6166, 6220, 6238, 6247, 6274, 6310,
  6292, 6301, 6076, 6112, 6121, 6103, 6130, 6490, 6499, 6517, 6526, 6553, 6535, 6319, 6327, 6337, 6355, 6346, 6373, 6382,
  6408, 6427, 6454, 6463, 4375, 4383, 4447, 4429, 4455, 4464, 4474, 4501, 4519, 4537, 4582, 4564, 4609, 4600, 4699, 4744,
  4726, 4771, 4753, 4762, 4780, 4788, 4789, 4798, 4852, 4843, 4618, 4627, 4636, 4645, 4690, 4681, 5031, 5032, 5041, 4879,
  4897, 4906, 4933, 4915, 4924, 4950, 4951, 4978, 4987, 4969, 5005, 5104, 5112, 5113, 5149, 5131, 5176, 5158, 5184, 5185,
  5193, 5194, 5230, 5212, 5239, 5266, 5274, 5275, 5284, 5302, 5311, 5338, 5320, 5329, 5446, 5455, 5509, 5527, 5545, 5554,
  5563, 5356, 5365, 5392, 5374, 5419, 5410, 5752, 5760, 5797, 5779, 5806, 5815, 5598, 5608, 5635, 5617, 5662, 5644, 5653,
  5679, 5680, 5689, 5707, 5716, 5698, 5743, 5734] : List Nat).map ofCode

theorem C_468_414_cert : certify C_468_414 468 414 = true := by decide +kernel

theorem C_468_414_isCode : IsCode C_468_414 468 414 := isCode_of_certify _ _ _ C_468_414_cert

/-- generator-matrix columns of the new `[408, 4, 360]_9` code (base-9 codes, see `ofCode`) -/
def C_408_360 : List Vec4 := ([
  1, 9, 37, 46, 28, 90, 91, 118, 127, 109, 136, 145, 172, 190, 226, 325, 334, 370, 352, 397,
  379, 406, 414, 415, 424, 442, 469, 244, 289, 307, 657, 685, 721, 703, 712, 495, 496, 514, 559, 541,
  550, 568, 577, 604, 613, 595, 640, 631, 729, 738, 748, 775, 802, 784, 810, 819, 847, 838, 883, 865,
  892, 900, 919, 964, 946, 955, 1054, 1072, 1090, 1099, 1108, 1135, 1153, 1180, 1207, 1189, 973, 1009, 1018, 1000,
  1027, 1378, 1414, 1423, 1450, 1432, 1216, 1224, 1225, 1234, 1261, 1288, 1297, 1306, 1315, 1333, 1324, 1468, 1495, 1504,
  1531, 1513, 1539, 1549, 1558, 1603, 1621, 1630, 1657, 1666, 1783, 1819, 1828, 1837, 1864, 1873, 1882, 1720, 1738, 1747,
  1729, 1765, 2107, 2161, 2170, 1953, 1999, 2026, 2044, 2062, 2053, 2080, 2089, 2925, 2953, 2962, 2944, 2971, 2980, 2997,
  2998, 3007, 3025, 3070, 3079, 3087, 3088, 3097, 3151, 3142, 3241, 3250, 3277, 3304, 3322, 3340, 3358, 3367, 3349, 3394,
  3385, 3160, 3205, 3187, 3223, 3583, 3601, 3610, 3619, 3403, 3411, 3412, 3421, 3439, 3457, 3493, 3529, 3511, 3556, 3547,
  3646, 3655, 3664, 3682, 3691, 3673, 3700, 3727, 3736, 3763, 3772, 3754, 3799, 3817, 3853, 3835, 3862, 3978, 4015, 4042,
  4024, 4033, 4060, 4069, 4087, 4096, 4105, 3889, 3898, 3943, 3952, 4339, 4321, 4366, 4348, 4132, 4168, 4177, 4159, 4195,
  4222, 4258, 4240, 4276, 2196, 2197, 2260, 2242, 2251, 2269, 2277, 2287, 2314, 2296, 2341, 2332, 2350, 2395, 2413, 2512,
  2530, 2548, 2584, 2601, 2602, 2629, 2620, 2647, 2431, 2439, 2476, 2503, 2485, 2494, 2836, 2844, 2845, 2854, 2872, 2881,
  2890, 2899, 2674, 2683, 2692, 2710, 2701, 2728, 2737, 2763, 2773, 2782, 2818, 5833, 5842, 5851, 5896, 5913, 5922, 5959,
  5941, 5977, 6013, 6031, 6040, 6067, 6157, 6165, 6175, 6193, 6202, 6184, 6211, 6220, 6247, 6256, 6274, 6283, 6265, 6121,
  6148, 6130, 6481, 6489, 6490, 6517, 6508, 6553, 6544, 6337, 6346, 6391, 6373, 6400, 6409, 6418, 6445, 6427, 6472, 6454,
  4375, 4384, 4411, 4420, 4438, 4464, 4465, 4474, 4492, 4501, 4510, 4519, 4545, 4555, 4573, 4591, 4707, 4708, 4726, 4780,
  4789, 4852, 4834, 4654, 4645, 4672, 4681, 5032, 5059, 5050, 5077, 5086, 4861, 4869, 4879, 4888, 4933, 4950, 4951, 5104,
  5113, 5122, 5140, 5149, 5203, 5221, 5212, 5239, 5248, 5274, 5275, 5311, 5293, 5428, 5436, 5446, 5473, 5455, 5500, 5482,
  5491, 5517, 5518, 5545, 5536, 5581, 5572, 5419, 5760, 5761, 5770, 5788, 5779, 5815, 5590, 5598, 5599, 5626, 5617, 5662,
  5644, 5653, 5679, 5680, 5707, 5743, 5725, 5734] : List Nat).map ofCode

theorem C_408_360_cert : certify C_408_360 408 360 = true := by decide +kernel

theorem C_408_360_isCode : IsCode C_408_360 408 360 := isCode_of_certify _ _ _ C_408_360_cert

/-- generator-matrix columns of the new `[314, 4, 276]_9` code (base-9 codes, see `ofCode`) -/
def C_314_276 : List Vec4 := ([
  37, 73, 91, 118, 154, 136, 145, 172, 190, 235, 226, 325, 343, 352, 379, 388, 406, 414, 442, 451,
  433, 469, 244, 316, 298, 676, 703, 532, 514, 541, 550, 576, 577, 586, 604, 595, 622, 631, 738, 739,
  748, 766, 775, 802, 810, 819, 829, 900, 901, 910, 1054, 1072, 1099, 1081, 1144, 1207, 1189, 991, 1027, 1036,
  1378, 1423, 1432, 1441, 1224, 1243, 1288, 1270, 1305, 1306, 1477, 1495, 1504, 1513, 1540, 1548, 1549, 1558, 1576, 1567,
  1603, 1621, 1629, 1630, 1639, 1666, 1693, 1675, 1783, 1819, 1828, 1837, 1918, 1729, 2107, 2143, 2152, 2152, 2134, 2161,
  1945, 1953, 1990, 1972, 2017, 2026, 2044, 2080, 2917, 2925, 2935, 2944, 2989, 2980, 2998, 3034, 3061, 3079, 3097, 3106,
  3250, 3277, 3313, 3295, 3304, 3322, 3340, 3367, 3385, 3169, 3178, 3187, 3223, 3583, 3601, 3592, 3628, 3411, 3493, 3502,
  3520, 3529, 3511, 3556, 3664, 3682, 3673, 3718, 3709, 3763, 3754, 3799, 3871, 3988, 4015, 3997, 4087, 3925, 3934, 3952,
  4312, 4330, 4339, 4348, 4177, 4195, 4213, 4231, 4249, 4258, 4240, 2188, 2197, 2224, 2233, 2215, 2260, 2269, 2287, 2296,
  2323, 2332, 2350, 2395, 2377, 2422, 2413, 2520, 2601, 2629, 2638, 2647, 2439, 2440, 2467, 2476, 2458, 2494, 2845, 2854,
  2908, 2890, 2899, 2674, 2683, 2692, 2737, 2763, 2773, 5833, 5842, 5878, 5887, 5896, 5913, 5932, 5977, 5995, 6031, 6067,
  6049, 6157, 6165, 6166, 6193, 6202, 6184, 6220, 6238, 6247, 6274, 6292, 6301, 6084, 6112, 6130, 6481, 6489, 6490, 6499,
  6535, 6544, 6319, 6327, 6337, 6391, 6436, 6436, 4455, 4456, 4465, 4474, 4483, 4510, 4545, 4582, 4564, 4609, 4591, 4600,
  4699, 4744, 4789, 4798, 4834, 4618, 4626, 4681, 5068, 4861, 4888, 4942, 4950, 4951, 4987, 4969, 5014, 5140, 5131, 5185,
  5221, 5212, 5257, 5239, 5274, 5275, 5284, 5302, 5311, 5293, 5320, 5446, 5473, 5455, 5500, 5491, 5517, 5572, 5383, 5392,
  5401, 5752, 5788, 5797, 5824, 5806, 5608, 5644, 5653, 5689, 5707, 5716, 5698, 5734] : List Nat).map ofCode

theorem C_314_276_cert : certify C_314_276 314 276 = true := by decide +kernel

theorem C_314_276_isCode : IsCode C_314_276 314 276 := isCode_of_certify _ _ _ C_314_276_cert

/-- generator-matrix columns of the new `[355, 4, 312]_9` code (base-9 codes, see `ofCode`) -/
def C_355_312 : List Vec4 := ([
  1, 9, 46, 55, 64, 81, 90, 127, 145, 172, 208, 190, 235, 217, 361, 352, 397, 406, 414, 478,
  252, 289, 271, 316, 316, 316, 307, 658, 667, 685, 694, 676, 487, 495, 496, 523, 541, 568, 576, 613,
  730, 748, 766, 775, 784, 820, 847, 838, 883, 865, 874, 901, 910, 964, 955, 1054, 1072, 1090, 1126, 1117,
  1143, 1171, 1180, 981, 982, 991, 1009, 1018, 1045, 1027, 1378, 1396, 1216, 1252, 1279, 1315, 1342, 1369, 1459, 1477,
  1504, 1540, 1549, 1558, 1621, 1629, 1639, 1684, 1792, 1819, 1828, 1810, 1846, 1872, 1891, 1918, 1774, 1756, 1765, 2115,
  2116, 2125, 2143, 2152, 1945, 1954, 1963, 1972, 2017, 1999, 2026, 2034, 2062, 2053, 2080, 2935, 2953, 2962, 2980, 2997,
  2998, 3034, 3043, 3052, 3061, 3088, 3097, 3115, 3151, 3142, 3241, 3259, 3295, 3331, 3367, 3394, 3376, 3160, 3169, 3187,
  3232, 3214, 3223, 3565, 3583, 3601, 3610, 3592, 3619, 3403, 3411, 3492, 3493, 3538, 3654, 3655, 3726, 3727, 3799, 3816,
  3826, 3853, 3835, 3880, 3862, 3988, 3997, 4051, 4059, 4060, 4096, 4123, 4105, 4114, 3889, 3898, 3907, 3934, 3943, 3952,
  4294, 4303, 4339, 4348, 4357, 4150, 4159, 4204, 4186, 4213, 4221, 4222, 4249, 4240, 4276, 2188, 2196, 2197, 2206, 2224,
  2260, 2242, 2268, 2278, 2287, 2305, 2296, 2386, 2422, 2413, 2512, 2520, 2584, 2575, 2593, 2611, 2665, 2656, 2431, 2440,
  2458, 2845, 2872, 2863, 2674, 2682, 2683, 2692, 2710, 2719, 2728, 2773, 2791, 2827, 2818, 5842, 5860, 5887, 5941, 5986,
  5968, 5977, 6003, 6004, 6031, 6040, 6166, 6175, 6202, 6184, 6220, 6238, 6247, 6274, 6310, 6292, 6084, 6094, 6103, 6148,
  6489, 6499, 6517, 6553, 6327, 6328, 6337, 6355, 6391, 6373, 6436, 6463, 4375, 4384, 4411, 4429, 4492, 4501, 4483, 4528,
  4510, 4545, 4546, 4555, 4573, 4582, 4564, 4600, 4699, 4717, 4735, 4762, 4798, 4807, 4843, 4626, 5023, 5032, 5041, 5077,
  5086, 4869, 4870, 4897, 4888, 4933, 4950, 4951, 4987, 4969, 4996, 5005, 5104, 5112, 5113, 5122, 5140, 5149, 5167, 5184,
  5221, 5212, 5274, 5284, 5311, 5428, 5437, 5446, 5464, 5455, 5500, 5509, 5517, 5518, 5545, 5554, 5536, 5347, 5355, 5365,
  5392, 5752, 5760, 5797, 5779, 5598, 5599, 5608, 5662, 5671, 5707, 5698, 5743, 5725, 5734] : List Nat).map ofCode

theorem C_355_312_cert : certify C_355_312 355 312 = true := by decide +kernel

theorem C_355_312_isCode : IsCode C_355_312 355 312 := isCode_of_certify _ _ _ C_355_312_cert

/-- generator-matrix columns of the new `[439, 4, 387]_9` code (base-9 codes, see `ofCode`) -/
def C_439_387 : List Vec4 := ([
  10, 19, 46, 28, 73, 55, 82, 90, 100, 118, 154, 136, 145, 171, 172, 199, 208, 217, 226, 333,
  343, 361, 370, 397, 388, 415, 433, 478, 460, 244, 253, 262, 289, 271, 307, 657, 667, 487, 495, 496,
  505, 523, 532, 541, 568, 576, 586, 604, 613, 595, 640, 631, 729, 730, 739, 748, 766, 775, 757, 784,
  793, 819, 900, 910, 928, 937, 946, 1054, 1063, 1072, 1090, 1099, 1126, 1117, 1135, 1144, 1153, 1171, 1162, 1207,
  1189, 973, 981, 982, 1018, 1000, 1027, 1378, 1386, 1387, 1396, 1414, 1405, 1450, 1432, 1216, 1234, 1261, 1279, 1306,
  1342, 1324, 1351, 1467, 1495, 1486, 1513, 1522, 1539, 1549, 1585, 1567, 1639, 1657, 1666, 1684, 1783, 1791, 1792, 1801,
  1819, 1810, 1855, 1864, 1872, 1909, 1936, 1918, 1927, 1710, 1711, 2115, 2116, 2125, 2134, 2179, 1954, 1981, 1990, 2008,
  2035, 2044, 2062, 2071, 2053, 2089, 2926, 2953, 2998, 3016, 3043, 3025, 3070, 3052, 3079, 3087, 3115, 3124, 3133, 3249,
  3277, 3286, 3268, 3295, 3330, 3331, 3367, 3394, 3376, 3160, 3168, 3196, 3205, 3214, 3223, 3565, 3573, 3574, 3583, 3601,
  3637, 3619, 3411, 3484, 3492, 3493, 3502, 3529, 3511, 3538, 3646, 3654, 3655, 3664, 3682, 3691, 3718, 3700, 3726, 3727,
  3735, 3736, 3745, 3772, 3799, 3781, 3790, 3816, 3970, 3979, 4006, 3997, 4024, 4033, 4051, 4060, 4069, 4096, 4078, 4123,
  4114, 3889, 3898, 3907, 3916, 3961, 4302, 4303, 4312, 4330, 4339, 4321, 4366, 4348, 4357, 4132, 4140, 4141, 4150, 4204,
  4186, 4221, 4285, 2188, 2196, 2197, 2206, 2224, 2215, 2260, 2242, 2268, 2278, 2314, 2341, 2323, 2332, 2358, 2359, 2386,
  2395, 2404, 2413, 2520, 2557, 2593, 2601, 2611, 2620, 2665, 2647, 2656, 2439, 2440, 2449, 2467, 2458, 2503, 2836, 2872,
  2881, 2890, 2682, 2683, 2692, 2719, 2701, 2746, 2755, 2763, 2764, 2773, 2791, 2782, 2827, 2809, 2818, 5833, 5842, 5869,
  5878, 5860, 5913, 5914, 5922, 5923, 5950, 5959, 5941, 5986, 5968, 5977, 5995, 6004, 6013, 6040, 6022, 6058, 6175, 6193,
  6202, 6184, 6229, 6211, 6246, 6256, 6076, 6085, 6094, 6112, 6148, 6130, 6139, 6489, 6490, 6517, 6526, 6535, 6544, 6337,
  6355, 6364, 6373, 6382, 6436, 6436, 6436, 4383, 4447, 4464, 4465, 4474, 4492, 4501, 4483, 4528, 4510, 4537, 4555, 4573,
  4591, 4600, 4717, 4735, 4744, 4726, 4771, 4753, 4762, 4788, 4825, 4852, 4843, 4627, 4636, 4654, 4663, 4645, 4690, 4681,
  5023, 5032, 5041, 5050, 5095, 5077, 5086, 4897, 4933, 4924, 4960, 4978, 4969, 5014, 4996, 5005, 5112, 5113, 5140, 5149,
  5131, 5176, 5158, 5184, 5193, 5194, 5203, 5230, 5257, 5266, 5275, 5338, 5320, 5436, 5437, 5464, 5500, 5482, 5347, 5355,
  5392, 5419, 5401, 5410, 5760, 5770, 5779, 5824, 5815, 5590, 5608, 5626, 5635, 5662, 5671, 5689, 5743, 5725, 5734] : List Nat).map ofCode

theorem C_439_387_cert : certify C_439_387 439 387 = true := by decide +kernel

theorem C_439_387_isCode : IsCode C_439_387 439 387 := isCode_of_certify _ _ _ C_439_387_cert

/-- generator-matrix columns of the new `[579, 4, 513]_9` code (base-9 codes, see `ofCode`) -/
def C_579_513 : List Vec4 := ([
  1, 9, 10, 19, 28, 73, 64, 81, 82, 90, 100, 118, 127, 154, 145, 163, 172, 181, 199, 190,
  235, 217, 226, 334, 361, 352, 388, 406, 414, 415, 451, 433, 478, 460, 244, 252, 262, 280, 289, 316,
  298, 307, 649, 657, 658, 667, 685, 676, 703, 712, 495, 496, 505, 523, 532, 514, 541, 568, 576, 577,
  586, 604, 613, 595, 640, 631, 729, 730, 738, 748, 802, 810, 811, 819, 820, 829, 847, 856, 865, 874,
  900, 928, 937, 919, 964, 946, 1054, 1063, 1090, 1081, 1126, 1108, 1117, 1135, 1143, 1153, 1180, 1162, 1207, 1198,
  991, 1009, 1045, 1027, 1396, 1414, 1423, 1405, 1450, 1432, 1441, 1224, 1252, 1261, 1243, 1279, 1297, 1305, 1306, 1342,
  1369, 1351, 1360, 1459, 1467, 1468, 1495, 1504, 1486, 1531, 1513, 1522, 1539, 1540, 1548, 1558, 1585, 1567, 1612, 1594,
  1629, 1630, 1639, 1657, 1648, 1693, 1675, 1791, 1792, 1801, 1819, 1828, 1810, 1855, 1837, 1864, 1873, 1882, 1909, 1936,
  1927, 1702, 1710, 1711, 1720, 1747, 1765, 2107, 2115, 2116, 2125, 2143, 2152, 2179, 2170, 1945, 1953, 1963, 1972, 2017,
  1999, 2008, 2026, 2035, 2044, 2071, 2053, 2098, 2089, 2917, 2926, 2953, 2944, 2989, 2971, 2980, 2998, 3006, 3007, 3016,
  3043, 3025, 3070, 3052, 3061, 3079, 3087, 3088, 3097, 3124, 3151, 3241, 3249, 3259, 3277, 3286, 3268, 3313, 3304, 3331,
  3340, 3358, 3367, 3349, 3376, 3385, 3160, 3168, 3196, 3205, 3232, 3214, 3223, 3565, 3573, 3574, 3583, 3601, 3610, 3592,
  3637, 3628, 3412, 3421, 3439, 3448, 3430, 3457, 3466, 3484, 3511, 3538, 3646, 3654, 3655, 3664, 3682, 3691, 3718, 3700,
  3726, 3735, 3736, 3745, 3763, 3772, 3754, 3799, 3790, 3808, 3816, 3817, 3844, 3853, 3862, 3970, 3978, 3979, 3988, 4015,
  4042, 4024, 4033, 4051, 4060, 4069, 4123, 4105, 4114, 3898, 3907, 3934, 3961, 3943, 4294, 4302, 4303, 4330, 4321, 4366,
  4348, 4357, 4132, 4150, 4168, 4177, 4159, 4204, 4186, 4222, 4231, 4249, 4258, 4285, 4267, 4276, 2197, 2206, 2224, 2215,
  2242, 2251, 2268, 2277, 2278, 2314, 2296, 2341, 2323, 2332, 2350, 2358, 2368, 2395, 2377, 2422, 2404, 2413, 2512, 2520,
  2521, 2530, 2548, 2557, 2539, 2566, 2593, 2601, 2602, 2611, 2638, 2620, 2665, 2647, 2431, 2439, 2440, 2449, 2476, 2458,
  2494, 2836, 2844, 2845, 2854, 2863, 2908, 2899, 2674, 2682, 2683, 2710, 2719, 2746, 2728, 2737, 2755, 2764, 2773, 2782,
  2809, 2818, 5833, 5841, 5842, 5851, 5869, 5878, 5905, 5887, 5896, 5914, 5923, 5932, 5950, 5941, 5977, 5995, 6003, 6004,
  6013, 6040, 6022, 6067, 6049, 6058, 6165, 6166, 6193, 6202, 6184, 6211, 6220, 6246, 6274, 6265, 6310, 6292, 6301, 6084,
  6085, 6094, 6121, 6103, 6130, 6481, 6489, 6517, 6508, 6553, 6535, 6319, 6327, 6328, 6337, 6364, 6346, 6391, 6382, 6400,
  6408, 6409, 6418, 6436, 6445, 6427, 6454, 6463, 4375, 4383, 4384, 4393, 4411, 4402, 4429, 4455, 4464, 4465, 4492, 4501,
  4483, 4528, 4510, 4537, 4546, 4555, 4573, 4582, 4564, 4609, 4707, 4708, 4717, 4744, 4726, 4753, 4762, 4780, 4788, 4789,
  4798, 4816, 4825, 4852, 4834, 4843, 4618, 4636, 4654, 4663, 4645, 4690, 4681, 5032, 5041, 5050, 5095, 5077, 4861, 4869,
  4870, 4906, 4888, 4933, 4915, 4924, 4942, 4950, 4987, 4969, 5014, 4996, 5005, 5112, 5122, 5140, 5149, 5131, 5176, 5158,
  5167, 5184, 5193, 5221, 5230, 5212, 5257, 5239, 5248, 5266, 5275, 5302, 5311, 5293, 5320, 5329, 5428, 5436, 5437, 5446,
  5473, 5455, 5500, 5491, 5509, 5518, 5527, 5554, 5536, 5563, 5572, 5347, 5355, 5356, 5383, 5419, 5752, 5760, 5761, 5770,
  5788, 5806, 5815, 5590, 5598, 5608, 5635, 5617, 5662, 5644, 5653, 5671, 5679, 5689, 5707, 5716, 5743, 5725, 5734] : List Nat).map ofCode

theorem C_579_513_cert : certify C_579_513 579 513 = true := by decide +kernel

theorem C_579_513_isCode : IsCode C_579_513 579 513 := isCode_of_certify _ _ _ C_579_513_cert

/-- generator-matrix columns of the new `[229, 4, 200]_9` code (base-9 codes, see `ofCode`) -/
def C_229_200 : List Vec4 := ([
  1, 9, 19, 81, 91, 109, 136, 171, 181, 208, 226, 325, 361, 397, 433, 478, 469, 244, 280, 307,
  667, 495, 532, 514, 559, 568, 576, 604, 640, 730, 748, 810, 820, 847, 874, 900, 901, 928, 1063, 1099,
  1135, 1180, 1198, 973, 1018, 1386, 1414, 1423, 1405, 1441, 1224, 1279, 1297, 1324, 1531, 1549, 1576, 1585, 1567, 1666,
  1693, 1675, 1684, 1846, 1873, 1882, 1900, 1720, 1738, 1774, 1756, 2152, 2134, 2161, 1954, 1981, 1972, 2034, 2053, 2953,
  3007, 3016, 3043, 3079, 3087, 3124, 3151, 3250, 3268, 3330, 3358, 3394, 3160, 3187, 3232, 3214, 3565, 3573, 3403, 3412,
  3421, 3430, 3520, 3529, 3556, 3538, 3673, 3718, 3726, 3763, 3799, 3826, 3844, 3853, 3880, 3871, 4006, 4051, 4096, 4114,
  3897, 3907, 3943, 4294, 4302, 4366, 4141, 4168, 4186, 4213, 4222, 4231, 2188, 2197, 2251, 2314, 2341, 2377, 2602, 2620,
  2665, 2431, 2476, 2503, 2844, 2854, 2881, 2890, 2682, 2683, 2692, 2692, 2719, 2755, 2773, 2782, 5841, 5878, 5913, 5922,
  5932, 5959, 5959, 5941, 5995, 6040, 6049, 6238, 6246, 6247, 6085, 6112, 6130, 6139, 6517, 6508, 6535, 6328, 6346, 6409,
  6436, 6472, 4429, 4464, 4492, 4519, 4545, 4573, 4564, 4753, 4762, 4789, 4834, 4626, 4636, 4654, 4645, 5023, 5032, 5068,
  4879, 4897, 4960, 5104, 5113, 5167, 5184, 5203, 5257, 5284, 5320, 5329, 5436, 5500, 5509, 5518, 5563, 5355, 5374, 5401,
  5779, 5608, 5635, 5662, 5671, 5679, 5680, 5698, 5734] : List Nat).map ofCode

theorem C_229_200_cert : certify C_229_200 229 200 = true := by decide +kernel

theorem C_229_200_isCode : IsCode C_229_200 229 200 := isCode_of_certify _ _ _ C_229_200_cert

/-- generator-matrix columns of the new `[390, 4, 343]_9` code (base-9 codes, see `ofCode`) -/
def C_390_343 : List Vec4 := ([
  82, 91, 100, 127, 109, 136, 145, 163, 172, 199, 208, 190, 235, 333, 361, 370, 352, 379, 388, 424,
  451, 433, 253, 289, 316, 307, 657, 658, 667, 685, 694, 676, 712, 487, 496, 505, 532, 514, 559, 541,
  568, 577, 604, 640, 738, 739, 802, 811, 820, 847, 856, 838, 892, 900, 937, 919, 964, 1062, 1090, 1081,
  1117, 1180, 1162, 1207, 1189, 1198, 981, 991, 1009, 1018, 1036, 1386, 1414, 1450, 1441, 1279, 1297, 1305, 1306, 1333,
  1324, 1351, 1459, 1468, 1477, 1495, 1504, 1522, 1539, 1540, 1549, 1558, 1576, 1585, 1603, 1621, 1657, 1648, 1693, 1675,
  1684, 1791, 1828, 1846, 1872, 1909, 1927, 1702, 1738, 2107, 2115, 2116, 2125, 2143, 2134, 2179, 1945, 1963, 1990, 1972,
  1999, 2008, 2026, 2035, 2071, 2053, 2080, 2089, 2917, 2925, 2926, 2962, 2989, 2980, 2997, 2998, 3006, 3007, 3016, 3034,
  3088, 3097, 3115, 3124, 3151, 3133, 3241, 3249, 3250, 3277, 3295, 3322, 3331, 3340, 3367, 3349, 3394, 3160, 3178, 3196,
  3565, 3583, 3601, 3628, 3411, 3412, 3448, 3430, 3475, 3457, 3466, 3511, 3664, 3682, 3691, 3718, 3709, 3763, 3754, 3781,
  3808, 3817, 3853, 3880, 4042, 4051, 4059, 4060, 4069, 4078, 4123, 4105, 4114, 3889, 3897, 3898, 3907, 3925, 3934, 3961,
  3943, 4294, 4302, 4303, 4330, 4339, 4140, 4150, 4168, 4177, 4159, 4204, 4195, 4213, 4221, 4222, 4231, 4249, 4240, 4285,
  4267, 2197, 2206, 2224, 2233, 2215, 2260, 2358, 2359, 2368, 2386, 2395, 2377, 2512, 2530, 2539, 2584, 2575, 2593, 2602,
  2611, 2629, 2638, 2665, 2656, 2431, 2439, 2458, 2494, 2836, 2844, 2845, 2872, 2881, 2863, 2908, 2899, 2674, 2682, 2719,
  2701, 2746, 2737, 2755, 2782, 2827, 2818, 5833, 5841, 5851, 5878, 5860, 5913, 5914, 5959, 5968, 5977, 6031, 6040, 6058,
  6165, 6184, 6220, 6076, 6084, 6094, 6121, 6489, 6508, 6553, 6535, 6327, 6346, 6400, 6408, 6418, 6436, 6463, 4375, 4384,
  4420, 4402, 4447, 4464, 4465, 4474, 4492, 4483, 4510, 4519, 4699, 4708, 4735, 4744, 4771, 4780, 4789, 4798, 4843, 4618,
  4626, 4636, 4654, 4663, 4645, 4690, 4672, 5023, 5031, 5041, 5068, 5095, 5086, 4861, 4869, 4879, 4897, 4906, 4924, 4950,
  4951, 4960, 4978, 4969, 5014, 5005, 5104, 5112, 5122, 5131, 5176, 5158, 5167, 5221, 5212, 5274, 5275, 5284, 5293, 5338,
  5320, 5329, 5436, 5446, 5455, 5482, 5518, 5527, 5545, 5536, 5581, 5572, 5347, 5356, 5365, 5383, 5392, 5374, 5410, 5599,
  5608, 5626, 5662, 5644, 5653, 5671, 5680, 5707, 5743, 5734] : List Nat).map ofCode

theorem C_390_343_cert : certify C_390_343 390 343 = true := by decide +kernel

theorem C_390_343_isCode : IsCode C_390_343 390 343 := isCode_of_certify _ _ _ C_390_343_cert

/-- generator-matrix columns of the new `[345, 4, 303]_9` code (base-9 codes, see `ofCode`) -/
def C_345_303 : List Vec4 := ([
  1, 55, 81, 90, 91, 100, 118, 127, 171, 172, 208, 190, 235, 217, 226, 343, 361, 406, 442, 478,
  460, 252, 253, 289, 316, 316, 298, 649, 657, 658, 694, 676, 721, 712, 487, 496, 505, 532, 514, 541,
  568, 613, 729, 738, 739, 802, 820, 829, 847, 838, 883, 865, 874, 910, 928, 964, 946, 955, 1062, 1090,
  1099, 1081, 1126, 1108, 1117, 1135, 1153, 1171, 1198, 973, 981, 1018, 1378, 1396, 1423, 1225, 1252, 1243, 1288, 1279,
  1306, 1315, 1351, 1495, 1504, 1539, 1548, 1558, 1585, 1603, 1630, 1657, 1648, 1684, 1783, 1792, 1819, 1828, 1810, 1846,
  1872, 1891, 1918, 1702, 1711, 2116, 2125, 2143, 2134, 2170, 1945, 1954, 1963, 2017, 1999, 2008, 2026, 2062, 2071, 2080,
  2953, 2962, 2989, 2980, 2998, 3006, 3052, 3079, 3087, 3088, 3115, 3124, 3151, 3133, 3241, 3250, 3277, 3313, 3367, 3349,
  3394, 3376, 3178, 3232, 3573, 3574, 3583, 3601, 3592, 3619, 3628, 3403, 3411, 3448, 3475, 3457, 3466, 3492, 3493, 3502,
  3556, 3547, 3655, 3682, 3691, 3673, 3718, 3726, 3727, 3799, 3808, 3816, 3880, 3862, 3988, 4006, 3997, 4051, 4059, 4060,
  4069, 4096, 4123, 4105, 4114, 3897, 3925, 3952, 4294, 4303, 4330, 4339, 4348, 4357, 4140, 4177, 4159, 4204, 4186, 4213,
  4221, 4222, 4249, 4240, 4276, 2197, 2206, 2233, 2260, 2251, 2277, 2358, 2386, 2413, 2512, 2520, 2584, 2440, 2467, 2494,
  2872, 2863, 2674, 2682, 2692, 2719, 2701, 2746, 2763, 5833, 5878, 5860, 5887, 5896, 5914, 5941, 5986, 5977, 6004, 6013,
  6202, 6211, 6220, 6238, 6247, 6274, 6310, 6292, 6084, 6085, 6112, 6517, 6526, 6508, 6535, 6319, 6364, 6400, 6408, 6409,
  6436, 6463, 4375, 4384, 4393, 4411, 4447, 4438, 4464, 4492, 4501, 4483, 4528, 4510, 4545, 4555, 4573, 4564, 4609, 4591,
  4600, 4699, 4717, 4744, 4771, 4762, 4798, 4816, 4825, 4618, 4626, 4654, 4663, 4690, 4681, 5031, 5032, 5095, 5086, 4869,
  4870, 4897, 4950, 4987, 4969, 5104, 5113, 5122, 5140, 5149, 5131, 5221, 5230, 5212, 5257, 5274, 5275, 5284, 5311, 5428,
  5436, 5437, 5446, 5473, 5500, 5491, 5518, 5536, 5347, 5365, 5392, 5374, 5410, 5760, 5770, 5797, 5662, 5644, 5671, 5689,
  5707, 5698, 5743, 5725, 5734] : List Nat).map ofCode

theorem C_345_303_cert : certify C_345_303 345 303 = true := by decide +kernel

theorem C_345_303_isCode : IsCode C_345_303 345 303 := isCode_of_certify _ _ _ C_345_303_cert

/-- generator-matrix columns of the new `[486, 4, 429]_9` code (base-9 codes, see `ofCode`) -/
def C_486_429 : List Vec4 := ([
  19, 82, 100, 118, 127, 154, 163, 199, 208, 333, 334, 352, 388, 406, 415, 442, 433, 478, 460, 469,
  252, 253, 262, 316, 298, 307, 649, 658, 685, 721, 712, 487, 505, 523, 532, 514, 568, 576, 577, 613,
  622, 631, 730, 738, 748, 766, 775, 793, 810, 811, 829, 847, 856, 838, 883, 865, 900, 910, 928, 937,
  946, 1054, 1072, 1081, 1126, 1108, 1117, 1143, 1144, 1171, 1180, 1162, 1207, 1189, 1198, 981, 982, 1018, 1027, 1036,
  1378, 1386, 1387, 1396, 1423, 1405, 1450, 1441, 1224, 1225, 1261, 1279, 1297, 1305, 1306, 1333, 1342, 1351, 1459, 1467,
  1468, 1477, 1486, 1522, 1539, 1540, 1548, 1549, 1558, 1585, 1567, 1594, 1603, 1621, 1629, 1639, 1666, 1648, 1693, 1675,
  1684, 1783, 1792, 1801, 1819, 1810, 1855, 1846, 1864, 1872, 1873, 1882, 1900, 1909, 1936, 1927, 1710, 1720, 1738, 1747,
  1756, 1765, 2107, 2115, 2116, 2125, 2134, 2179, 2161, 1953, 1954, 1963, 1981, 2017, 1999, 2008, 2034, 2071, 2053, 2098,
  2080, 2926, 2953, 2944, 2980, 2997, 2998, 3016, 3034, 3043, 3070, 3052, 3087, 3097, 3115, 3124, 3106, 3151, 3133, 3250,
  3259, 3277, 3268, 3313, 3330, 3331, 3340, 3358, 3367, 3349, 3394, 3376, 3169, 3178, 3196, 3205, 3214, 3223, 3573, 3583,
  3601, 3610, 3637, 3619, 3403, 3412, 3439, 3430, 3475, 3457, 3466, 3492, 3493, 3502, 3529, 3511, 3538, 3646, 3654, 3655,
  3664, 3718, 3726, 3727, 3799, 3781, 3816, 3817, 3826, 3844, 3835, 3862, 3871, 3970, 3979, 3988, 4006, 4051, 4087, 4096,
  4078, 4123, 4105, 3897, 3898, 3925, 3934, 3916, 3961, 3943, 4302, 4303, 4312, 4330, 4321, 4348, 4357, 4132, 4140, 4141,
  4150, 4177, 4204, 4186, 4195, 4213, 4221, 4222, 4249, 4285, 4267, 4276, 2196, 2206, 2215, 2268, 2278, 2305, 2314, 2296,
  2358, 2377, 2422, 2404, 2512, 2530, 2548, 2539, 2566, 2593, 2601, 2602, 2629, 2665, 2656, 2439, 2440, 2449, 2467, 2476,
  2458, 2503, 2494, 2836, 2844, 2854, 2908, 2682, 2683, 2692, 2710, 2746, 2737, 2755, 2763, 2764, 2791, 2782, 2809, 5833,
  5869, 5878, 5860, 5887, 5913, 5914, 5923, 5950, 5968, 5995, 6040, 6022, 6067, 6049, 6058, 6157, 6175, 6193, 6184, 6229,
  6211, 6238, 6246, 6292, 6085, 6094, 6121, 6148, 6130, 6139, 6481, 6489, 6499, 6517, 6526, 6508, 6553, 6544, 6319, 6327,
  6328, 6337, 6355, 6364, 6346, 6391, 6382, 6408, 6463, 4375, 4383, 4384, 4411, 4420, 4402, 4455, 4456, 4465, 4474, 4492,
  4501, 4483, 4528, 4519, 4537, 4545, 4555, 4582, 4564, 4609, 4591, 4717, 4735, 4744, 4726, 4771, 4753, 4762, 4788, 4825,
  4834, 4843, 4618, 4627, 4636, 4663, 4690, 4681, 5023, 5032, 5041, 5068, 5095, 5077, 5086, 4861, 4879, 4897, 4888, 4933,
  4942, 4960, 4987, 4969, 5014, 4996, 5005, 5104, 5112, 5149, 5131, 5176, 5158, 5184, 5193, 5194, 5203, 5221, 5230, 5212,
  5257, 5239, 5266, 5275, 5284, 5302, 5311, 5293, 5320, 5437, 5446, 5464, 5473, 5500, 5509, 5517, 5545, 5554, 5536, 5581,
  5563, 5572, 5347, 5355, 5392, 5374, 5419, 5401, 5410, 5752, 5760, 5761, 5824, 5806, 5815, 5598, 5599, 5608, 5626, 5635,
  5617, 5671, 5679, 5707, 5716, 5734] : List Nat).map ofCode

theorem C_486_429_cert : certify C_486_429 486 429 = true := by decide +kernel

theorem C_486_429_isCode : IsCode C_486_429 486 429 := isCode_of_certify _ _ _ C_486_429_cert

/-- generator-matrix columns of the new `[496, 4, 438]_9` code (base-9 codes, see `ofCode`) -/
def C_496_438 : List Vec4 := ([
  19, 46, 28, 81, 82, 100, 154, 136, 145, 163, 171, 172, 181, 199, 208, 235, 217, 226, 333, 406,
  414, 415, 442, 451, 433, 478, 469, 244, 252, 253, 262, 289, 271, 316, 298, 649, 657, 658, 667, 694,
  676, 703, 712, 523, 532, 514, 541, 568, 576, 577, 604, 595, 640, 622, 631, 729, 738, 748, 766, 757,
  802, 784, 793, 810, 811, 820, 829, 847, 856, 900, 901, 910, 928, 919, 964, 955, 1054, 1072, 1090, 1081,
  1108, 1117, 1143, 1189, 973, 982, 1018, 1000, 1045, 1027, 1036, 1378, 1386, 1387, 1396, 1423, 1450, 1216, 1225, 1234,
  1252, 1261, 1288, 1279, 1305, 1306, 1342, 1459, 1504, 1486, 1531, 1513, 1539, 1567, 1612, 1621, 1630, 1639, 1657, 1666,
  1648, 1684, 1791, 1792, 1801, 1828, 1855, 1837, 1846, 1864, 1872, 1882, 1900, 1909, 1891, 1936, 1710, 1720, 1738, 1747,
  1729, 1774, 1756, 1765, 2107, 2125, 2143, 2152, 2134, 2161, 1945, 1953, 1954, 1963, 1981, 1990, 1972, 2017, 2008, 2026,
  2034, 2044, 2062, 2089, 2925, 2926, 2935, 2953, 2962, 2971, 2980, 3034, 3043, 3079, 3087, 3088, 3124, 3106, 3151, 3142,
  3241, 3249, 3250, 3259, 3286, 3268, 3313, 3295, 3304, 3322, 3331, 3340, 3358, 3349, 3394, 3376, 3160, 3169, 3196, 3205,
  3187, 3214, 3565, 3573, 3574, 3583, 3601, 3610, 3592, 3628, 3403, 3411, 3430, 3492, 3502, 3520, 3529, 3511, 3556, 3538,
  3547, 3655, 3682, 3727, 3763, 3754, 3781, 3790, 3808, 3816, 3817, 3826, 3844, 3835, 3880, 3862, 3970, 3978, 3988, 4006,
  3997, 4042, 4024, 4033, 4059, 4060, 4069, 4078, 4123, 4105, 3889, 3925, 3934, 3943, 4302, 4303, 4312, 4330, 4339, 4366,
  4348, 4357, 4140, 4141, 4150, 4177, 4159, 4204, 4195, 4222, 4231, 4249, 4285, 4276, 2196, 2197, 2206, 2224, 2233, 2215,
  2260, 2269, 2277, 2287, 2305, 2314, 2296, 2341, 2323, 2350, 2368, 2395, 2377, 2404, 2413, 2520, 2521, 2530, 2548, 2557,
  2539, 2584, 2575, 2611, 2629, 2647, 2656, 2439, 2503, 2494, 2836, 2844, 2845, 2890, 2899, 2674, 2682, 2692, 2710, 2701,
  2737, 2755, 2764, 2791, 2800, 2782, 2827, 2809, 5841, 5842, 5851, 5869, 5905, 5887, 5896, 5922, 5923, 5932, 5950, 5959,
  5941, 5986, 5977, 6157, 6166, 6175, 6193, 6202, 6184, 6211, 6238, 6246, 6247, 6256, 6283, 6265, 6310, 6301, 6076, 6094,
  6112, 6121, 6103, 6148, 6139, 6489, 6490, 6526, 6508, 6553, 6535, 6544, 6319, 6327, 6328, 6337, 6355, 6364, 6391, 6373,
  6382, 6400, 6418, 6436, 4375, 4384, 4420, 4402, 4429, 4438, 4455, 4465, 4474, 4492, 4501, 4483, 4528, 4510, 4537, 4545,
  4573, 4582, 4564, 4609, 4591, 4707, 4708, 4762, 4798, 4807, 4834, 4618, 4626, 4627, 4636, 4663, 4690, 4672, 4681, 5023,
  5032, 5050, 5095, 5086, 4869, 4870, 4879, 4888, 4933, 4915, 4924, 4942, 4950, 4951, 4960, 4978, 4987, 5005, 5104, 5140,
  5149, 5131, 5176, 5158, 5167, 5184, 5185, 5193, 5203, 5221, 5230, 5212, 5257, 5248, 5274, 5275, 5302, 5311, 5293, 5338,
  5320, 5329, 5428, 5437, 5446, 5464, 5500, 5482, 5491, 5509, 5517, 5518, 5545, 5554, 5581, 5563, 5572, 5355, 5356, 5365,
  5383, 5374, 5419, 5410, 5760, 5599, 5608, 5617, 5644, 5679, 5680, 5689, 5716, 5698, 5743, 5725] : List Nat).map ofCode

theorem C_496_438_cert : certify C_496_438 496 438 = true := by decide +kernel

theorem C_496_438_isCode : IsCode C_496_438 496 438 := isCode_of_certify _ _ _ C_496_438_cert

/-- generator-matrix columns of the new `[303, 4, 266]_9` code (base-9 codes, see `ofCode`) -/
def C_303_266 : List Vec4 := ([
  1, 10, 19, 28, 73, 81, 82, 90, 100, 127, 136, 145, 172, 190, 217, 226, 406, 414, 424, 442,
  433, 244, 253, 262, 280, 298, 307, 657, 685, 721, 712, 495, 541, 586, 613, 631, 748, 810, 819, 883,
  892, 900, 910, 928, 946, 1135, 1144, 1162, 1207, 1189, 981, 1018, 1000, 1027, 1036, 1386, 1387, 1414, 1423, 1450,
  1270, 1297, 1305, 1306, 1333, 1342, 1360, 1459, 1495, 1486, 1531, 1522, 1539, 1549, 1558, 1576, 1612, 1621, 1630, 1648,
  1791, 1864, 1882, 1909, 1891, 1936, 1918, 1710, 1747, 2125, 2143, 2134, 2170, 1972, 2017, 1999, 2008, 2034, 2035, 2071,
  2098, 2080, 2089, 2917, 2926, 2953, 2989, 2998, 3007, 3016, 3043, 3052, 3087, 3088, 3115, 3106, 3340, 3358, 3394, 3376,
  3160, 3168, 3178, 3205, 3232, 3573, 3574, 3583, 3592, 3619, 3628, 3421, 3466, 3484, 3529, 3511, 3556, 3646, 3655, 3682,
  3673, 3718, 3727, 3735, 3745, 3763, 3754, 3799, 3790, 3816, 3871, 4096, 4078, 4105, 3897, 3934, 3943, 4312, 4330, 4339,
  4366, 4357, 4141, 4204, 4186, 4213, 4222, 4231, 4285, 4267, 4276, 2197, 2206, 2233, 2251, 2277, 2287, 2305, 2296, 2323,
  2358, 2368, 2377, 2404, 2413, 2593, 2601, 2638, 2620, 2665, 2647, 2656, 2439, 2440, 2476, 2458, 2503, 2485, 2881, 2908,
  2710, 2755, 2773, 2791, 2827, 2809, 2818, 5878, 5860, 5905, 5896, 5913, 5950, 5959, 5977, 5995, 6004, 6031, 6067, 6058,
  6283, 6076, 6094, 6103, 6139, 6481, 6490, 6499, 6508, 6364, 6391, 6382, 6409, 6418, 6436, 4393, 4402, 4465, 4474, 4483,
  4510, 4519, 4537, 4545, 4555, 4582, 4609, 4591, 4753, 4753, 4780, 4788, 4798, 4816, 4807, 4618, 4627, 4654, 4672, 4681,
  5031, 5068, 5095, 4906, 4924, 4942, 4950, 4987, 5140, 5149, 5158, 5167, 5184, 5185, 5194, 5212, 5239, 5274, 5302, 5293,
  5338, 5509, 5545, 5581, 5563, 5347, 5356, 5383, 5392, 5419, 5410, 5760, 5770, 5797, 5779, 5824, 5815, 5590, 5635, 5671,
  5679, 5689, 5716] : List Nat).map ofCode

theorem C_303_266_cert : certify C_303_266 303 266 = true := by decide +kernel

theorem C_303_266_isCode : IsCode C_303_266 303 266 := isCode_of_certify _ _ _ C_303_266_cert

/-- generator-matrix columns of the new `[565, 4, 500]_9` code (base-9 codes, see `ofCode`) -/
def C_565_500 : List Vec4 := ([
  1, 9, 10, 28, 55, 64, 82, 90, 91, 118, 127, 109, 154, 163, 171, 172, 181, 199, 208, 190,
  235, 226, 333, 334, 361, 370, 397, 379, 388, 406, 414, 415, 424, 442, 451, 478, 460, 469, 244, 262,
  280, 289, 271, 298, 649, 657, 667, 685, 676, 721, 703, 712, 487, 495, 496, 523, 532, 514, 559, 541,
  550, 576, 604, 595, 622, 729, 730, 738, 766, 775, 757, 802, 810, 829, 856, 838, 892, 900, 910, 928,
  919, 946, 955, 1054, 1062, 1063, 1072, 1090, 1099, 1126, 1108, 1117, 1135, 1143, 1144, 1153, 1171, 1207, 1198, 973,
  982, 1009, 1018, 1000, 1045, 1036, 1378, 1386, 1387, 1396, 1414, 1405, 1450, 1432, 1216, 1234, 1252, 1261, 1243, 1270,
  1305, 1306, 1315, 1333, 1342, 1324, 1369, 1351, 1360, 1468, 1477, 1495, 1504, 1486, 1531, 1539, 1549, 1558, 1576, 1585,
  1567, 1612, 1629, 1630, 1639, 1666, 1648, 1693, 1819, 1810, 1872, 1873, 1882, 1900, 1909, 1936, 1918, 1710, 1711, 1720,
  1738, 1747, 1774, 1765, 2115, 2116, 2125, 2143, 2152, 2134, 2170, 1954, 1963, 1981, 1990, 1972, 2017, 2035, 2071, 2053,
  2098, 2089, 2917, 2925, 2926, 2935, 2944, 2971, 3006, 3016, 3034, 3070, 3052, 3061, 3079, 3087, 3088, 3097, 3115, 3124,
  3106, 3151, 3133, 3250, 3259, 3277, 3286, 3268, 3313, 3304, 3330, 3331, 3358, 3367, 3376, 3385, 3160, 3168, 3169, 3178,
  3205, 3187, 3232, 3565, 3573, 3574, 3583, 3601, 3592, 3619, 3403, 3421, 3439, 3448, 3430, 3475, 3457, 3484, 3492, 3493,
  3502, 3520, 3529, 3511, 3556, 3538, 3646, 3655, 3664, 3682, 3691, 3673, 3718, 3700, 3726, 3727, 3735, 3736, 3745, 3754,
  3799, 3781, 3817, 3826, 3853, 3835, 3880, 3862, 3871, 3970, 3978, 3979, 3988, 4006, 4015, 3997, 4042, 4033, 4051, 4059,
  4060, 4087, 4123, 4114, 3897, 3898, 3925, 3952, 4294, 4302, 4303, 4312, 4339, 4321, 4366, 4348, 4357, 4141, 4150, 4168,
  4177, 4159, 4195, 4213, 4221, 4249, 4258, 4240, 4285, 4276, 2188, 2196, 2197, 2206, 2224, 2233, 2215, 2260, 2268, 2269,
  2277, 2287, 2314, 2341, 2332, 2350, 2359, 2386, 2395, 2377, 2404, 2413, 2512, 2520, 2557, 2539, 2566, 2575, 2593, 2611,
  2629, 2638, 2620, 2665, 2647, 2656, 2440, 2449, 2476, 2458, 2503, 2485, 2836, 2845, 2872, 2881, 2863, 2908, 2899, 2674,
  2683, 2692, 2710, 2737, 2755, 2763, 2764, 2791, 2827, 2809, 2818, 5833, 5841, 5842, 5851, 5878, 5905, 5887, 5913, 5914,
  5922, 5932, 5950, 5959, 5986, 5968, 5977, 5995, 6003, 6013, 6031, 6040, 6049, 6157, 6165, 6166, 6175, 6193, 6202, 6229,
  6211, 6220, 6247, 6256, 6274, 6283, 6292, 6076, 6084, 6094, 6112, 6121, 6103, 6148, 6139, 6481, 6489, 6499, 6508, 6553,
  6535, 6544, 6319, 6327, 6328, 6355, 6364, 6391, 6400, 6409, 6418, 6427, 6472, 6454, 6463, 4375, 4383, 4384, 4393, 4411,
  4420, 4402, 4447, 4438, 4464, 4474, 4492, 4483, 4528, 4510, 4537, 4545, 4546, 4555, 4582, 4564, 4609, 4591, 4699, 4707,
  4708, 4735, 4744, 4726, 4771, 4753, 4789, 4798, 4816, 4807, 4852, 4843, 4618, 4626, 4627, 4636, 4645, 4690, 4672, 4681,
  5023, 5031, 5059, 5086, 4861, 4870, 4879, 4897, 4933, 4915, 4924, 4942, 4950, 4951, 4987, 4969, 5014, 4996, 5005, 5104,
  5112, 5122, 5149, 5131, 5176, 5158, 5167, 5184, 5185, 5193, 5221, 5230, 5212, 5248, 5266, 5274, 5311, 5320, 5436, 5437,
  5446, 5464, 5473, 5500, 5482, 5509, 5517, 5518, 5527, 5554, 5536, 5581, 5563, 5572, 5347, 5355, 5356, 5365, 5383, 5392,
  5374, 5419, 5410, 5752, 5760, 5761, 5788, 5779, 5824, 5806, 5815, 5590, 5599, 5608, 5635, 5617, 5644, 5653, 5671, 5679,
  5689, 5716, 5698, 5725, 5734] : List Nat).map ofCode

theorem C_565_500_cert : certify C_565_500 565 500 = true := by decide +kernel

theorem C_565_500_isCode : IsCode C_565_500 565 500 := isCode_of_certify _ _ _ C_565_500_cert

/-- generator-matrix columns of the new `[292, 4, 256]_9` code (base-9 codes, see `ofCode`) -/
def C_292_256 : List Vec4 := ([
  1, 10, 37, 46, 28, 82, 90, 91, 118, 171, 208, 190, 217, 325, 334, 370, 352, 397, 379, 414,
  451, 460, 253, 262, 289, 271, 657, 487, 495, 496, 505, 550, 640, 729, 730, 802, 784, 793, 810, 892,
  901, 928, 919, 955, 1090, 1117, 1135, 1153, 1171, 1162, 1189, 973, 991, 1000, 1396, 1414, 1405, 1216, 1234, 1288,
  1270, 1279, 1333, 1324, 1351, 1467, 1504, 1531, 1549, 1576, 1630, 1657, 1684, 1792, 1828, 1810, 1855, 1837, 1873, 1882,
  1909, 1936, 1927, 2107, 2115, 2143, 2152, 2152, 2179, 2170, 1953, 1981, 2008, 2026, 2035, 2062, 2080, 2089, 2917, 2925,
  2935, 2962, 2989, 2980, 3043, 3025, 3088, 3124, 3151, 3241, 3249, 3286, 3268, 3304, 3322, 3330, 3349, 3385, 3160, 3168,
  3187, 3223, 3565, 3574, 3583, 3610, 3592, 3493, 3529, 3556, 3538, 3547, 3654, 3691, 3673, 3700, 3726, 3736, 3745, 3763,
  3772, 3754, 3799, 3978, 3979, 4006, 4015, 4024, 4033, 4060, 4069, 4078, 4114, 3889, 3952, 4302, 4366, 4140, 4141, 4150,
  4168, 4186, 4195, 4221, 4222, 4231, 4258, 4240, 2233, 2242, 2269, 2287, 2341, 2350, 2358, 2386, 2404, 2593, 2620, 2665,
  2476, 2485, 2845, 2872, 2881, 2899, 2674, 2692, 2710, 2719, 2701, 2746, 2764, 2791, 2827, 2809, 2818, 5869, 5896, 5913,
  5914, 5922, 5923, 5932, 5959, 5941, 5968, 6004, 6013, 6031, 6022, 6058, 6165, 6220, 6247, 6256, 6274, 6283, 6084, 6121,
  6130, 6139, 6481, 6526, 6544, 6364, 6346, 6373, 6436, 6436, 4383, 4464, 4474, 4528, 4519, 4537, 4545, 4573, 4591, 4699,
  4753, 4789, 4825, 4852, 4834, 4636, 4654, 4645, 4681, 5023, 5041, 5059, 5050, 4950, 4951, 5005, 5104, 5113, 5122, 5176,
  5158, 5185, 5193, 5221, 5230, 5212, 5239, 5266, 5274, 5293, 5436, 5437, 5464, 5455, 5500, 5482, 5491, 5517, 5347, 5355,
  5761, 5770, 5788, 5779, 5590, 5617, 5662, 5644, 5653, 5679, 5743, 5725] : List Nat).map ofCode

theorem C_292_256_cert : certify C_292_256 292 256 = true := by decide +kernel

theorem C_292_256_isCode : IsCode C_292_256 292 256 := isCode_of_certify _ _ _ C_292_256_cert

/-- generator-matrix columns of the new `[333, 4, 292]_9` code (base-9 codes, see `ofCode`) -/
def C_333_292 : List Vec4 := ([
  1, 10, 28, 55, 64, 81, 90, 91, 100, 118, 171, 172, 199, 208, 235, 226, 325, 334, 343, 352,
  415, 424, 442, 451, 460, 316, 298, 307, 712, 487, 496, 532, 550, 568, 576, 586, 595, 640, 622, 631,
  729, 738, 757, 802, 784, 829, 856, 865, 892, 910, 964, 946, 1099, 1135, 1143, 1153, 1198, 1045, 1378, 1386,
  1387, 1450, 1224, 1252, 1261, 1243, 1288, 1279, 1297, 1351, 1477, 1495, 1504, 1531, 1522, 1548, 1612, 1603, 1657, 1648,
  1783, 1819, 1810, 1855, 1846, 1864, 1872, 1873, 1882, 1909, 1918, 1927, 1702, 1711, 2116, 2125, 2179, 2170, 1945, 1999,
  2044, 2098, 2080, 2917, 2953, 2962, 2989, 2998, 3006, 3025, 3061, 3087, 3133, 3249, 3250, 3313, 3330, 3340, 3367, 3385,
  3169, 3574, 3583, 3619, 3628, 3421, 3439, 3430, 3457, 3492, 3502, 3556, 3547, 3654, 3664, 3682, 3700, 3709, 3736, 3745,
  3763, 3799, 3781, 3790, 3808, 3816, 3817, 3844, 3880, 3862, 3997, 4024, 4033, 4059, 4060, 4069, 4087, 3907, 4294, 4302,
  4303, 4330, 4339, 4321, 4141, 4177, 4204, 4186, 4213, 4231, 4258, 4240, 4285, 4276, 2196, 2206, 2224, 2233, 2260, 2269,
  2277, 2278, 2296, 2350, 2368, 2386, 2395, 2404, 2413, 2512, 2520, 2530, 2557, 2539, 2584, 2566, 2620, 2665, 2656, 2431,
  2439, 2494, 2836, 2854, 2872, 2863, 2908, 2899, 2682, 2692, 2719, 2746, 2728, 2763, 2791, 2800, 2827, 5878, 5860, 5905,
  5887, 5896, 5922, 5923, 5932, 5977, 6013, 6040, 6022, 6058, 6165, 6193, 6202, 6229, 6211, 6220, 6238, 6247, 6256, 6265,
  6292, 6301, 6084, 6085, 6112, 6489, 6508, 6535, 6355, 6364, 6382, 6400, 6408, 6409, 6418, 6427, 6454, 4375, 4384, 4402,
  4447, 4455, 4456, 4465, 4474, 4492, 4528, 4510, 4545, 4555, 4564, 4609, 4591, 4707, 4717, 4744, 4753, 4762, 4825, 4834,
  4618, 4626, 4663, 5031, 5032, 5068, 5050, 5095, 5086, 4861, 4869, 4870, 4897, 4888, 4924, 4950, 4978, 4987, 4996, 5112,
  5113, 5140, 5184, 5193, 5203, 5230, 5257, 5239, 5248, 5266, 5311, 5338, 5437, 5446, 5473, 5491, 5554, 5536, 5581, 5374,
  5410, 5752, 5770, 5788, 5806, 5608, 5635, 5617, 5662, 5644, 5680, 5689, 5698] : List Nat).map ofCode

theorem C_333_292_cert : certify C_333_292 333 292 = true := by decide +kernel

theorem C_333_292_isCode : IsCode C_333_292 333 292 := isCode_of_certify _ _ _ C_333_292_cert

/-- generator-matrix columns of the new `[382, 4, 336]_9` code (base-9 codes, see `ofCode`) -/
def C_382_336 : List Vec4 := ([
  9, 10, 19, 37, 28, 73, 64, 82, 100, 118, 127, 145, 171, 235, 217, 226, 325, 361, 352, 388,
  415, 424, 451, 433, 460, 253, 280, 289, 316, 298, 657, 658, 685, 712, 495, 523, 532, 514, 541, 550,
  586, 604, 622, 730, 738, 748, 802, 784, 793, 820, 883, 874, 901, 910, 928, 937, 955, 1054, 1062, 1063,
  1090, 1099, 1135, 1144, 1162, 1207, 1189, 991, 1018, 1045, 1036, 1386, 1387, 1423, 1450, 1441, 1225, 1234, 1261, 1243,
  1270, 1297, 1305, 1306, 1315, 1333, 1342, 1369, 1351, 1467, 1477, 1495, 1486, 1531, 1513, 1548, 1549, 1558, 1585, 1567,
  1612, 1594, 1603, 1630, 1657, 1666, 1693, 1675, 1791, 1792, 1801, 1819, 1872, 1891, 1918, 1927, 1702, 1774, 1756, 1765,
  2107, 2115, 2116, 2125, 2134, 2179, 2170, 1954, 1981, 2008, 2034, 2035, 2062, 2071, 2053, 2098, 2089, 2926, 2953, 2989,
  3007, 3016, 3088, 3097, 3249, 3259, 3277, 3286, 3304, 3358, 3367, 3349, 3385, 3160, 3169, 3205, 3187, 3232, 3583, 3610,
  3628, 3439, 3492, 3493, 3529, 3538, 3646, 3655, 3664, 3682, 3691, 3673, 3700, 3745, 3754, 3790, 3808, 3816, 3826, 3844,
  3835, 3862, 3979, 3988, 4015, 3997, 4069, 4087, 4096, 4123, 3897, 3925, 3943, 3952, 4303, 4330, 4366, 4132, 4140, 4141,
  4177, 4159, 4186, 4221, 4222, 4249, 4240, 4267, 4276, 2188, 2197, 2224, 2242, 2278, 2305, 2314, 2296, 2323, 2332, 2359,
  2368, 2386, 2377, 2404, 2413, 2512, 2530, 2584, 2593, 2601, 2602, 2629, 2439, 2476, 2872, 2863, 2908, 2674, 2682, 2683,
  2710, 2719, 2791, 2800, 2818, 5833, 5878, 5905, 5887, 5896, 5914, 5922, 5950, 5941, 5986, 5977, 6004, 6031, 6031, 6067,
  6049, 6058, 6157, 6165, 6166, 6229, 6256, 6274, 6283, 6310, 6292, 6301, 6076, 6084, 6112, 6121, 6103, 6481, 6489, 6517,
  6526, 6508, 6553, 6544, 6391, 6373, 6400, 6408, 6409, 6427, 6454, 6463, 4375, 4384, 4393, 4447, 4438, 4465, 4492, 4501,
  4528, 4510, 4519, 4545, 4546, 4582, 4591, 4600, 4699, 4708, 4717, 4744, 4726, 4771, 4762, 4780, 4788, 4789, 4816, 4825,
  4807, 4852, 4843, 4618, 4690, 5032, 5050, 5077, 5086, 4879, 4906, 4933, 4950, 4978, 4987, 4969, 4996, 5112, 5140, 5167,
  5184, 5185, 5194, 5221, 5212, 5239, 5275, 5284, 5311, 5293, 5338, 5329, 5473, 5455, 5500, 5491, 5509, 5517, 5545, 5554,
  5563, 5572, 5347, 5355, 5356, 5374, 5401, 5410, 5760, 5797, 5590, 5635, 5617, 5644, 5653, 5679, 5680, 5689, 5707, 5716,
  5698, 5734] : List Nat).map ofCode

theorem C_382_336_cert : certify C_382_336 382 336 = true := by decide +kernel

theorem C_382_336_isCode : IsCode C_382_336 382 336 := isCode_of_certify _ _ _ C_382_336_cert

/-- generator-matrix columns of the new `[220, 4, 192]_9` code (base-9 codes, see `ofCode`) -/
def C_220_192 : List Vec4 := ([
  9, 46, 28, 73, 55, 81, 82, 91, 154, 171, 190, 333, 361, 397, 388, 406, 433, 478, 460, 252,
  658, 667, 685, 676, 523, 577, 613, 631, 738, 793, 810, 811, 856, 838, 910, 937, 1054, 1062, 1081, 1144,
  1171, 973, 991, 1045, 1386, 1405, 1441, 1216, 1224, 1261, 1288, 1342, 1360, 1504, 1486, 1513, 1522, 1540, 1548, 1567,
  1630, 1791, 1792, 1846, 1864, 1872, 1882, 1927, 1747, 1756, 2116, 2125, 1999, 2062, 2071, 2089, 2962, 2980, 2998, 3006,
  3070, 3087, 3088, 3097, 3151, 3133, 3250, 3322, 3331, 3367, 3349, 3160, 3205, 3573, 3583, 3601, 3610, 3637, 3421, 3430,
  3466, 3538, 3664, 3673, 3709, 3727, 3745, 3781, 3808, 3880, 3979, 3997, 4059, 4069, 4087, 4078, 4294, 4339, 4321, 4366,
  4357, 4168, 4186, 2215, 2260, 2242, 2278, 2395, 2422, 2512, 2520, 2521, 2611, 2656, 2431, 2503, 2485, 2845, 2881, 2899,
  2692, 2746, 2728, 2755, 2800, 2809, 2818, 5878, 5860, 5905, 5896, 5923, 5950, 5941, 6013, 6031, 6067, 6049, 6157, 6229,
  6211, 6246, 6247, 6310, 6301, 6084, 6112, 6139, 6517, 6327, 6337, 6373, 6409, 4393, 4420, 4447, 4429, 4455, 4464, 4474,
  4528, 4537, 4545, 4546, 4555, 4591, 4717, 4726, 4771, 4753, 4789, 4834, 4618, 5095, 4861, 4888, 4924, 4942, 4951, 5112,
  5184, 5194, 5230, 5212, 5311, 5329, 5428, 5455, 5491, 5517, 5536, 5563, 5752, 5760, 5770, 5779, 5653, 5689, 5743, 5734] : List Nat).map ofCode

theorem C_220_192_cert : certify C_220_192 220 192 = true := by decide +kernel

theorem C_220_192_isCode : IsCode C_220_192 220 192 := isCode_of_certify _ _ _ C_220_192_cert

/-- generator-matrix columns of the new `[277, 4, 243]_9` code (base-9 codes, see `ofCode`) -/
def C_277_243 : List Vec4 := ([
  9, 28, 73, 90, 109, 199, 235, 217, 226, 325, 334, 343, 361, 424, 442, 451, 478, 280, 271, 316,
  307, 658, 541, 550, 586, 640, 622, 631, 730, 757, 802, 819, 829, 856, 883, 874, 919, 946, 955, 1117,
  1207, 982, 991, 1009, 1045, 1386, 1387, 1396, 1450, 1441, 1252, 1243, 1279, 1297, 1315, 1342, 1468, 1495, 1486, 1531,
  1522, 1540, 1558, 1612, 1639, 1657, 1666, 1675, 1783, 1791, 1828, 1855, 1846, 1864, 1872, 1882, 1909, 1927, 1720, 1747,
  1774, 1756, 2143, 2161, 2170, 1999, 2026, 2044, 2098, 2080, 2925, 2953, 2989, 2980, 3006, 3043, 3025, 3052, 3151, 3249,
  3259, 3286, 3268, 3313, 3330, 3340, 3367, 3376, 3385, 3168, 3169, 3187, 3214, 3223, 3601, 3592, 3628, 3439, 3430, 3457,
  3492, 3520, 3654, 3682, 3700, 3709, 3736, 3745, 3763, 3790, 3817, 3844, 3988, 4015, 4024, 4033, 4069, 4087, 4096, 4105,
  3889, 3907, 3934, 3943, 4302, 4303, 4330, 4321, 4357, 4177, 4159, 4186, 4221, 4222, 4231, 4285, 4276, 2196, 2260, 2269,
  2277, 2332, 2350, 2368, 2395, 2404, 2520, 2530, 2557, 2539, 2566, 2638, 2620, 2431, 2458, 2503, 2836, 2854, 2908, 2899,
  2719, 2763, 2800, 2809, 5860, 5887, 5896, 5923, 5932, 5986, 5977, 6004, 6013, 6022, 6058, 6165, 6193, 6229, 6238, 6256,
  6274, 6301, 6094, 6103, 6148, 6130, 6481, 6499, 6508, 6544, 6328, 6364, 6382, 6408, 6409, 6418, 6436, 6454, 4411, 4402,
  4465, 4474, 4492, 4501, 4573, 4591, 4600, 4699, 4707, 4708, 4744, 4798, 4807, 4834, 4645, 5031, 5068, 5050, 4906, 4924,
  4950, 4951, 4978, 4969, 5112, 5140, 5193, 5203, 5230, 5212, 5248, 5266, 5284, 5338, 5320, 5428, 5473, 5500, 5518, 5545,
  5581, 5401, 5760, 5770, 5788, 5797, 5806, 5590, 5598, 5635, 5617, 5644, 5653, 5671, 5680, 5689, 5725] : List Nat).map ofCode

theorem C_277_243_cert : certify C_277_243 277 243 = true := by decide +kernel

theorem C_277_243_isCode : IsCode C_277_243 277 243 := isCode_of_certify _ _ _ C_277_243_cert

/-- generator-matrix columns of the new `[318, 4, 279]_9` code (base-9 codes, see `ofCode`) -/
def C_318_279 : List Vec4 := ([
  10, 19, 46, 28, 82, 90, 154, 163, 199, 235, 217, 226, 325, 334, 343, 361, 397, 379, 388, 406,
  415, 424, 442, 451, 433, 252, 316, 316, 316, 694, 703, 541, 550, 586, 604, 595, 640, 622, 631, 766,
  757, 802, 810, 820, 856, 838, 883, 892, 946, 1063, 1090, 1162, 1189, 1386, 1387, 1396, 1414, 1405, 1450, 1224,
  1252, 1261, 1270, 1279, 1297, 1305, 1324, 1360, 1459, 1468, 1495, 1531, 1513, 1522, 1576, 1612, 1594, 1629, 1657, 1684,
  1783, 1828, 1855, 1837, 1846, 1864, 1872, 1873, 1882, 1909, 1936, 1927, 1710, 2115, 2179, 2170, 1954, 1981, 1972, 1999,
  2026, 2034, 2035, 2044, 2062, 2098, 2080, 2917, 2926, 2953, 2944, 2989, 3006, 3007, 3034, 3025, 3070, 3088, 3106, 3241,
  3249, 3313, 3330, 3340, 3358, 3367, 3394, 3376, 3385, 3168, 3592, 3411, 3421, 3439, 3430, 3484, 3492, 3529, 3664, 3700,
  3709, 3736, 3745, 3763, 3754, 3781, 3790, 3817, 3826, 3844, 3835, 3970, 3978, 3988, 4042, 4024, 4033, 4087, 4123, 4105,
  4114, 4302, 4303, 4330, 4321, 4366, 4357, 4132, 4141, 4177, 4186, 4195, 4221, 4222, 4231, 4258, 4285, 4276, 2197, 2260,
  2269, 2277, 2314, 2323, 2350, 2368, 2395, 2377, 2404, 2520, 2521, 2530, 2557, 2539, 2566, 2601, 2602, 2629, 2620, 2439,
  2836, 2854, 2908, 2890, 2899, 2674, 2719, 2763, 2764, 2800, 2782, 5869, 5860, 5905, 5887, 5922, 5923, 5932, 5959, 5941,
  5986, 5977, 5995, 6004, 6013, 6031, 6022, 6067, 6058, 6165, 6166, 6175, 6193, 6229, 6238, 6256, 6274, 6265, 6301, 6517,
  6508, 6327, 6364, 6373, 6382, 6409, 6418, 6445, 6427, 6454, 6463, 4411, 4402, 4455, 4456, 4465, 4474, 4492, 4501, 4573,
  4707, 4744, 4753, 4780, 4788, 4789, 4834, 5041, 5068, 5050, 5077, 4861, 4879, 4933, 4924, 4942, 4950, 4978, 5014, 5005,
  5104, 5140, 5158, 5167, 5185, 5193, 5203, 5221, 5230, 5239, 5248, 5266, 5284, 5302, 5338, 5329, 5500, 5509, 5581, 5563,
  5572, 5761, 5770, 5788, 5797, 5779, 5824, 5806, 5590, 5599, 5626, 5635, 5617, 5644, 5671, 5680, 5707, 5743] : List Nat).map ofCode

theorem C_318_279_cert : certify C_318_279 318 279 = true := by decide +kernel

theorem C_318_279_isCode : IsCode C_318_279 318 279 := isCode_of_certify _ _ _ C_318_279_cert

/-- generator-matrix columns of the new `[422, 4, 372]_9` code (base-9 codes, see `ofCode`) -/
def C_422_372 : List Vec4 := ([
  1, 9, 10, 37, 28, 64, 90, 100, 109, 154, 136, 145, 171, 181, 226, 397, 379, 388, 414, 415,
  244, 252, 262, 271, 298, 307, 657, 658, 667, 721, 495, 523, 514, 559, 550, 568, 577, 640, 730, 748,
  766, 802, 793, 819, 829, 847, 838, 883, 865, 874, 892, 900, 937, 919, 964, 1126, 1108, 1117, 1135, 1143,
  1153, 1171, 1207, 1189, 1198, 1009, 1000, 1045, 1378, 1396, 1414, 1423, 1405, 1432, 1441, 1234, 1243, 1288, 1270, 1315,
  1333, 1324, 1351, 1360, 1468, 1477, 1495, 1531, 1540, 1548, 1558, 1576, 1585, 1603, 1629, 1639, 1657, 1648, 1693, 1791,
  1801, 1810, 1837, 1837, 1846, 1873, 1882, 1900, 1891, 1936, 1927, 1702, 1710, 1711, 1720, 1738, 1747, 2107, 2116, 2125,
  2143, 2152, 2179, 2170, 1945, 1963, 1990, 1972, 2017, 2026, 2034, 2062, 2925, 2926, 2935, 2953, 2944, 2971, 3006, 3007,
  3016, 3034, 3043, 3079, 3087, 3115, 3133, 3142, 3241, 3249, 3268, 3295, 3331, 3340, 3358, 3367, 3376, 3168, 3169, 3178,
  3196, 3205, 3214, 3573, 3574, 3592, 3628, 3411, 3412, 3439, 3448, 3430, 3457, 3466, 3484, 3492, 3493, 3502, 3529, 3538,
  3654, 3664, 3691, 3673, 3718, 3700, 3726, 3727, 3735, 3745, 3817, 3826, 3853, 3970, 3978, 3988, 4015, 4024, 4051, 4059,
  4060, 4069, 4078, 4123, 4105, 4114, 3889, 3897, 3934, 3961, 3943, 3952, 4302, 4303, 4312, 4339, 4321, 4348, 4357, 4132,
  4141, 4177, 4159, 4204, 4186, 4213, 4231, 4258, 4240, 4267, 2196, 2206, 2215, 2260, 2242, 2251, 2277, 2278, 2287, 2305,
  2296, 2341, 2323, 2368, 2377, 2422, 2404, 2557, 2539, 2584, 2575, 2601, 2602, 2611, 2629, 2665, 2647, 2439, 2440, 2467,
  2458, 2503, 2485, 2494, 2845, 2872, 2881, 2908, 2899, 2682, 2683, 2710, 2719, 2701, 2728, 2773, 2782, 2818, 5833, 5841,
  5842, 5869, 5905, 5887, 5896, 5913, 5923, 5950, 5941, 5986, 5968, 5977, 5995, 6003, 6031, 6040, 6058, 6157, 6165, 6202,
  6184, 6229, 6246, 6247, 6283, 6265, 6310, 6084, 6085, 6103, 6148, 6130, 6139, 6490, 6508, 6535, 6319, 6327, 6328, 6355,
  6346, 6391, 6373, 6408, 6409, 6436, 6445, 6472, 6463, 4384, 4393, 4411, 4455, 4456, 4464, 4501, 4483, 4528, 4510, 4537,
  4545, 4546, 4573, 4582, 4564, 4707, 4717, 4744, 4771, 4780, 4789, 4798, 4816, 4807, 4834, 4618, 4626, 4627, 4636, 4654,
  4663, 4645, 4690, 5023, 5031, 5032, 5041, 5068, 5050, 5095, 4869, 4870, 4897, 4933, 4951, 4978, 4987, 5014, 4996, 5104,
  5140, 5158, 5167, 5185, 5194, 5203, 5221, 5230, 5248, 5275, 5284, 5302, 5338, 5320, 5329, 5428, 5446, 5482, 5491, 5518,
  5527, 5545, 5554, 5572, 5356, 5365, 5383, 5401, 5752, 5761, 5770, 5788, 5797, 5599, 5608, 5635, 5662, 5644, 5653, 5671,
  5707, 5743] : List Nat).map ofCode

theorem C_422_372_cert : certify C_422_372 422 372 = true := by decide +kernel

theorem C_422_372_isCode : IsCode C_422_372 422 372 := isCode_of_certify _ _ _ C_422_372_cert

/-- generator-matrix columns of the new `[426, 4, 375]_9` code (base-9 codes, see `ofCode`) -/
def C_426_375 : List Vec4 := ([
  1, 9, 10, 19, 28, 55, 64, 90, 91, 127, 154, 145, 163, 171, 172, 199, 208, 190, 235, 352,
  379, 388, 415, 424, 478, 460, 253, 262, 271, 316, 298, 649, 657, 658, 685, 721, 487, 496, 505, 523,
  532, 514, 550, 576, 586, 604, 613, 595, 640, 622, 631, 729, 730, 739, 748, 775, 757, 784, 810, 847,
  856, 865, 874, 892, 901, 928, 964, 955, 1054, 1062, 1081, 1108, 1117, 1143, 1171, 1180, 1189, 1198, 973, 981,
  982, 991, 1009, 1386, 1387, 1423, 1224, 1225, 1252, 1261, 1279, 1297, 1306, 1315, 1342, 1324, 1360, 1477, 1504, 1531,
  1513, 1522, 1539, 1540, 1548, 1558, 1576, 1585, 1612, 1594, 1630, 1639, 1792, 1819, 1810, 1855, 1837, 1846, 1864, 1872,
  1873, 1882, 1909, 1891, 1936, 1927, 1702, 1710, 1711, 1738, 1729, 1774, 2116, 2143, 2152, 2134, 2179, 1963, 2017, 1999,
  2008, 2035, 2044, 2071, 2053, 2098, 2080, 2917, 2926, 2935, 2953, 2962, 2980, 2997, 2998, 3043, 3025, 3052, 3061, 3079,
  3124, 3151, 3142, 3249, 3259, 3277, 3330, 3331, 3340, 3358, 3367, 3349, 3385, 3178, 3187, 3214, 3223, 3573, 3601, 3610,
  3403, 3421, 3439, 3448, 3475, 3466, 3484, 3492, 3493, 3556, 3538, 3655, 3664, 3691, 3673, 3718, 3700, 3726, 3727, 3736,
  3745, 3763, 3754, 3781, 3790, 3816, 3844, 3853, 3880, 3862, 4006, 4033, 4051, 4059, 4060, 4087, 4096, 3889, 3897, 3925,
  3934, 3943, 4294, 4303, 4339, 4321, 4366, 4348, 4132, 4140, 4141, 4150, 4159, 4204, 4186, 4213, 4231, 4249, 4258, 4276,
  2224, 2233, 2260, 2251, 2268, 2269, 2278, 2287, 2305, 2314, 2296, 2358, 2368, 2386, 2395, 2404, 2413, 2512, 2520, 2530,
  2557, 2539, 2584, 2593, 2611, 2629, 2620, 2665, 2656, 2439, 2449, 2467, 2458, 2485, 2494, 2836, 2854, 2872, 2863, 2899,
  2682, 2719, 2701, 2746, 2728, 2764, 2773, 2791, 2800, 2827, 2818, 5833, 5841, 5860, 5905, 5887, 5914, 5922, 5923, 5932,
  5959, 5968, 5977, 5995, 6003, 6040, 6067, 6165, 6202, 6184, 6229, 6220, 6238, 6256, 6265, 6310, 6292, 6085, 6094, 6121,
  6103, 6148, 6489, 6499, 6526, 6319, 6328, 6337, 6355, 6391, 6382, 6400, 6418, 6436, 6427, 4375, 4384, 4393, 4402, 4447,
  4429, 4438, 4455, 4456, 4464, 4474, 4492, 4483, 4528, 4545, 4546, 4600, 4699, 4707, 4735, 4771, 4753, 4762, 4780, 4788,
  4789, 4798, 4816, 4807, 4834, 4618, 4626, 4654, 4690, 4672, 4681, 5023, 5032, 5050, 5086, 4861, 4869, 4870, 4879, 4897,
  4888, 4924, 4950, 4951, 4978, 4987, 4969, 4996, 5122, 5140, 5149, 5131, 5184, 5193, 5203, 5212, 5257, 5239, 5274, 5275,
  5338, 5428, 5436, 5464, 5517, 5518, 5545, 5554, 5536, 5581, 5419, 5410, 5752, 5760, 5761, 5824, 5598, 5608, 5626, 5635,
  5617, 5662, 5680, 5698, 5725, 5734] : List Nat).map ofCode

theorem C_426_375_cert : certify C_426_375 426 375 = true := by decide +kernel

theorem C_426_375_isCode : IsCode C_426_375 426 375 := isCode_of_certify _ _ _ C_426_375_cert

/-- generator-matrix columns of the new `[473, 4, 417]_9` code (base-9 codes, see `ofCode`) -/
def C_473_417 : List Vec4 := ([
  1, 9, 37, 28, 73, 55, 64, 82, 90, 100, 118, 127, 109, 154, 136, 145, 199, 190, 235, 370,
  352, 379, 424, 433, 478, 469, 253, 280, 289, 271, 298, 649, 657, 658, 685, 721, 703, 712, 496, 505,
  523, 514, 559, 550, 576, 586, 613, 640, 622, 631, 729, 730, 739, 748, 775, 757, 784, 793, 811, 819,
  847, 856, 865, 874, 900, 928, 919, 955, 1054, 1062, 1063, 1099, 1081, 1108, 1117, 1135, 1143, 1144, 1153, 1171,
  1180, 1162, 1207, 1189, 973, 981, 982, 991, 1009, 1018, 1386, 1387, 1423, 1405, 1432, 1441, 1225, 1234, 1252, 1288,
  1270, 1279, 1297, 1305, 1306, 1315, 1342, 1324, 1351, 1360, 1468, 1477, 1486, 1531, 1513, 1522, 1539, 1540, 1558, 1576,
  1585, 1612, 1594, 1603, 1630, 1639, 1666, 1648, 1675, 1791, 1792, 1855, 1846, 1864, 1872, 1882, 1909, 1891, 1927, 1702,
  1710, 1711, 1720, 1747, 1774, 2143, 2134, 2161, 1953, 1963, 2017, 1999, 2008, 2035, 2044, 2071, 2098, 2080, 2925, 2926,
  2935, 2953, 2962, 2971, 2980, 2997, 3007, 3016, 3043, 3025, 3070, 3052, 3061, 3079, 3087, 3124, 3106, 3151, 3133, 3142,
  3249, 3250, 3259, 3277, 3286, 3268, 3330, 3340, 3358, 3367, 3349, 3385, 3168, 3178, 3187, 3232, 3214, 3223, 3573, 3574,
  3601, 3610, 3637, 3403, 3412, 3439, 3448, 3475, 3466, 3484, 3492, 3493, 3502, 3520, 3529, 3511, 3538, 3547, 3646, 3655,
  3691, 3673, 3718, 3700, 3726, 3727, 3736, 3745, 3763, 3790, 3808, 3844, 3862, 3871, 3979, 4006, 4015, 4042, 4033, 4051,
  4059, 4060, 4087, 4096, 4078, 3889, 3897, 3925, 3934, 3943, 3952, 4303, 4321, 4348, 4132, 4140, 4150, 4168, 4159, 4204,
  4186, 4213, 4231, 4249, 4276, 2224, 2260, 2251, 2268, 2269, 2278, 2287, 2314, 2296, 2341, 2323, 2332, 2358, 2359, 2368,
  2386, 2395, 2404, 2520, 2530, 2548, 2557, 2539, 2584, 2602, 2611, 2629, 2638, 2620, 2665, 2647, 2656, 2440, 2449, 2449,
  2467, 2458, 2503, 2494, 2836, 2844, 2854, 2881, 2863, 2899, 2682, 2719, 2701, 2728, 2755, 2764, 2773, 2791, 2800, 2782,
  2827, 2809, 5833, 5851, 5869, 5878, 5860, 5887, 5913, 5914, 5923, 5932, 5959, 5977, 5995, 6003, 6040, 6049, 6157, 6165,
  6202, 6229, 6211, 6238, 6246, 6256, 6310, 6292, 6085, 6094, 6103, 6148, 6130, 6481, 6489, 6499, 6526, 6535, 6544, 6319,
  6328, 6337, 6355, 6346, 6391, 6382, 6418, 6436, 6445, 6472, 4375, 4393, 4420, 4402, 4429, 4438, 4464, 4474, 4492, 4483,
  4528, 4537, 4545, 4546, 4609, 4600, 4699, 4707, 4708, 4771, 4780, 4788, 4789, 4798, 4816, 4825, 4807, 4834, 4618, 4654,
  4645, 4690, 4681, 5059, 5050, 5095, 5086, 4869, 4870, 4897, 4906, 4888, 4915, 4924, 4942, 4950, 4951, 4960, 4978, 4969,
  5014, 4996, 5122, 5140, 5149, 5131, 5184, 5185, 5193, 5194, 5203, 5212, 5274, 5275, 5302, 5293, 5338, 5320, 5428, 5436,
  5464, 5482, 5491, 5517, 5518, 5527, 5545, 5554, 5581, 5563, 5572, 5347, 5365, 5392, 5401, 5410, 5752, 5760, 5824, 5815,
  5590, 5598, 5608, 5626, 5635, 5617, 5653, 5679, 5680, 5716, 5698, 5725, 5734] : List Nat).map ofCode

theorem C_473_417_cert : certify C_473_417 473 417 = true := by decide +kernel

theorem C_473_417_isCode : IsCode C_473_417 473 417 := isCode_of_certify _ _ _ C_473_417_cert

/-- generator-matrix columns of the new `[553, 4, 489]_9` code (base-9 codes, see `ofCode`) -/
def C_553_489 : List Vec4 := ([
  9, 19, 37, 28, 55, 64, 81, 82, 90, 100, 127, 109, 154, 145, 163, 171, 172, 181, 199, 208,
  235, 217, 226, 325, 361, 370, 352, 397, 388, 415, 424, 451, 433, 478, 460, 244, 252, 280, 289, 271,
  316, 298, 307, 649, 657, 658, 685, 694, 676, 712, 495, 496, 523, 532, 514, 550, 568, 576, 577, 586,
  613, 595, 640, 622, 729, 738, 739, 748, 757, 784, 810, 829, 847, 856, 865, 892, 900, 901, 910, 928,
  964, 946, 955, 1063, 1072, 1090, 1099, 1081, 1108, 1117, 1135, 1143, 1171, 1180, 1162, 1189, 1198, 973, 981, 991,
  1018, 1045, 1027, 1036, 1378, 1386, 1387, 1396, 1414, 1423, 1432, 1441, 1216, 1224, 1225, 1234, 1261, 1243, 1288, 1270,
  1297, 1305, 1306, 1315, 1333, 1342, 1324, 1360, 1459, 1468, 1495, 1504, 1531, 1513, 1522, 1540, 1548, 1549, 1558, 1576,
  1594, 1603, 1621, 1629, 1630, 1639, 1648, 1693, 1675, 1684, 1783, 1819, 1828, 1837, 1864, 1872, 1882, 1909, 1891, 1918,
  1927, 1710, 1711, 1720, 1738, 1729, 1774, 1756, 1765, 2115, 2116, 2143, 2134, 2179, 2161, 1953, 1954, 1963, 1981, 1990,
  1972, 2008, 2026, 2034, 2035, 2044, 2062, 2053, 2080, 2089, 2917, 2925, 2935, 2953, 2962, 2989, 2971, 2980, 2997, 3006,
  3016, 3034, 3043, 3025, 3052, 3061, 3087, 3115, 3124, 3142, 3241, 3249, 3250, 3259, 3277, 3286, 3268, 3304, 3322, 3330,
  3331, 3340, 3358, 3376, 3385, 3160, 3196, 3205, 3187, 3232, 3214, 3574, 3583, 3601, 3592, 3637, 3619, 3628, 3411, 3412,
  3421, 3448, 3430, 3475, 3457, 3466, 3484, 3493, 3502, 3520, 3529, 3547, 3654, 3664, 3682, 3673, 3718, 3700, 3709, 3763,
  3772, 3754, 3799, 3781, 3808, 3816, 3826, 3853, 3835, 3880, 3862, 3871, 3979, 3988, 4006, 4015, 4024, 4033, 4059, 4060,
  4087, 4096, 4078, 4123, 4105, 3889, 3907, 3925, 3934, 3952, 4294, 4302, 4303, 4312, 4339, 4321, 4366, 4348, 4132, 4168,
  4177, 4204, 4186, 4195, 4213, 4222, 4249, 4240, 4285, 4267, 4276, 2224, 2233, 2215, 2260, 2251, 2268, 2269, 2277, 2287,
  2305, 2296, 2341, 2332, 2358, 2359, 2368, 2386, 2395, 2422, 2413, 2512, 2520, 2521, 2530, 2548, 2557, 2539, 2584, 2566,
  2601, 2638, 2620, 2431, 2439, 2440, 2449, 2467, 2476, 2458, 2485, 2494, 2845, 2854, 2872, 2881, 2908, 2890, 2899, 2674,
  2682, 2692, 2710, 2701, 2746, 2728, 2737, 2755, 2764, 2773, 2782, 2827, 2818, 5833, 5851, 5869, 5860, 5913, 5914, 5922,
  5923, 5959, 5941, 5968, 5977, 6004, 6013, 6031, 6040, 6022, 6049, 6165, 6166, 6175, 6193, 6184, 6211, 6220, 6238, 6246,
  6247, 6256, 6283, 6265, 6310, 6301, 6085, 6094, 6112, 6121, 6148, 6130, 6139, 6481, 6489, 6499, 6517, 6553, 6535, 6544,
  6327, 6328, 6337, 6355, 6364, 6346, 6391, 6400, 6408, 6436, 6445, 6427, 6472, 6454, 6463, 4375, 4383, 4393, 4411, 4420,
  4402, 4456, 4464, 4474, 4492, 4501, 4528, 4537, 4545, 4546, 4555, 4573, 4564, 4600, 4699, 4707, 4708, 4744, 4771, 4753,
  4762, 4780, 4789, 4798, 4852, 4834, 4618, 4626, 4627, 4645, 4690, 4681, 5031, 5032, 5059, 5068, 5050, 5095, 5077, 5086,
  4861, 4869, 4888, 4933, 4915, 4924, 4950, 4960, 4978, 4987, 4969, 4996, 5104, 5113, 5122, 5149, 5131, 5158, 5193, 5194,
  5203, 5230, 5212, 5275, 5284, 5302, 5311, 5293, 5320, 5329, 5428, 5437, 5464, 5473, 5500, 5482, 5491, 5509, 5517, 5527,
  5545, 5536, 5581, 5563, 5355, 5365, 5392, 5374, 5419, 5401, 5410, 5752, 5760, 5797, 5779, 5824, 5815, 5590, 5598, 5608,
  5626, 5635, 5617, 5662, 5644, 5653, 5679, 5680, 5689, 5716, 5743, 5725, 5734] : List Nat).map ofCode

theorem C_553_489_cert : certify C_553_489 553 489 = true := by decide +kernel

theorem C_553_489_isCode : IsCode C_553_489 553 489 := isCode_of_certify _ _ _ C_553_489_cert

/-- generator-matrix columns of the new `[265, 4, 232]_9` code (base-9 codes, see `ofCode`) -/
def C_265_232 : List Vec4 := ([
  10, 19, 46, 64, 90, 91, 163, 172, 199, 325, 333, 334, 343, 414, 424, 442, 451, 460, 244, 252,
  262, 280, 496, 505, 523, 559, 576, 622, 730, 748, 766, 784, 819, 856, 838, 865, 874, 892, 910, 937,
  955, 1072, 1090, 1081, 1143, 1171, 1414, 1405, 1450, 1441, 1216, 1234, 1261, 1279, 1305, 1306, 1342, 1324, 1369, 1459,
  1468, 1477, 1495, 1513, 1539, 1540, 1576, 1567, 1612, 1603, 1621, 1801, 1828, 1810, 1864, 1891, 1936, 1927, 1702, 1711,
  1738, 1729, 2107, 2115, 1953, 2008, 2026, 2034, 2044, 2080, 2925, 2926, 2935, 2971, 2980, 3006, 3034, 3151, 3133, 3249,
  3277, 3286, 3313, 3322, 3330, 3340, 3349, 3376, 3574, 3601, 3637, 3628, 3403, 3421, 3439, 3466, 3493, 3502, 3547, 3654,
  3691, 3726, 3735, 3736, 3763, 3772, 3799, 3781, 3808, 3826, 3844, 3880, 4060, 4069, 4087, 4078, 4123, 4105, 3898, 3907,
  3934, 3916, 3952, 4303, 4312, 4321, 4357, 4140, 4240, 4285, 2188, 2197, 2260, 2314, 2323, 2332, 2350, 2359, 2368, 2395,
  2404, 2520, 2575, 2602, 2431, 2467, 2476, 2503, 2836, 2881, 2908, 2890, 2701, 2791, 2800, 2782, 2827, 2818, 5841, 5851,
  5878, 5860, 5896, 5977, 5995, 6003, 6004, 6031, 6058, 6238, 6247, 6256, 6292, 6084, 6121, 6103, 6148, 6489, 6319, 6346,
  6391, 6382, 4429, 4456, 4465, 4483, 4528, 4555, 4573, 4591, 4699, 4735, 4771, 4789, 4798, 4843, 4626, 4627, 4636, 4645,
  4672, 5023, 5031, 5068, 5050, 5086, 4861, 4869, 4888, 4915, 4924, 4950, 4951, 5140, 5149, 5176, 5158, 5185, 5194, 5203,
  5221, 5257, 5266, 5274, 5275, 5293, 5329, 5436, 5509, 5517, 5518, 5572, 5347, 5355, 5392, 5419, 5401, 5797, 5608, 5626,
  5635, 5644, 5680, 5689, 5734] : List Nat).map ofCode

theorem C_265_232_cert : certify C_265_232 265 232 = true := by decide +kernel

theorem C_265_232_isCode : IsCode C_265_232 265 232 := isCode_of_certify _ _ _ C_265_232_cert

/-- **Main theorem (q = 9).** For each pair `(n, d)` below a linear `[n, 4, ≥ d]` code over GF(9)
exists. Each of these lengths is strictly smaller than the upper bound on `n_9(4,d)` in Maruta's table
(as of 2026-10-08):
  * `d = 190`: table `216 ≤ n ≤ 219`, new code of length `218`
  * `d = 191`: table `217 ≤ n ≤ 220`, new code of length `219`
  * `d = 192`: table `218 ≤ n ≤ 221`, new code of length `220`
  * `d = 194`: table `220 ≤ n ≤ 224`, new code of length `223`
  * `d = 195`: table `221 ≤ n ≤ 225`, new code of length `224`
  * `d = 196`: table `222 ≤ n ≤ 226`, new code of length `225`
  * `d = 197`: table `224 ≤ n ≤ 227`, new code of length `226`
  * `d = 198`: table `225 ≤ n ≤ 228`, new code of length `227`
  * `d = 199`: table `226 ≤ n ≤ 229`, new code of length `228`
  * `d = 200`: table `227 ≤ n ≤ 230`, new code of length `229`
  * `d = 231`: table `262 ≤ n ≤ 265`, new code of length `264`
  * `d = 232`: table `263 ≤ n ≤ 266`, new code of length `265`
  * `d = 241`: table `273 ≤ n ≤ 276`, new code of length `275`
  * `d = 242`: table `274 ≤ n ≤ 277`, new code of length `276`
  * `d = 243`: table `275 ≤ n ≤ 278`, new code of length `277`
  * `d = 253`: table `287 ≤ n ≤ 290`, new code of length `289`
  * `d = 254`: table `288 ≤ n ≤ 291`, new code of length `290`
  * `d = 255`: table `289 ≤ n ≤ 292`, new code of length `291`
  * `d = 256`: table `290 ≤ n ≤ 293`, new code of length `292`
  * `d = 262`: table `297 ≤ n ≤ 300`, new code of length `299`
  * `d = 263`: table `298 ≤ n ≤ 301`, new code of length `300`
  * `d = 264`: table `299 ≤ n ≤ 302`, new code of length `301`
  * `d = 265`: table `300 ≤ n ≤ 303`, new code of length `302`
  * `d = 266`: table `301 ≤ n ≤ 304`, new code of length `303`
  * `d = 267`: table `302 ≤ n ≤ 306`, new code of length `305`
  * `d = 268`: table `303 ≤ n ≤ 307`, new code of length `306`
  * `d = 269`: table `304 ≤ n ≤ 308`, new code of length `307`
  * `d = 270`: table `305 ≤ n ≤ 309`, new code of length `308`
  * `d = 271`: table `307 ≤ n ≤ 310`, new code of length `309`
  * `d = 272`: table `308 ≤ n ≤ 311`, new code of length `310`
  * `d = 273`: table `309 ≤ n ≤ 312`, new code of length `311`
  * `d = 274`: table `310 ≤ n ≤ 314`, new code of length `312`
  * `d = 275`: table `311 ≤ n ≤ 315`, new code of length `313`
  * `d = 276`: table `312 ≤ n ≤ 316`, new code of length `314`
  * `d = 277`: table `313 ≤ n ≤ 317`, new code of length `316`
  * `d = 278`: table `315 ≤ n ≤ 318`, new code of length `317`
  * `d = 279`: table `316 ≤ n ≤ 319`, new code of length `318`
  * `d = 289`: table `328 ≤ n ≤ 331`, new code of length `330`
  * `d = 290`: table `329 ≤ n ≤ 332`, new code of length `331`
  * `d = 291`: table `330 ≤ n ≤ 333`, new code of length `332`
  * `d = 292`: table `331 ≤ n ≤ 334`, new code of length `333`
  * `d = 298`: table `338 ≤ n ≤ 341`, new code of length `340`
  * `d = 299`: table `339 ≤ n ≤ 342`, new code of length `341`
  * `d = 300`: table `340 ≤ n ≤ 343`, new code of length `342`
  * `d = 301`: table `341 ≤ n ≤ 344`, new code of length `343`
  * `d = 302`: table `342 ≤ n ≤ 345`, new code of length `344`
  * `d = 303`: table `343 ≤ n ≤ 347`, new code of length `345`
  * `d = 304`: table `344 ≤ n ≤ 348`, new code of length `347`
  * `d = 305`: table `345 ≤ n ≤ 349`, new code of length `348`
  * `d = 306`: table `346 ≤ n ≤ 350`, new code of length `349`
  * `d = 307`: table `348 ≤ n ≤ 351`, new code of length `350`
  * `d = 308`: table `349 ≤ n ≤ 352`, new code of length `351`
  * `d = 309`: table `350 ≤ n ≤ 353`, new code of length `352`
  * `d = 310`: table `351 ≤ n ≤ 354`, new code of length `353`
  * `d = 311`: table `352 ≤ n ≤ 355`, new code of length `354`
  * `d = 312`: table `353 ≤ n ≤ 356`, new code of length `355`
  * `d = 333`: table `376 ≤ n ≤ 380`, new code of length `379`
  * `d = 334`: table `378 ≤ n ≤ 382`, new code of length `380`
  * `d = 335`: table `379 ≤ n ≤ 383`, new code of length `381`
  * `d = 336`: table `380 ≤ n ≤ 384`, new code of length `382`
  * `d = 337`: table `381 ≤ n ≤ 385`, new code of length `384`
  * `d = 338`: table `382 ≤ n ≤ 386`, new code of length `385`
  * `d = 339`: table `383 ≤ n ≤ 387`, new code of length `386`
  * `d = 340`: table `384 ≤ n ≤ 388`, new code of length `387`
  * `d = 341`: table `385 ≤ n ≤ 389`, new code of length `388`
  * `d = 342`: table `386 ≤ n ≤ 390`, new code of length `389`
  * `d = 343`: table `388 ≤ n ≤ 392`, new code of length `390`
  * `d = 344`: table `389 ≤ n ≤ 393`, new code of length `392`
  * `d = 345`: table `390 ≤ n ≤ 394`, new code of length `393`
  * `d = 346`: table `391 ≤ n ≤ 395`, new code of length `394`
  * `d = 347`: table `392 ≤ n ≤ 396`, new code of length `395`
  * `d = 348`: table `393 ≤ n ≤ 397`, new code of length `396`
  * `d = 349`: table `394 ≤ n ≤ 398`, new code of length `397`
  * `d = 350`: table `396 ≤ n ≤ 399`, new code of length `398`
  * `d = 351`: table `397 ≤ n ≤ 400`, new code of length `399`
  * `d = 352`: table `398 ≤ n ≤ 401`, new code of length `400`
  * `d = 353`: table `399 ≤ n ≤ 402`, new code of length `401`
  * `d = 354`: table `400 ≤ n ≤ 403`, new code of length `402`
  * `d = 355`: table `401 ≤ n ≤ 404`, new code of length `403`
  * `d = 356`: table `402 ≤ n ≤ 405`, new code of length `404`
  * `d = 357`: table `403 ≤ n ≤ 406`, new code of length `405`
  * `d = 358`: table `405 ≤ n ≤ 407`, new code of length `406`
  * `d = 359`: table `406 ≤ n ≤ 408`, new code of length `407`
  * `d = 360`: table `407 ≤ n ≤ 409`, new code of length `408`
  * `d = 370`: table `418 ≤ n ≤ 422`, new code of length `420`
  * `d = 371`: table `419 ≤ n ≤ 423`, new code of length `421`
  * `d = 372`: table `420 ≤ n ≤ 424`, new code of length `422`
  * `d = 373`: table `421 ≤ n ≤ 425`, new code of length `424`
  * `d = 374`: table `423 ≤ n ≤ 426`, new code of length `425`
  * `d = 375`: table `424 ≤ n ≤ 427`, new code of length `426`
  * `d = 379`: table `429 ≤ n ≤ 432`, new code of length `431`
  * `d = 380`: table `430 ≤ n ≤ 433`, new code of length `432`
  * `d = 381`: table `431 ≤ n ≤ 434`, new code of length `433`
  * `d = 382`: table `432 ≤ n ≤ 435`, new code of length `434`
  * `d = 383`: table `433 ≤ n ≤ 436`, new code of length `435`
  * `d = 384`: table `434 ≤ n ≤ 437`, new code of length `436`
  * `d = 385`: table `435 ≤ n ≤ 438`, new code of length `437`
  * `d = 386`: table `436 ≤ n ≤ 439`, new code of length `438`
  * `d = 387`: table `437 ≤ n ≤ 440`, new code of length `439`
  * `d = 397`: table `449 ≤ n ≤ 452`, new code of length `451`
  * `d = 398`: table `450 ≤ n ≤ 453`, new code of length `452`
  * `d = 399`: table `451 ≤ n ≤ 454`, new code of length `453`
  * `d = 400`: table `452 ≤ n ≤ 455`, new code of length `454`
  * `d = 401`: table `453 ≤ n ≤ 456`, new code of length `455`
  * `d = 402`: table `454 ≤ n ≤ 457`, new code of length `456`
  * `d = 403`: table `455 ≤ n ≤ 458`, new code of length `457`
  * `d = 404`: table `456 ≤ n ≤ 459`, new code of length `458`
  * `d = 405`: table `457 ≤ n ≤ 460`, new code of length `459`
  * `d = 406`: table `459 ≤ n ≤ 462`, new code of length `460`
  * `d = 407`: table `460 ≤ n ≤ 463`, new code of length `461`
  * `d = 408`: table `461 ≤ n ≤ 464`, new code of length `462`
  * `d = 409`: table `462 ≤ n ≤ 465`, new code of length `463`
  * `d = 410`: table `463 ≤ n ≤ 466`, new code of length `464`
  * `d = 411`: table `464 ≤ n ≤ 467`, new code of length `465`
  * `d = 412`: table `465 ≤ n ≤ 468`, new code of length `466`
  * `d = 413`: table `466 ≤ n ≤ 469`, new code of length `467`
  * `d = 414`: table `467 ≤ n ≤ 470`, new code of length `468`
  * `d = 415`: table `469 ≤ n ≤ 472`, new code of length `471`
  * `d = 416`: table `470 ≤ n ≤ 473`, new code of length `472`
  * `d = 417`: table `471 ≤ n ≤ 474`, new code of length `473`
  * `d = 424`: table `479 ≤ n ≤ 482`, new code of length `481`
  * `d = 425`: table `480 ≤ n ≤ 483`, new code of length `482`
  * `d = 426`: table `481 ≤ n ≤ 484`, new code of length `483`
  * `d = 427`: table `482 ≤ n ≤ 485`, new code of length `484`
  * `d = 428`: table `483 ≤ n ≤ 486`, new code of length `485`
  * `d = 429`: table `484 ≤ n ≤ 487`, new code of length `486`
  * `d = 433`: table `490 ≤ n ≤ 492`, new code of length `491`
  * `d = 434`: table `491 ≤ n ≤ 493`, new code of length `492`
  * `d = 435`: table `492 ≤ n ≤ 494`, new code of length `493`
  * `d = 436`: table `493 ≤ n ≤ 495`, new code of length `494`
  * `d = 437`: table `494 ≤ n ≤ 496`, new code of length `495`
  * `d = 438`: table `495 ≤ n ≤ 497`, new code of length `496`
  * `d = 487`: table `550 ≤ n ≤ 552`, new code of length `551`
  * `d = 488`: table `551 ≤ n ≤ 553`, new code of length `552`
  * `d = 489`: table `552 ≤ n ≤ 554`, new code of length `553`
  * `d = 496`: table `560 ≤ n ≤ 562`, new code of length `561`
  * `d = 497`: table `561 ≤ n ≤ 563`, new code of length `562`
  * `d = 498`: table `562 ≤ n ≤ 564`, new code of length `563`
  * `d = 499`: table `563 ≤ n ≤ 565`, new code of length `564`
  * `d = 500`: table `564 ≤ n ≤ 566`, new code of length `565`
  * `d = 505`: table `570 ≤ n ≤ 572`, new code of length `571`
  * `d = 506`: table `571 ≤ n ≤ 573`, new code of length `572`
  * `d = 507`: table `572 ≤ n ≤ 574`, new code of length `573`
  * `d = 508`: table `573 ≤ n ≤ 575`, new code of length `574`
  * `d = 509`: table `574 ≤ n ≤ 576`, new code of length `575`
  * `d = 510`: table `575 ≤ n ≤ 577`, new code of length `576`
  * `d = 511`: table `576 ≤ n ≤ 578`, new code of length `577`
  * `d = 512`: table `578 ≤ n ≤ 579`, new code of length `578` (attains the lower bound: value determined)
  * `d = 513`: table `579 ≤ n ≤ 580`, new code of length `579` (attains the lower bound: value determined)
-/
theorem main9 :
    (∃ L : List Vec4, IsCode L 218 190) ∧
    (∃ L : List Vec4, IsCode L 219 191) ∧
    (∃ L : List Vec4, IsCode L 220 192) ∧
    (∃ L : List Vec4, IsCode L 223 194) ∧
    (∃ L : List Vec4, IsCode L 224 195) ∧
    (∃ L : List Vec4, IsCode L 225 196) ∧
    (∃ L : List Vec4, IsCode L 226 197) ∧
    (∃ L : List Vec4, IsCode L 227 198) ∧
    (∃ L : List Vec4, IsCode L 228 199) ∧
    (∃ L : List Vec4, IsCode L 229 200) ∧
    (∃ L : List Vec4, IsCode L 264 231) ∧
    (∃ L : List Vec4, IsCode L 265 232) ∧
    (∃ L : List Vec4, IsCode L 275 241) ∧
    (∃ L : List Vec4, IsCode L 276 242) ∧
    (∃ L : List Vec4, IsCode L 277 243) ∧
    (∃ L : List Vec4, IsCode L 289 253) ∧
    (∃ L : List Vec4, IsCode L 290 254) ∧
    (∃ L : List Vec4, IsCode L 291 255) ∧
    (∃ L : List Vec4, IsCode L 292 256) ∧
    (∃ L : List Vec4, IsCode L 299 262) ∧
    (∃ L : List Vec4, IsCode L 300 263) ∧
    (∃ L : List Vec4, IsCode L 301 264) ∧
    (∃ L : List Vec4, IsCode L 302 265) ∧
    (∃ L : List Vec4, IsCode L 303 266) ∧
    (∃ L : List Vec4, IsCode L 305 267) ∧
    (∃ L : List Vec4, IsCode L 306 268) ∧
    (∃ L : List Vec4, IsCode L 307 269) ∧
    (∃ L : List Vec4, IsCode L 308 270) ∧
    (∃ L : List Vec4, IsCode L 309 271) ∧
    (∃ L : List Vec4, IsCode L 310 272) ∧
    (∃ L : List Vec4, IsCode L 311 273) ∧
    (∃ L : List Vec4, IsCode L 312 274) ∧
    (∃ L : List Vec4, IsCode L 313 275) ∧
    (∃ L : List Vec4, IsCode L 314 276) ∧
    (∃ L : List Vec4, IsCode L 316 277) ∧
    (∃ L : List Vec4, IsCode L 317 278) ∧
    (∃ L : List Vec4, IsCode L 318 279) ∧
    (∃ L : List Vec4, IsCode L 330 289) ∧
    (∃ L : List Vec4, IsCode L 331 290) ∧
    (∃ L : List Vec4, IsCode L 332 291) ∧
    (∃ L : List Vec4, IsCode L 333 292) ∧
    (∃ L : List Vec4, IsCode L 340 298) ∧
    (∃ L : List Vec4, IsCode L 341 299) ∧
    (∃ L : List Vec4, IsCode L 342 300) ∧
    (∃ L : List Vec4, IsCode L 343 301) ∧
    (∃ L : List Vec4, IsCode L 344 302) ∧
    (∃ L : List Vec4, IsCode L 345 303) ∧
    (∃ L : List Vec4, IsCode L 347 304) ∧
    (∃ L : List Vec4, IsCode L 348 305) ∧
    (∃ L : List Vec4, IsCode L 349 306) ∧
    (∃ L : List Vec4, IsCode L 350 307) ∧
    (∃ L : List Vec4, IsCode L 351 308) ∧
    (∃ L : List Vec4, IsCode L 352 309) ∧
    (∃ L : List Vec4, IsCode L 353 310) ∧
    (∃ L : List Vec4, IsCode L 354 311) ∧
    (∃ L : List Vec4, IsCode L 355 312) ∧
    (∃ L : List Vec4, IsCode L 379 333) ∧
    (∃ L : List Vec4, IsCode L 380 334) ∧
    (∃ L : List Vec4, IsCode L 381 335) ∧
    (∃ L : List Vec4, IsCode L 382 336) ∧
    (∃ L : List Vec4, IsCode L 384 337) ∧
    (∃ L : List Vec4, IsCode L 385 338) ∧
    (∃ L : List Vec4, IsCode L 386 339) ∧
    (∃ L : List Vec4, IsCode L 387 340) ∧
    (∃ L : List Vec4, IsCode L 388 341) ∧
    (∃ L : List Vec4, IsCode L 389 342) ∧
    (∃ L : List Vec4, IsCode L 390 343) ∧
    (∃ L : List Vec4, IsCode L 392 344) ∧
    (∃ L : List Vec4, IsCode L 393 345) ∧
    (∃ L : List Vec4, IsCode L 394 346) ∧
    (∃ L : List Vec4, IsCode L 395 347) ∧
    (∃ L : List Vec4, IsCode L 396 348) ∧
    (∃ L : List Vec4, IsCode L 397 349) ∧
    (∃ L : List Vec4, IsCode L 398 350) ∧
    (∃ L : List Vec4, IsCode L 399 351) ∧
    (∃ L : List Vec4, IsCode L 400 352) ∧
    (∃ L : List Vec4, IsCode L 401 353) ∧
    (∃ L : List Vec4, IsCode L 402 354) ∧
    (∃ L : List Vec4, IsCode L 403 355) ∧
    (∃ L : List Vec4, IsCode L 404 356) ∧
    (∃ L : List Vec4, IsCode L 405 357) ∧
    (∃ L : List Vec4, IsCode L 406 358) ∧
    (∃ L : List Vec4, IsCode L 407 359) ∧
    (∃ L : List Vec4, IsCode L 408 360) ∧
    (∃ L : List Vec4, IsCode L 420 370) ∧
    (∃ L : List Vec4, IsCode L 421 371) ∧
    (∃ L : List Vec4, IsCode L 422 372) ∧
    (∃ L : List Vec4, IsCode L 424 373) ∧
    (∃ L : List Vec4, IsCode L 425 374) ∧
    (∃ L : List Vec4, IsCode L 426 375) ∧
    (∃ L : List Vec4, IsCode L 431 379) ∧
    (∃ L : List Vec4, IsCode L 432 380) ∧
    (∃ L : List Vec4, IsCode L 433 381) ∧
    (∃ L : List Vec4, IsCode L 434 382) ∧
    (∃ L : List Vec4, IsCode L 435 383) ∧
    (∃ L : List Vec4, IsCode L 436 384) ∧
    (∃ L : List Vec4, IsCode L 437 385) ∧
    (∃ L : List Vec4, IsCode L 438 386) ∧
    (∃ L : List Vec4, IsCode L 439 387) ∧
    (∃ L : List Vec4, IsCode L 451 397) ∧
    (∃ L : List Vec4, IsCode L 452 398) ∧
    (∃ L : List Vec4, IsCode L 453 399) ∧
    (∃ L : List Vec4, IsCode L 454 400) ∧
    (∃ L : List Vec4, IsCode L 455 401) ∧
    (∃ L : List Vec4, IsCode L 456 402) ∧
    (∃ L : List Vec4, IsCode L 457 403) ∧
    (∃ L : List Vec4, IsCode L 458 404) ∧
    (∃ L : List Vec4, IsCode L 459 405) ∧
    (∃ L : List Vec4, IsCode L 460 406) ∧
    (∃ L : List Vec4, IsCode L 461 407) ∧
    (∃ L : List Vec4, IsCode L 462 408) ∧
    (∃ L : List Vec4, IsCode L 463 409) ∧
    (∃ L : List Vec4, IsCode L 464 410) ∧
    (∃ L : List Vec4, IsCode L 465 411) ∧
    (∃ L : List Vec4, IsCode L 466 412) ∧
    (∃ L : List Vec4, IsCode L 467 413) ∧
    (∃ L : List Vec4, IsCode L 468 414) ∧
    (∃ L : List Vec4, IsCode L 471 415) ∧
    (∃ L : List Vec4, IsCode L 472 416) ∧
    (∃ L : List Vec4, IsCode L 473 417) ∧
    (∃ L : List Vec4, IsCode L 481 424) ∧
    (∃ L : List Vec4, IsCode L 482 425) ∧
    (∃ L : List Vec4, IsCode L 483 426) ∧
    (∃ L : List Vec4, IsCode L 484 427) ∧
    (∃ L : List Vec4, IsCode L 485 428) ∧
    (∃ L : List Vec4, IsCode L 486 429) ∧
    (∃ L : List Vec4, IsCode L 491 433) ∧
    (∃ L : List Vec4, IsCode L 492 434) ∧
    (∃ L : List Vec4, IsCode L 493 435) ∧
    (∃ L : List Vec4, IsCode L 494 436) ∧
    (∃ L : List Vec4, IsCode L 495 437) ∧
    (∃ L : List Vec4, IsCode L 496 438) ∧
    (∃ L : List Vec4, IsCode L 551 487) ∧
    (∃ L : List Vec4, IsCode L 552 488) ∧
    (∃ L : List Vec4, IsCode L 553 489) ∧
    (∃ L : List Vec4, IsCode L 561 496) ∧
    (∃ L : List Vec4, IsCode L 562 497) ∧
    (∃ L : List Vec4, IsCode L 563 498) ∧
    (∃ L : List Vec4, IsCode L 564 499) ∧
    (∃ L : List Vec4, IsCode L 565 500) ∧
    (∃ L : List Vec4, IsCode L 571 505) ∧
    (∃ L : List Vec4, IsCode L 572 506) ∧
    (∃ L : List Vec4, IsCode L 573 507) ∧
    (∃ L : List Vec4, IsCode L 574 508) ∧
    (∃ L : List Vec4, IsCode L 575 509) ∧
    (∃ L : List Vec4, IsCode L 576 510) ∧
    (∃ L : List Vec4, IsCode L 577 511) ∧
    (∃ L : List Vec4, IsCode L 578 512) ∧
    (∃ L : List Vec4, IsCode L 579 513) :=
  ⟨⟨C_220_192.drop 2, isCode_drop _ _ _ 2 C_220_192_isCode⟩,
   ⟨C_220_192.drop 1, isCode_drop _ _ _ 1 C_220_192_isCode⟩,
   ⟨C_220_192, C_220_192_isCode⟩,
   ⟨C_229_200.drop 6, isCode_drop _ _ _ 6 C_229_200_isCode⟩,
   ⟨C_229_200.drop 5, isCode_drop _ _ _ 5 C_229_200_isCode⟩,
   ⟨C_229_200.drop 4, isCode_drop _ _ _ 4 C_229_200_isCode⟩,
   ⟨C_229_200.drop 3, isCode_drop _ _ _ 3 C_229_200_isCode⟩,
   ⟨C_229_200.drop 2, isCode_drop _ _ _ 2 C_229_200_isCode⟩,
   ⟨C_229_200.drop 1, isCode_drop _ _ _ 1 C_229_200_isCode⟩,
   ⟨C_229_200, C_229_200_isCode⟩,
   ⟨C_265_232.drop 1, isCode_drop _ _ _ 1 C_265_232_isCode⟩,
   ⟨C_265_232, C_265_232_isCode⟩,
   ⟨C_277_243.drop 2, isCode_drop _ _ _ 2 C_277_243_isCode⟩,
   ⟨C_277_243.drop 1, isCode_drop _ _ _ 1 C_277_243_isCode⟩,
   ⟨C_277_243, C_277_243_isCode⟩,
   ⟨C_292_256.drop 3, isCode_drop _ _ _ 3 C_292_256_isCode⟩,
   ⟨C_292_256.drop 2, isCode_drop _ _ _ 2 C_292_256_isCode⟩,
   ⟨C_292_256.drop 1, isCode_drop _ _ _ 1 C_292_256_isCode⟩,
   ⟨C_292_256, C_292_256_isCode⟩,
   ⟨C_303_266.drop 4, isCode_drop _ _ _ 4 C_303_266_isCode⟩,
   ⟨C_303_266.drop 3, isCode_drop _ _ _ 3 C_303_266_isCode⟩,
   ⟨C_303_266.drop 2, isCode_drop _ _ _ 2 C_303_266_isCode⟩,
   ⟨C_303_266.drop 1, isCode_drop _ _ _ 1 C_303_266_isCode⟩,
   ⟨C_303_266, C_303_266_isCode⟩,
   ⟨C_314_276.drop 9, isCode_drop _ _ _ 9 C_314_276_isCode⟩,
   ⟨C_314_276.drop 8, isCode_drop _ _ _ 8 C_314_276_isCode⟩,
   ⟨C_314_276.drop 7, isCode_drop _ _ _ 7 C_314_276_isCode⟩,
   ⟨C_314_276.drop 6, isCode_drop _ _ _ 6 C_314_276_isCode⟩,
   ⟨C_314_276.drop 5, isCode_drop _ _ _ 5 C_314_276_isCode⟩,
   ⟨C_314_276.drop 4, isCode_drop _ _ _ 4 C_314_276_isCode⟩,
   ⟨C_314_276.drop 3, isCode_drop _ _ _ 3 C_314_276_isCode⟩,
   ⟨C_314_276.drop 2, isCode_drop _ _ _ 2 C_314_276_isCode⟩,
   ⟨C_314_276.drop 1, isCode_drop _ _ _ 1 C_314_276_isCode⟩,
   ⟨C_314_276, C_314_276_isCode⟩,
   ⟨C_318_279.drop 2, isCode_drop _ _ _ 2 C_318_279_isCode⟩,
   ⟨C_318_279.drop 1, isCode_drop _ _ _ 1 C_318_279_isCode⟩,
   ⟨C_318_279, C_318_279_isCode⟩,
   ⟨C_333_292.drop 3, isCode_drop _ _ _ 3 C_333_292_isCode⟩,
   ⟨C_333_292.drop 2, isCode_drop _ _ _ 2 C_333_292_isCode⟩,
   ⟨C_333_292.drop 1, isCode_drop _ _ _ 1 C_333_292_isCode⟩,
   ⟨C_333_292, C_333_292_isCode⟩,
   ⟨C_345_303.drop 5, isCode_drop _ _ _ 5 C_345_303_isCode⟩,
   ⟨C_345_303.drop 4, isCode_drop _ _ _ 4 C_345_303_isCode⟩,
   ⟨C_345_303.drop 3, isCode_drop _ _ _ 3 C_345_303_isCode⟩,
   ⟨C_345_303.drop 2, isCode_drop _ _ _ 2 C_345_303_isCode⟩,
   ⟨C_345_303.drop 1, isCode_drop _ _ _ 1 C_345_303_isCode⟩,
   ⟨C_345_303, C_345_303_isCode⟩,
   ⟨C_355_312.drop 8, isCode_drop _ _ _ 8 C_355_312_isCode⟩,
   ⟨C_355_312.drop 7, isCode_drop _ _ _ 7 C_355_312_isCode⟩,
   ⟨C_355_312.drop 6, isCode_drop _ _ _ 6 C_355_312_isCode⟩,
   ⟨C_355_312.drop 5, isCode_drop _ _ _ 5 C_355_312_isCode⟩,
   ⟨C_355_312.drop 4, isCode_drop _ _ _ 4 C_355_312_isCode⟩,
   ⟨C_355_312.drop 3, isCode_drop _ _ _ 3 C_355_312_isCode⟩,
   ⟨C_355_312.drop 2, isCode_drop _ _ _ 2 C_355_312_isCode⟩,
   ⟨C_355_312.drop 1, isCode_drop _ _ _ 1 C_355_312_isCode⟩,
   ⟨C_355_312, C_355_312_isCode⟩,
   ⟨C_382_336.drop 3, isCode_drop _ _ _ 3 C_382_336_isCode⟩,
   ⟨C_382_336.drop 2, isCode_drop _ _ _ 2 C_382_336_isCode⟩,
   ⟨C_382_336.drop 1, isCode_drop _ _ _ 1 C_382_336_isCode⟩,
   ⟨C_382_336, C_382_336_isCode⟩,
   ⟨C_390_343.drop 6, isCode_drop _ _ _ 6 C_390_343_isCode⟩,
   ⟨C_390_343.drop 5, isCode_drop _ _ _ 5 C_390_343_isCode⟩,
   ⟨C_390_343.drop 4, isCode_drop _ _ _ 4 C_390_343_isCode⟩,
   ⟨C_390_343.drop 3, isCode_drop _ _ _ 3 C_390_343_isCode⟩,
   ⟨C_390_343.drop 2, isCode_drop _ _ _ 2 C_390_343_isCode⟩,
   ⟨C_390_343.drop 1, isCode_drop _ _ _ 1 C_390_343_isCode⟩,
   ⟨C_390_343, C_390_343_isCode⟩,
   ⟨C_408_360.drop 16, isCode_drop _ _ _ 16 C_408_360_isCode⟩,
   ⟨C_408_360.drop 15, isCode_drop _ _ _ 15 C_408_360_isCode⟩,
   ⟨C_408_360.drop 14, isCode_drop _ _ _ 14 C_408_360_isCode⟩,
   ⟨C_408_360.drop 13, isCode_drop _ _ _ 13 C_408_360_isCode⟩,
   ⟨C_408_360.drop 12, isCode_drop _ _ _ 12 C_408_360_isCode⟩,
   ⟨C_408_360.drop 11, isCode_drop _ _ _ 11 C_408_360_isCode⟩,
   ⟨C_408_360.drop 10, isCode_drop _ _ _ 10 C_408_360_isCode⟩,
   ⟨C_408_360.drop 9, isCode_drop _ _ _ 9 C_408_360_isCode⟩,
   ⟨C_408_360.drop 8, isCode_drop _ _ _ 8 C_408_360_isCode⟩,
   ⟨C_408_360.drop 7, isCode_drop _ _ _ 7 C_408_360_isCode⟩,
   ⟨C_408_360.drop 6, isCode_drop _ _ _ 6 C_408_360_isCode⟩,
   ⟨C_408_360.drop 5, isCode_drop _ _ _ 5 C_408_360_isCode⟩,
   ⟨C_408_360.drop 4, isCode_drop _ _ _ 4 C_408_360_isCode⟩,
   ⟨C_408_360.drop 3, isCode_drop _ _ _ 3 C_408_360_isCode⟩,
   ⟨C_408_360.drop 2, isCode_drop _ _ _ 2 C_408_360_isCode⟩,
   ⟨C_408_360.drop 1, isCode_drop _ _ _ 1 C_408_360_isCode⟩,
   ⟨C_408_360, C_408_360_isCode⟩,
   ⟨C_422_372.drop 2, isCode_drop _ _ _ 2 C_422_372_isCode⟩,
   ⟨C_422_372.drop 1, isCode_drop _ _ _ 1 C_422_372_isCode⟩,
   ⟨C_422_372, C_422_372_isCode⟩,
   ⟨C_426_375.drop 2, isCode_drop _ _ _ 2 C_426_375_isCode⟩,
   ⟨C_426_375.drop 1, isCode_drop _ _ _ 1 C_426_375_isCode⟩,
   ⟨C_426_375, C_426_375_isCode⟩,
   ⟨C_439_387.drop 8, isCode_drop _ _ _ 8 C_439_387_isCode⟩,
   ⟨C_439_387.drop 7, isCode_drop _ _ _ 7 C_439_387_isCode⟩,
   ⟨C_439_387.drop 6, isCode_drop _ _ _ 6 C_439_387_isCode⟩,
   ⟨C_439_387.drop 5, isCode_drop _ _ _ 5 C_439_387_isCode⟩,
   ⟨C_439_387.drop 4, isCode_drop _ _ _ 4 C_439_387_isCode⟩,
   ⟨C_439_387.drop 3, isCode_drop _ _ _ 3 C_439_387_isCode⟩,
   ⟨C_439_387.drop 2, isCode_drop _ _ _ 2 C_439_387_isCode⟩,
   ⟨C_439_387.drop 1, isCode_drop _ _ _ 1 C_439_387_isCode⟩,
   ⟨C_439_387, C_439_387_isCode⟩,
   ⟨C_468_414.drop 17, isCode_drop _ _ _ 17 C_468_414_isCode⟩,
   ⟨C_468_414.drop 16, isCode_drop _ _ _ 16 C_468_414_isCode⟩,
   ⟨C_468_414.drop 15, isCode_drop _ _ _ 15 C_468_414_isCode⟩,
   ⟨C_468_414.drop 14, isCode_drop _ _ _ 14 C_468_414_isCode⟩,
   ⟨C_468_414.drop 13, isCode_drop _ _ _ 13 C_468_414_isCode⟩,
   ⟨C_468_414.drop 12, isCode_drop _ _ _ 12 C_468_414_isCode⟩,
   ⟨C_468_414.drop 11, isCode_drop _ _ _ 11 C_468_414_isCode⟩,
   ⟨C_468_414.drop 10, isCode_drop _ _ _ 10 C_468_414_isCode⟩,
   ⟨C_468_414.drop 9, isCode_drop _ _ _ 9 C_468_414_isCode⟩,
   ⟨C_468_414.drop 8, isCode_drop _ _ _ 8 C_468_414_isCode⟩,
   ⟨C_468_414.drop 7, isCode_drop _ _ _ 7 C_468_414_isCode⟩,
   ⟨C_468_414.drop 6, isCode_drop _ _ _ 6 C_468_414_isCode⟩,
   ⟨C_468_414.drop 5, isCode_drop _ _ _ 5 C_468_414_isCode⟩,
   ⟨C_468_414.drop 4, isCode_drop _ _ _ 4 C_468_414_isCode⟩,
   ⟨C_468_414.drop 3, isCode_drop _ _ _ 3 C_468_414_isCode⟩,
   ⟨C_468_414.drop 2, isCode_drop _ _ _ 2 C_468_414_isCode⟩,
   ⟨C_468_414.drop 1, isCode_drop _ _ _ 1 C_468_414_isCode⟩,
   ⟨C_468_414, C_468_414_isCode⟩,
   ⟨C_473_417.drop 2, isCode_drop _ _ _ 2 C_473_417_isCode⟩,
   ⟨C_473_417.drop 1, isCode_drop _ _ _ 1 C_473_417_isCode⟩,
   ⟨C_473_417, C_473_417_isCode⟩,
   ⟨C_486_429.drop 5, isCode_drop _ _ _ 5 C_486_429_isCode⟩,
   ⟨C_486_429.drop 4, isCode_drop _ _ _ 4 C_486_429_isCode⟩,
   ⟨C_486_429.drop 3, isCode_drop _ _ _ 3 C_486_429_isCode⟩,
   ⟨C_486_429.drop 2, isCode_drop _ _ _ 2 C_486_429_isCode⟩,
   ⟨C_486_429.drop 1, isCode_drop _ _ _ 1 C_486_429_isCode⟩,
   ⟨C_486_429, C_486_429_isCode⟩,
   ⟨C_496_438.drop 5, isCode_drop _ _ _ 5 C_496_438_isCode⟩,
   ⟨C_496_438.drop 4, isCode_drop _ _ _ 4 C_496_438_isCode⟩,
   ⟨C_496_438.drop 3, isCode_drop _ _ _ 3 C_496_438_isCode⟩,
   ⟨C_496_438.drop 2, isCode_drop _ _ _ 2 C_496_438_isCode⟩,
   ⟨C_496_438.drop 1, isCode_drop _ _ _ 1 C_496_438_isCode⟩,
   ⟨C_496_438, C_496_438_isCode⟩,
   ⟨C_553_489.drop 2, isCode_drop _ _ _ 2 C_553_489_isCode⟩,
   ⟨C_553_489.drop 1, isCode_drop _ _ _ 1 C_553_489_isCode⟩,
   ⟨C_553_489, C_553_489_isCode⟩,
   ⟨C_565_500.drop 4, isCode_drop _ _ _ 4 C_565_500_isCode⟩,
   ⟨C_565_500.drop 3, isCode_drop _ _ _ 3 C_565_500_isCode⟩,
   ⟨C_565_500.drop 2, isCode_drop _ _ _ 2 C_565_500_isCode⟩,
   ⟨C_565_500.drop 1, isCode_drop _ _ _ 1 C_565_500_isCode⟩,
   ⟨C_565_500, C_565_500_isCode⟩,
   ⟨C_579_513.drop 8, isCode_drop _ _ _ 8 C_579_513_isCode⟩,
   ⟨C_579_513.drop 7, isCode_drop _ _ _ 7 C_579_513_isCode⟩,
   ⟨C_579_513.drop 6, isCode_drop _ _ _ 6 C_579_513_isCode⟩,
   ⟨C_579_513.drop 5, isCode_drop _ _ _ 5 C_579_513_isCode⟩,
   ⟨C_579_513.drop 4, isCode_drop _ _ _ 4 C_579_513_isCode⟩,
   ⟨C_579_513.drop 3, isCode_drop _ _ _ 3 C_579_513_isCode⟩,
   ⟨C_579_513.drop 2, isCode_drop _ _ _ 2 C_579_513_isCode⟩,
   ⟨C_579_513.drop 1, isCode_drop _ _ _ 1 C_579_513_isCode⟩,
   ⟨C_579_513, C_579_513_isCode⟩⟩


end Q9

#print axioms Q8.GF8_is_field
#print axioms Q8.main8
#print axioms Q9.GF9_is_field
#print axioms Q9.main9
