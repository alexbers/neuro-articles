set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-! Generic lemmas: integer vectors as lists, sign changes, compatibility (angle ≥ 60°). Core Lean only. -/

namespace K19

def dot : List Int → List Int → Int
  | a :: as, b :: bs => a * b + dot as bs
  | _, _ => 0

def sgn : List Int → List Int → List Int
  | a :: as, b :: bs => (a * b) :: sgn as bs
  | _, _ => []

/-- `x` and `y` make an angle of at least 60°: `⟨x,y⟩ ≤ |x||y|/2`, in exact integer form. -/
def Compat (x y : List Int) : Prop := dot x y ≤ 0 ∨ 4 * (dot x y * dot x y) ≤ dot x x * dot y y

def compatB (x y : List Int) : Bool :=
  decide (dot x y ≤ 0) || decide (4 * (dot x y * dot x y) ≤ dot x x * dot y y)

theorem compatB_iff (x y : List Int) : compatB x y = true ↔ Compat x y := by
  simp [compatB, Compat]

theorem dot_comm : ∀ x y : List Int, dot x y = dot y x
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by simp [dot, dot_comm as bs, Int.mul_comm]

theorem Compat.symm {x y : List Int} (h : Compat x y) : Compat y x := by
  unfold Compat at *; rw [dot_comm y x]; rcases h with h | h
  · exact Or.inl h
  · right; rw [Int.mul_comm (dot y y)]; exact h

theorem dot_sgn_left : ∀ s x y : List Int, dot (sgn s x) y = dot x (sgn s y)
  | [], x, y => by cases x <;> cases y <;> rfl
  | _ :: _, [], _ => by simp [sgn, dot]
  | _ :: _, _ :: _, [] => by simp [sgn, dot]
  | a :: as, b :: bs, c :: cs => by
      simp only [sgn, dot, dot_sgn_left as bs cs]
      rw [Int.mul_comm a b, Int.mul_assoc]

theorem sgn_sgn : ∀ s t x : List Int, sgn s (sgn t x) = sgn (sgn s t) x
  | [], _, _ => by simp [sgn]
  | _ :: _, [], _ => by simp [sgn]
  | _ :: _, _ :: _, [] => by simp [sgn]
  | a :: as, b :: bs, c :: cs => by
      simp only [sgn, sgn_sgn as bs cs, Int.mul_assoc]

/-- a sign vector: every entry squares to one -/
def IsSign (s : List Int) : Prop := ∀ a ∈ s, a * a = 1

theorem sgn_invol : ∀ (s x : List Int), IsSign s → x.length ≤ s.length → sgn s (sgn s x) = x
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, _ => by simp [sgn]
  | a :: as, b :: bs, hs, hl => by
      simp only [sgn]
      have ha : a * a = 1 := hs a (by simp)
      have hs' : IsSign as := fun c hc => hs c (by simp [hc])
      rw [sgn_invol as bs hs' (by simp at hl; omega)]
      rw [← Int.mul_assoc, ha, Int.one_mul]

theorem dot_sgn_sgn (s x y : List Int) (hs : IsSign s) (hy : y.length ≤ s.length) :
    dot (sgn s x) (sgn s y) = dot x y := by
  rw [dot_sgn_left, sgn_invol s y hs hy]

theorem length_sgn : ∀ s x : List Int, (sgn s x).length = min s.length x.length
  | [], x => by simp [sgn]
  | _ :: _, [] => by simp [sgn]
  | _ :: as, _ :: bs => by simp [sgn, length_sgn as bs]

theorem compat_sgn (s x y : List Int) (hs : IsSign s) (hx : x.length ≤ s.length) (hy : y.length ≤ s.length) :
    Compat (sgn s x) (sgn s y) ↔ Compat x y := by
  unfold Compat
  rw [dot_sgn_sgn s x y hs hy, dot_sgn_sgn s x x hs hx, dot_sgn_sgn s y y hs hy]

end K19
/-! ## Part 2: functions on coordinates, the bridge to lists, sign changes, base structure. -/

namespace K19

def sumTo : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => sumTo n f + f n

def dotF (x y : Nat → Int) : Int := sumTo 20 (fun k => x k * y k)

def vecN (n : Nat) (f : Nat → Int) : List Int := (List.range n).map f
def vecOf (f : Nat → Int) : List Int := vecN 20 f

theorem dot_append : ∀ (a b c d : List Int), a.length = c.length →
    dot (a ++ b) (c ++ d) = dot a c + dot b d
  | [], b, [], d, _ => by simp [dot]
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | x :: a, b, y :: c, d, h => by
      simp only [List.cons_append, dot]
      rw [dot_append a b c d (by simpa using h)]; omega

theorem dot_vecN (n : Nat) (f g : Nat → Int) : dot (vecN n f) (vecN n g) = sumTo n (fun k => f k * g k) := by
  induction n with
  | zero => simp [vecN, dot, sumTo]
  | succ n ih =>
    simp only [vecN, List.range_succ, List.map_append, List.map_cons, List.map_nil] at *
    rw [dot_append _ _ _ _ (by simp), ih]
    simp [dot, sumTo]

theorem dot_vecOf (f g : Nat → Int) : dot (vecOf f) (vecOf g) = dotF f g := dot_vecN 20 f g

theorem sgn_vecN (n : Nat) (s f : Nat → Int) : sgn (vecN n s) (vecN n f) = vecN n (fun k => s k * f k) := by
  induction n with
  | zero => simp [vecN, sgn]
  | succ n ih =>
    simp only [vecN, List.range_succ, List.map_append, List.map_cons, List.map_nil] at *
    have hsplit : ∀ (a b c d : List Int), a.length = c.length → sgn (a ++ b) (c ++ d) = sgn a c ++ sgn b d := by
      intro a b c d h
      induction a generalizing c with
      | nil => cases c <;> simp_all [sgn]
      | cons x a iha => cases c with
        | nil => simp at h
        | cons y c => simp only [List.cons_append, sgn]; rw [iha c (by simpa using h)]
    rw [hsplit _ _ _ _ (by simp), ih]; simp [sgn]

theorem vecOf_ne {f g : Nat → Int} (h : vecOf f ≠ vecOf g) : ∃ k, k < 20 ∧ f k ≠ g k := by
  apply Classical.byContradiction; intro hc
  apply h; unfold vecOf vecN; apply List.map_congr_left
  intro k hk; simp at hk
  apply Classical.byContradiction; intro hne; exact hc ⟨k, hk, hne⟩

theorem length_vecOf (f : Nat → Int) : (vecOf f).length = 20 := by simp [vecOf, vecN]

/-- sign vector given by a bitmask of minus signs -/
def signF (gm : Nat) : Nat → Int := fun k => if gm.testBit k then -1 else 1

theorem isSign_signF (gm : Nat) : IsSign (vecOf (signF gm)) := by
  intro a ha; simp [vecOf, vecN, signF] at ha
  obtain ⟨k, _, hk⟩ := ha; subst hk; split <;> decide

theorem signF_mul (a b : Nat) (k : Nat) : signF a k * signF b k = signF (a ^^^ b) k := by
  simp only [signF, Nat.testBit_xor]
  by_cases ha : a.testBit k <;> by_cases hb : b.testBit k <;> simp [ha, hb]

theorem sgn_signF_signF (a b : Nat) : sgn (vecOf (signF a)) (vecOf (signF b)) = vecOf (signF (a ^^^ b)) := by
  unfold vecOf; rw [sgn_vecN]; congr 1; funext k; exact signF_mul a b k

end K19
/-! ## Part 3: structural lemmas for the Cohn–Li odd configuration (octad vectors and roots). -/
namespace K19


/-- octad vector: support `o` (bitmask), minus signs at the bits of `m` -/
def octF (o m : Nat) : Nat → Int := fun k => if o.testBit k then (if m.testBit k then -1 else 1) else 0

/-- number of set bits of `x` among the first `n` -/
def cnt : Nat → Nat → Int
  | 0, _ => 0
  | n + 1, x => cnt n x + (if x.testBit n then 1 else 0)

theorem sumTo_le (n : Nat) (f g : Nat → Int) (h : ∀ k, k < n → f k ≤ g k) : sumTo n f ≤ sumTo n g := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    simp only [sumTo]
    have h1 := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    have h2 := h n (Nat.lt_succ_self n)
    omega

theorem sumTo_congr (n : Nat) (f g : Nat → Int) (h : ∀ k, k < n → f k = g k) : sumTo n f = sumTo n g := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    simp only [sumTo]
    rw [ih (fun k hk => h k (Nat.lt_succ_of_lt hk)), h n (Nat.lt_succ_self n)]

theorem cnt_eq_sumTo (n x : Nat) : cnt n x = sumTo n (fun k => if x.testBit k then 1 else 0) := by
  induction n with
  | zero => simp [cnt, sumTo]
  | succ n ih => simp [cnt, sumTo, ih]

/-- two octad vectors on different octads: the inner product is at most the size of the intersection -/
theorem dot_oct_le_cnt (o m o' m' : Nat) : dotF (octF o m) (octF o' m') ≤ cnt 20 (o &&& o') := by
  rw [cnt_eq_sumTo]
  apply sumTo_le
  intro k _
  simp only [octF, Nat.testBit_and]
  by_cases h1 : o.testBit k <;> by_cases h2 : o'.testBit k <;> by_cases h3 : m.testBit k <;>
    by_cases h4 : m'.testBit k <;> simp [h1, h2, h3, h4]

/-- same octad: inner product = |o| - 2 * #(o ∩ (m xor m')) -/
theorem dot_oct_same (o m m' : Nat) :
    dotF (octF o m) (octF o m') = cnt 20 o - 2 * cnt 20 (o &&& (m ^^^ m')) := by
  simp only [dotF]
  rw [cnt_eq_sumTo, cnt_eq_sumTo]
  generalize 20 = n
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    simp only [sumTo]
    rw [ih]
    simp only [octF, Nat.testBit_and, Nat.testBit_xor]
    by_cases h1 : o.testBit n <;> by_cases h3 : m.testBit n <;> by_cases h4 : m'.testBit n <;>
      simp [h1, h3, h4] <;> omega

/-- parity: #(o∩(m xor m')) ≡ #(o∩m) + #(o∩m') (mod 2), in the form of an exact identity -/
theorem cnt_xor (o m m' : Nat) (n : Nat) :
    cnt n (o &&& (m ^^^ m')) + 2 * cnt n (o &&& (m &&& m')) = cnt n (o &&& m) + cnt n (o &&& m') := by
  induction n with
  | zero => simp [cnt]
  | succ n ih =>
    simp only [cnt, Nat.testBit_and, Nat.testBit_xor]
    by_cases h1 : o.testBit n <;> by_cases h3 : m.testBit n <;> by_cases h4 : m'.testBit n <;>
      simp [h1, h3, h4] <;> omega

theorem sumTo_nonneg (n : Nat) (f : Nat → Int) (h : ∀ j, 0 ≤ f j) : 0 ≤ sumTo n f := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih => simp only [sumTo]; have := h n; omega

theorem le_sumTo (n k : Nat) (f : Nat → Int) (h : ∀ j, 0 ≤ f j) (hk : k < n) : f k ≤ sumTo n f := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [sumTo]
    by_cases hkn : k < n
    · have := ih hkn; have := h n; omega
    · have hkeq : k = n := by omega
      subst hkeq
      have := sumTo_nonneg k f h; omega

/-- if two octad vectors on the same octad differ (as functions on coordinates < 20), the
xor-count is positive -/
theorem cnt_pos_of_ne (o m m' : Nat)
    (h : ∃ k, k < 20 ∧ octF o m k ≠ octF o m' k) : 1 ≤ cnt 20 (o &&& (m ^^^ m')) := by
  obtain ⟨k, hk, hne⟩ := h
  rw [cnt_eq_sumTo]
  have hb : (o &&& (m ^^^ m')).testBit k = true := by
    simp only [octF] at hne
    simp only [Nat.testBit_and, Nat.testBit_xor]
    by_cases h1 : o.testBit k <;> by_cases h3 : m.testBit k <;> by_cases h4 : m'.testBit k <;>
      simp_all
  have hnn : ∀ j, (0 : Int) ≤ (fun j => if (o &&& (m ^^^ m')).testBit j then (1 : Int) else 0) j := by
    intro j; simp only; split <;> omega
  have := le_sumTo 20 k _ hnn hk
  simp only [hb] at this
  simpa using this

/-- Lemma 2.1 of Cohn–Li for two octad vectors on the same octad with odd sign parities. -/
theorem dot_oct_same_le (o m m' : Nat) (ho : cnt 20 o = 8)
    (hm : cnt 20 (o &&& m) % 2 = 1) (hm' : cnt 20 (o &&& m') % 2 = 1)
    (h : ∃ k, k < 20 ∧ octF o m k ≠ octF o m' k) : dotF (octF o m) (octF o m') ≤ 4 := by
  rw [dot_oct_same, ho]
  have hx := cnt_xor o m m' 20
  have hp := cnt_pos_of_ne o m m' h
  omega

/-- root vector ±2e_i ± 2e_j -/
def rootF (i j : Nat) (a b : Int) : Nat → Int := fun k => if k = i then a else if k = j then b else 0

theorem sumTo_add (n : Nat) (f g : Nat → Int) :
    sumTo n (fun k => f k + g k) = sumTo n f + sumTo n g := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih => simp only [sumTo, ih]; omega

theorem sumTo_zero (n : Nat) : sumTo n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumTo, ih]

theorem sumTo_single (n i : Nat) (f : Nat → Int) (hi : i < n)
    (hf : ∀ k, k < n → k ≠ i → f k = 0) : sumTo n f = f i := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [sumTo]
    by_cases hin : i < n
    · rw [ih hin (fun k hk hki => hf k (by omega) hki)]
      have := hf n (by omega) (by omega); omega
    · have hieq : i = n := by omega
      subst hieq
      have : sumTo i f = 0 := by
        rw [sumTo_congr i f (fun _ => 0) (fun k hk => hf k (by omega) (by omega))]
        exact sumTo_zero i
      omega

theorem dot_root (i j : Nat) (a b : Int) (y : Nat → Int) (hij : i ≠ j) (hi : i < 20) (hj : j < 20) :
    dotF (rootF i j a b) y = a * y i + b * y j := by
  unfold dotF
  rw [sumTo_congr 20 _ (fun k => (if k = i then a * y i else 0) + (if k = j then b * y j else 0))
    (fun k _ => by
      unfold rootF
      by_cases hki : k = i
      · subst hki; simp [hij]
      · by_cases hkj : k = j
        · subst hkj; simp [hki]
        · simp [hki, hkj])]
  rw [sumTo_add]
  rw [sumTo_single 20 i _ hi (fun k _ hki => by simp [hki]),
      sumTo_single 20 j _ hj (fun k _ hkj => by simp [hkj])]
  simp

end K19
/-! ## Part 4: the symmetry-reduced proof, for arbitrary data satisfying finitely checkable hypotheses. -/
namespace K19

def octV (p : Nat × Nat) : List Int := vecOf (octF p.1 p.2)
def rootV (r : Nat × Nat × Int × Int) : List Int := vecOf (rootF r.1 r.2.1 r.2.2.1 r.2.2.2)

/-- action of the sign change with minus-mask `gm` on octad data and on root data -/
def gO (gm : Nat) (p : Nat × Nat) : Nat × Nat := (p.1, p.2 ^^^ (gm &&& p.1))
def gR (gm : Nat) (r : Nat × Nat × Int × Int) : Nat × Nat × Int × Int :=
  (r.1, r.2.1, signF gm r.1 * r.2.2.1, signF gm r.2.1 * r.2.2.2)

theorem compat_of_le4 {x y : List Int} (h : dot x y ≤ 4) (hx : dot x x = 8) (hy : dot y y = 8) :
    Compat x y := by
  unfold Compat; rw [hx, hy]
  by_cases h0 : dot x y ≤ 0
  · exact Or.inl h0
  · right
    have : dot x y = 1 ∨ dot x y = 2 ∨ dot x y = 3 ∨ dot x y = 4 := by omega
    rcases this with h1 | h1 | h1 | h1 <;> rw [h1] <;> decide

theorem norm_octV (p : Nat × Nat) (h : cnt 20 p.1 = 8) : dot (octV p) (octV p) = 8 := by
  unfold octV; rw [dot_vecOf]; unfold dotF
  have := dot_oct_same p.1 p.2 p.2
  unfold dotF at this; rw [this, h, Nat.xor_self, Nat.and_zero]
  simp [cnt_eq_sumTo, sumTo_zero]

theorem rootF_i (i j : Nat) (a b : Int) : rootF i j a b i = a := by simp [rootF]
theorem rootF_j (i j : Nat) (a b : Int) (h : i ≠ j) : rootF i j a b j = b := by
  simp [rootF, Ne.symm h]

theorem norm_rootV (r : Nat × Nat × Int × Int) (h1 : r.1 < 20) (h2 : r.2.1 < 20) (h3 : r.1 ≠ r.2.1)
    (ha : r.2.2.1 = 2 ∨ r.2.2.1 = -2) (hb : r.2.2.2 = 2 ∨ r.2.2.2 = -2) : dot (rootV r) (rootV r) = 8 := by
  unfold rootV; rw [dot_vecOf, dot_root _ _ _ _ _ h3 h1 h2, rootF_i, rootF_j _ _ _ _ h3]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;> decide

theorem octF_abs (o m k : Nat) : octF o m k = 0 ∨ octF o m k = 1 ∨ octF o m k = -1 := by
  unfold octF; split
  · split <;> simp
  · simp

theorem dot_rootV_octV (r : Nat × Nat × Int × Int) (p : Nat × Nat) (h1 : r.1 < 20) (h2 : r.2.1 < 20)
    (h3 : r.1 ≠ r.2.1) (ha : r.2.2.1 = 2 ∨ r.2.2.1 = -2) (hb : r.2.2.2 = 2 ∨ r.2.2.2 = -2) :
    dot (rootV r) (octV p) ≤ 4 := by
  unfold rootV octV; rw [dot_vecOf, dot_root _ _ _ _ _ h3 h1 h2]
  rcases octF_abs p.1 p.2 r.1 with e1 | e1 | e1 <;> rcases octF_abs p.1 p.2 r.2.1 with e2 | e2 | e2 <;>
    rw [e1, e2] <;> rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;> decide

theorem dot_octV_octV (p q : Nat × Nat) (hp : cnt 20 p.1 = 8) (hpm : cnt 20 (p.1 &&& p.2) % 2 = 1)
    (hqm : cnt 20 (q.1 &&& q.2) % 2 = 1)
    (hint : p.1 ≠ q.1 → cnt 20 (p.1 &&& q.1) ≤ 4) (hne : octV p ≠ octV q) : dot (octV p) (octV q) ≤ 4 := by
  unfold octV at *; rw [dot_vecOf]
  by_cases hpq : p.1 = q.1
  · have hne' := vecOf_ne hne
    obtain ⟨k, hk, hk2⟩ := hne'
    have := dot_oct_same_le p.1 p.2 q.2 hp hpm (by rw [hpq]; exact hqm) ⟨k, hk, by rw [hpq] at hk2 ⊢; exact hk2⟩
    rw [hpq] at this ⊢; exact this
  · have := dot_oct_le_cnt p.1 p.2 q.1 q.2
    have := hint hpq; omega

theorem sgn_octV (gm : Nat) (p : Nat × Nat) : sgn (vecOf (signF gm)) (octV p) = octV (gO gm p) := by
  unfold octV vecOf gO; rw [sgn_vecN]; congr 1; funext k
  simp only [signF, octF, Nat.testBit_xor, Nat.testBit_and]
  by_cases h1 : gm.testBit k <;> by_cases h2 : p.1.testBit k <;> by_cases h3 : p.2.testBit k <;>
    simp [h1, h2, h3]

theorem sgn_rootV (gm : Nat) (r : Nat × Nat × Int × Int) (h : r.1 ≠ r.2.1) :
    sgn (vecOf (signF gm)) (rootV r) = rootV (gR gm r) := by
  unfold rootV vecOf gR; rw [sgn_vecN]; congr 1; funext k
  simp only [rootF]
  by_cases hi : k = r.1
  · subst hi; simp
  · by_cases hj : k = r.2.1
    · subst hj; simp [hi]
    · simp [hi, hj]

theorem length_sgn_vecOf (gm : Nat) (x : List Int) (hx : x.length = 20) :
    (sgn (vecOf (signF gm)) x).length = 20 := by
  rw [length_sgn, length_vecOf, hx]; rfl

theorem main_generic (octData : List (Nat × Nat)) (rootData : List (Nat × Nat × Int × Int))
    (octads : List Nat) (reps : List (List Int)) (grpM : List Nat)
    (hOct : ∀ p ∈ octData, p.1 ∈ octads ∧ cnt 20 p.1 = 8 ∧ cnt 20 (p.1 &&& p.2) % 2 = 1)
    (hOctads : ∀ o ∈ octads, ∀ o' ∈ octads, o ≠ o' → cnt 20 (o &&& o') ≤ 4)
    (hRoot : ∀ r ∈ rootData, r.1 < 20 ∧ r.2.1 < 20 ∧ r.1 ≠ r.2.1 ∧ (r.2.2.1 = 2 ∨ r.2.2.1 = -2) ∧
      (r.2.2.2 = 2 ∨ r.2.2.2 = -2))
    (hRR : ∀ r ∈ rootData, ∀ r' ∈ rootData, r = r' ∨ dot (rootV r) (rootV r') ≤ 4)
    (hClosO : ∀ gm ∈ grpM, ∀ p ∈ octData, gO gm p ∈ octData)
    (hClosR : ∀ gm ∈ grpM, ∀ r ∈ rootData, gR gm r ∈ rootData)
    (hGrp : ∀ a ∈ grpM, ∀ b ∈ grpM, a ^^^ b ∈ grpM)
    (hRepLen : ∀ r ∈ reps, r.length = 20)
    (hK3 : ∀ r ∈ reps, (∀ p ∈ octData, compatB r (octV p) = true) ∧ ∀ q ∈ rootData, compatB r (rootV q) = true)
    (hK4 : ∀ r ∈ reps, ∀ r' ∈ reps, ∀ gm ∈ grpM,
      sgn (vecOf (signF gm)) r' = r ∨ compatB r (sgn (vecOf (signF gm)) r') = true) :
    ∀ x ∈ rootData.map rootV ++ octData.map octV ++ grpM.flatMap (fun gm => reps.map (sgn (vecOf (signF gm)))),
    ∀ y ∈ rootData.map rootV ++ octData.map octV ++ grpM.flatMap (fun gm => reps.map (sgn (vecOf (signF gm)))),
    x ≠ y → Compat x y := by
  -- base facts
  have baseLen : ∀ x ∈ rootData.map rootV ++ octData.map octV, x.length = 20 := by
    intro x hx; simp only [List.mem_append, List.mem_map] at hx
    rcases hx with ⟨r, _, rfl⟩ | ⟨p, _, rfl⟩ <;> exact length_vecOf _
  have baseNorm : ∀ x ∈ rootData.map rootV ++ octData.map octV, dot x x = 8 := by
    intro x hx; simp only [List.mem_append, List.mem_map] at hx
    rcases hx with ⟨r, hr, rfl⟩ | ⟨p, hp, rfl⟩
    · obtain ⟨h1, h2, h3, ha, hb⟩ := hRoot r hr; exact norm_rootV r h1 h2 h3 ha hb
    · exact norm_octV p (hOct p hp).2.1
  have baseClos : ∀ gm ∈ grpM, ∀ x ∈ rootData.map rootV ++ octData.map octV,
      sgn (vecOf (signF gm)) x ∈ rootData.map rootV ++ octData.map octV := by
    intro gm hg x hx; simp only [List.mem_append, List.mem_map] at hx ⊢
    rcases hx with ⟨r, hr, rfl⟩ | ⟨p, hp, rfl⟩
    · left; exact ⟨gR gm r, hClosR gm hg r hr, (sgn_rootV gm r (hRoot r hr).2.2.1).symm⟩
    · right; exact ⟨gO gm p, hClosO gm hg p hp, (sgn_octV gm p).symm⟩
  have baseBase : ∀ x ∈ rootData.map rootV ++ octData.map octV, ∀ y ∈ rootData.map rootV ++ octData.map octV,
      x ≠ y → Compat x y := by
    intro x hx y hy hxy
    apply compat_of_le4 _ (baseNorm x hx) (baseNorm y hy)
    simp only [List.mem_append, List.mem_map] at hx hy
    rcases hx with ⟨r, hr, rfl⟩ | ⟨p, hp, rfl⟩ <;> rcases hy with ⟨r', hr', rfl⟩ | ⟨q, hq, rfl⟩
    · rcases hRR r hr r' hr' with h | h
      · exact absurd (by rw [h]) hxy
      · exact h
    · obtain ⟨h1, h2, h3, ha, hb⟩ := hRoot r hr; exact dot_rootV_octV r q h1 h2 h3 ha hb
    · obtain ⟨h1, h2, h3, ha, hb⟩ := hRoot r' hr'; rw [dot_comm]; exact dot_rootV_octV r' p h1 h2 h3 ha hb
    · obtain ⟨hpo, hp8, hpm⟩ := hOct p hp; obtain ⟨hqo, _, hqm⟩ := hOct q hq
      exact dot_octV_octV p q hp8 hpm hqm (fun hne => hOctads p.1 hpo q.1 hqo hne) hxy
  -- new points
  have newMem : ∀ y ∈ grpM.flatMap (fun gm => reps.map (sgn (vecOf (signF gm)))),
      ∃ gm ∈ grpM, ∃ r ∈ reps, y = sgn (vecOf (signF gm)) r := by
    intro y hy; simp only [List.mem_flatMap, List.mem_map] at hy
    obtain ⟨gm, hg, r, hr, rfl⟩ := hy; exact ⟨gm, hg, r, hr, rfl⟩
  have isS : ∀ gm, IsSign (vecOf (signF gm)) := isSign_signF
  have inv : ∀ gm (x : List Int), x.length = 20 → sgn (vecOf (signF gm)) (sgn (vecOf (signF gm)) x) = x := by
    intro gm x hx; exact sgn_invol _ x (isS gm) (by rw [length_vecOf, hx] <;> omega)
  -- base vs new
  have baseNew : ∀ x ∈ rootData.map rootV ++ octData.map octV, ∀ gm ∈ grpM, ∀ r ∈ reps,
      Compat x (sgn (vecOf (signF gm)) r) := by
    intro x hx gm hg r hr
    have hxl := baseLen x hx
    have hrl := hRepLen r hr
    rw [← compat_sgn (vecOf (signF gm)) x _ (isS gm) (by rw [length_vecOf, hxl] <;> omega)
        (by rw [length_sgn_vecOf gm r hrl, length_vecOf] <;> omega)]
    rw [inv gm r hrl]
    apply Compat.symm
    have hmem := baseClos gm hg x hx
    simp only [List.mem_append, List.mem_map] at hmem
    rcases hmem with ⟨q, hq, hqe⟩ | ⟨p, hp, hpe⟩
    · rw [← hqe]; exact (compatB_iff _ _).1 ((hK3 r hr).2 q hq)
    · rw [← hpe]; exact (compatB_iff _ _).1 ((hK3 r hr).1 p hp)
  -- new vs new
  have newNew : ∀ a ∈ grpM, ∀ r ∈ reps, ∀ b ∈ grpM, ∀ r' ∈ reps,
      sgn (vecOf (signF a)) r ≠ sgn (vecOf (signF b)) r' →
      Compat (sgn (vecOf (signF a)) r) (sgn (vecOf (signF b)) r') := by
    intro a ha r hr b hb r' hr' hne
    have hrl := hRepLen r hr; have hrl' := hRepLen r' hr'
    rw [← compat_sgn (vecOf (signF a)) _ _ (isS a) (by rw [length_sgn_vecOf a r hrl, length_vecOf] <;> omega)
        (by rw [length_sgn_vecOf b r' hrl', length_vecOf] <;> omega)]
    rw [inv a r hrl, sgn_sgn, sgn_signF_signF]
    rcases hK4 r hr r' hr' (a ^^^ b) (hGrp a ha b hb) with h | h
    · exfalso; apply hne
      rw [← h, ← sgn_signF_signF, ← sgn_sgn, inv a _ (length_sgn_vecOf b r' hrl')]
    · exact (compatB_iff _ _).1 h
  -- assemble
  intro x hx y hy hxy
  simp only [List.mem_append] at hx hy
  have hx' : x ∈ rootData.map rootV ++ octData.map octV ∨
      x ∈ grpM.flatMap (fun gm => reps.map (sgn (vecOf (signF gm)))) := by
    rcases hx with (h | h) | h
    · exact Or.inl (List.mem_append.2 (Or.inl h))
    · exact Or.inl (List.mem_append.2 (Or.inr h))
    · exact Or.inr h
  have hy' : y ∈ rootData.map rootV ++ octData.map octV ∨
      y ∈ grpM.flatMap (fun gm => reps.map (sgn (vecOf (signF gm)))) := by
    rcases hy with (h | h) | h
    · exact Or.inl (List.mem_append.2 (Or.inl h))
    · exact Or.inl (List.mem_append.2 (Or.inr h))
    · exact Or.inr h
  rcases hx' with hxb | hxn <;> rcases hy' with hyb | hyn
  · exact baseBase x hxb y hyb hxy
  · obtain ⟨gm, hg, r, hr, rfl⟩ := newMem y hyn; exact baseNew x hxb gm hg r hr
  · obtain ⟨gm, hg, r, hr, rfl⟩ := newMem x hxn; exact (baseNew y hyb gm hg r hr).symm
  · obtain ⟨a, ha, r, hr, rfl⟩ := newMem x hxn; obtain ⟨b, hb, r', hr', rfl⟩ := newMem y hyn
    exact newNew a ha r hr b hb r' hr' hxy

end K19
/-! ## Part 5: closure via sorted keys, injective encoding for distinctness. -/
namespace K19

def keyO (p : Nat × Nat) : Nat := p.1 * 2 ^ 20 + p.2
def keyR (r : Nat × Nat × Int × Int) : Nat :=
  (r.1 * 32 + r.2.1) * 4 + (if r.2.2.1 = 2 then 2 else 0) + (if r.2.2.2 = 2 then 1 else 0)

theorem keyO_inj (p q : Nat × Nat) (hp : p.2 < 2 ^ 20) (hq : q.2 < 2 ^ 20) (h : keyO p = keyO q) : p = q := by
  unfold keyO at h
  have h1 : p.1 = q.1 := by omega
  have h2 : p.2 = q.2 := by omega
  exact Prod.ext h1 h2

theorem keyR_inj (r s : Nat × Nat × Int × Int) (hr1 : r.2.1 < 32) (hs1 : s.2.1 < 32)
    (hra : r.2.2.1 = 2 ∨ r.2.2.1 = -2) (hrb : r.2.2.2 = 2 ∨ r.2.2.2 = -2)
    (hsa : s.2.2.1 = 2 ∨ s.2.2.1 = -2) (hsb : s.2.2.2 = 2 ∨ s.2.2.2 = -2) (h : keyR r = keyR s) : r = s := by
  obtain ⟨i, j, a, b⟩ := r; obtain ⟨i', j', a', b'⟩ := s
  simp only at *
  unfold keyR at h; simp only at h
  rcases hra with rfl | rfl <;> rcases hrb with rfl | rfl <;> rcases hsa with rfl | rfl <;>
    rcases hsb with rfl | rfl <;> simp at h <;>
    (first | (have : i = i' := by omega); (have : j = j' := by omega); subst_vars; rfl | omega)

/-- structurally recursive merge (fuel = first argument) -/
def mergeF : Nat → List Nat → List Nat → List Nat
  | 0, a, b => a ++ b
  | _ + 1, [], b => b
  | _ + 1, a :: as, [] => a :: as
  | n + 1, x :: a, y :: b => if x ≤ y then x :: mergeF n a (y :: b) else y :: mergeF n (x :: a) b

theorem mergeF_perm : ∀ (n : Nat) (a b : List Nat), (mergeF n a b).Perm (a ++ b)
  | 0, a, b => by simp [mergeF]
  | _ + 1, [], b => by simp [mergeF]
  | _ + 1, a :: as, [] => by simp [mergeF]
  | n + 1, x :: a, y :: b => by
      simp only [mergeF]
      split
      · exact (mergeF_perm n a (y :: b)).cons x
      · have h1 := (mergeF_perm n (x :: a) b).cons y
        exact h1.trans (List.perm_middle.symm)

/-- structurally recursive merge sort (fuel = first argument) -/
def msortF : Nat → List Nat → List Nat
  | 0, l => l
  | f + 1, l => if l.length ≤ 1 then l else
      mergeF l.length (msortF f (l.take (l.length / 2))) (msortF f (l.drop (l.length / 2)))

theorem msortF_perm : ∀ (f : Nat) (l : List Nat), (msortF f l).Perm l
  | 0, l => by simp [msortF]
  | f + 1, l => by
      simp only [msortF]
      split
      · exact List.Perm.refl l
      · refine (mergeF_perm _ _ _).trans ?_
        have h := (msortF_perm f (l.take (l.length / 2))).append (msortF_perm f (l.drop (l.length / 2)))
        rw [List.take_append_drop] at h; exact h

theorem mem_of_sorted_eq {α : Type} (key : α → Nat) (P : α → Prop)
    (hinj : ∀ x y, P x → P y → key x = key y → x = y) (l1 l2 : List α)
    (h1 : ∀ x ∈ l1, P x) (h2 : ∀ x ∈ l2, P x)
    (hs : msortF 64 (l1.map key) = msortF 64 (l2.map key)) :
    ∀ x ∈ l1, x ∈ l2 := by
  intro x hx
  have hk : key x ∈ msortF 64 (l1.map key) :=
    (msortF_perm _ _).mem_iff.2 (List.mem_map.2 ⟨x, hx, rfl⟩)
  rw [hs] at hk
  obtain ⟨y, hy, hyx⟩ := List.mem_map.1 ((msortF_perm _ _).mem_iff.1 hk)
  rw [hinj y x (h2 y hy) (h1 x hx) hyx] at hy; exact hy

/-- injective encoding of an integer vector with entries in [-2^15, 2^15) -/
def encV : List Int → Nat
  | [] => 0
  | a :: as => (a + 2 ^ 15).toNat + 2 ^ 16 * encV as

def Bounded (v : List Int) : Prop := ∀ a ∈ v, -2 ^ 15 ≤ a ∧ a < 2 ^ 15

theorem encV_inj : ∀ x y : List Int, x.length = y.length → Bounded x → Bounded y → encV x = encV y → x = y
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _ => by simp at h
  | a :: as, b :: bs, hl, hx, hy, he => by
      have ha := hx a (by simp); have hb := hy b (by simp)
      simp only [encV] at he
      have hu : (a + 2 ^ 15).toNat < 2 ^ 16 := by omega
      have hv : (b + 2 ^ 15).toNat < 2 ^ 16 := by omega
      have h1 : (a + 2 ^ 15).toNat = (b + 2 ^ 15).toNat := by omega
      have h2 : encV as = encV bs := by omega
      have hab : a = b := by omega
      rw [hab, encV_inj as bs (by simpa using hl) (fun c hc => hx c (by simp [hc]))
        (fun c hc => hy c (by simp [hc])) h2]

def strictInc : List Nat → Bool
  | a :: b :: t => decide (a < b) && strictInc (b :: t)
  | _ => true

theorem strictInc_lt : ∀ (a : Nat) (l : List Nat), strictInc (a :: l) = true → ∀ x ∈ l, a < x
  | _, [], _, x, hx => by simp at hx
  | a, b :: t, h, x, hx => by
      simp only [strictInc, Bool.and_eq_true, decide_eq_true_eq] at h
      have ih := strictInc_lt b t h.2
      simp at hx; rcases hx with rfl | hx
      · exact h.1
      · exact Nat.lt_trans h.1 (ih x hx)

theorem strictInc_nodup : ∀ l : List Nat, strictInc l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
      refine List.nodup_cons.2 ⟨fun hm => Nat.lt_irrefl a (strictInc_lt a l h a hm), ?_⟩
      apply strictInc_nodup
      cases l with
      | nil => rfl
      | cons b t => simp only [strictInc, Bool.and_eq_true] at h; exact h.2

theorem nodup_of_enc (L : List (List Int))
    (hs : strictInc (msortF 64 (L.map encV)) = true) : L.Nodup := by
  have h1 := strictInc_nodup _ hs
  have h2 : (L.map encV).Nodup := (msortF_perm _ _).nodup_iff.1 h1
  exact List.Pairwise.of_map encV (fun a b h hab => h (by rw [hab])) h2

end K19
/-! ## Part 5b: fast evaluation of inner products with octad vectors and roots. -/
namespace K19

def posList (o : Nat) : List Nat := (List.range 20).filter (fun k => o.testBit k)

def dotOct (r : List Int) (pos : List Nat) (m : Nat) : Int :=
  (pos.map (fun k => (if m.testBit k then -1 else 1) * r.getD k 0)).sum

theorem list_eq_vecN : ∀ (r : List Int), r = vecN r.length (fun k => r.getD k 0)
  | [] => rfl
  | a :: r => by
      have ih := list_eq_vecN r
      simp only [vecN, List.length_cons] at *
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      have e : ((fun k => (a :: r).getD k 0) ∘ Nat.succ) = (fun k => r.getD k 0) := by
        funext k; simp
      rw [e, ← ih]; simp

theorem dot_list_vecOf (r : List Int) (hr : r.length = 20) (f : Nat → Int) :
    dot r (vecOf f) = sumTo 20 (fun k => r.getD k 0 * f k) := by
  have h := list_eq_vecN r
  rw [hr] at h
  conv => lhs; rw [h]
  exact dot_vecN 20 _ f

theorem sumTo_filter (n o : Nat) (g : Nat → Int) :
    sumTo n (fun k => if o.testBit k then g k else 0) = (((List.range n).filter (fun k => o.testBit k)).map g).sum := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    simp only [sumTo, ih, List.range_succ, List.filter_append, List.map_append, List.sum_append]
    by_cases h : o.testBit n <;> simp [h]

theorem dot_octV_fast (r : List Int) (hr : r.length = 20) (p : Nat × Nat) :
    dot r (octV p) = dotOct r (posList p.1) p.2 := by
  unfold octV; rw [dot_list_vecOf r hr]
  unfold dotOct posList
  rw [← sumTo_filter]
  apply sumTo_congr; intro k _
  simp only [octF]
  by_cases h1 : p.1.testBit k <;> by_cases h2 : p.2.testBit k <;> simp [h1, h2, Int.mul_comm]

theorem dot_rootV_fast (r : List Int) (hr : r.length = 20) (q : Nat × Nat × Int × Int)
    (h1 : q.1 < 20) (h2 : q.2.1 < 20) (h3 : q.1 ≠ q.2.1) :
    dot r (rootV q) = q.2.2.1 * r.getD q.1 0 + q.2.2.2 * r.getD q.2.1 0 := by
  rw [dot_comm]; unfold rootV
  have h := list_eq_vecN r; rw [hr] at h
  conv => lhs; rw [h]
  rw [show vecN 20 (fun k => r.getD k 0) = vecOf (fun k => r.getD k 0) from rfl, dot_vecOf]
  exact dot_root _ _ _ _ _ h3 h1 h2

end K19
/-! ## Part 6: pairwise version of the reduction (gives distinctness for free). -/
namespace K19

theorem not_compat_self (x : List Int) (h : 0 < dot x x) : ¬ Compat x x := by
  unfold Compat; intro hc
  rcases hc with h1 | h1
  · omega
  · have : dot x x * dot x x > 0 := Int.mul_pos h h
    omega

theorem ne_of_compat {x y : List Int} (hx : 0 < dot x x) (h : Compat x y) : x ≠ y := by
  intro e; subst e; exact not_compat_self x hx h

theorem testBit_differ (o m m' : Nat) (hm : m &&& o = m) (hm' : m' &&& o = m')
    (hlt : m < 2 ^ 20) (hlt' : m' < 2 ^ 20) (hne : m ≠ m') :
    ∃ k, k < 20 ∧ octF o m k ≠ octF o m' k := by
  have : ∃ k, m.testBit k ≠ m'.testBit k := by
    apply Classical.byContradiction; intro hc
    apply hne; apply Nat.eq_of_testBit_eq; intro k
    apply Classical.byContradiction; intro hk; exact hc ⟨k, hk⟩
  obtain ⟨k, hk⟩ := this
  have hk20 : k < 20 := by
    apply Classical.byContradiction; intro hk2
    have h1 : m.testBit k = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega)))
    have h2 : m'.testBit k = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlt' (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [h1, h2] at hk; exact hk rfl
  refine ⟨k, hk20, ?_⟩
  have ho : o.testBit k = true := by
    have e1 : (m &&& o).testBit k = m.testBit k := by rw [hm]
    have e2 : (m' &&& o).testBit k = m'.testBit k := by rw [hm']
    rw [Nat.testBit_and] at e1 e2
    cases hmk : m.testBit k <;> cases hmk' : m'.testBit k <;> simp_all
  simp only [octF, ho]
  cases hmk : m.testBit k <;> cases hmk' : m'.testBit k <;> simp_all

theorem dot_octV_rec (p q : Nat × Nat) (hp : cnt 20 p.1 = 8) (hpm : cnt 20 (p.1 &&& p.2) % 2 = 1)
    (hqm : cnt 20 (q.1 &&& q.2) % 2 = 1) (hint : p.1 ≠ q.1 → cnt 20 (p.1 &&& q.1) ≤ 4)
    (hsub : p.2 &&& p.1 = p.2) (hsub' : q.2 &&& q.1 = q.2) (hl : p.2 < 2 ^ 20) (hl' : q.2 < 2 ^ 20)
    (hne : p ≠ q) : dot (octV p) (octV q) ≤ 4 := by
  obtain ⟨o, m⟩ := p; obtain ⟨o', m'⟩ := q
  simp only at *
  unfold octV; rw [dot_vecOf]
  show dotF (octF o m) (octF o' m') ≤ 4
  by_cases hpq : o = o'
  · subst hpq
    have hm : m ≠ m' := fun h => hne (by rw [h])
    obtain ⟨k, hk, hk2⟩ := testBit_differ o m m' hsub hsub' hl hl' hm
    exact dot_oct_same_le o m m' hp hpm hqm ⟨k, hk, hk2⟩
  · have := dot_oct_le_cnt o m o' m'
    have := hint hpq; omega

theorem sgn_ones : ∀ (s x : List Int), (∀ a ∈ s, a = 1) → x.length ≤ s.length → sgn s x = x
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, _ => by simp [sgn]
  | a :: as, b :: bs, hs, hl => by
      simp only [sgn]
      rw [hs a (by simp), Int.one_mul, sgn_ones as bs (fun c hc => hs c (by simp [hc])) (by simp at hl; omega)]

theorem main_pairwise (octData : List (Nat × Nat)) (rootData : List (Nat × Nat × Int × Int))
    (octads : List Nat) (reps : List (List Int)) (grpM : List Nat)
    (hOct : ∀ p ∈ octData, p.1 ∈ octads ∧ cnt 20 p.1 = 8 ∧ cnt 20 (p.1 &&& p.2) % 2 = 1 ∧
      p.2 &&& p.1 = p.2 ∧ p.2 < 2 ^ 20)
    (hOctNodup : octData.Nodup) (hRootNodup : rootData.Nodup)
    (hOctads : ∀ o ∈ octads, ∀ o' ∈ octads, o ≠ o' → cnt 20 (o &&& o') ≤ 4)
    (hRoot : ∀ r ∈ rootData, r.1 < 20 ∧ r.2.1 < 20 ∧ r.1 ≠ r.2.1 ∧ (r.2.2.1 = 2 ∨ r.2.2.1 = -2) ∧
      (r.2.2.2 = 2 ∨ r.2.2.2 = -2))
    (hRR : ∀ r ∈ rootData, ∀ r' ∈ rootData, r = r' ∨ dot (rootV r) (rootV r') ≤ 4)
    (hClosO : ∀ gm ∈ grpM, ∀ p ∈ octData, gO gm p ∈ octData)
    (hClosR : ∀ gm ∈ grpM, ∀ r ∈ rootData, gR gm r ∈ rootData)
    (hGrp : ∀ a ∈ grpM, ∀ b ∈ grpM, a ^^^ b ∈ grpM)
    (hGrpNodup : grpM.Nodup) (hRepsNodup : reps.Nodup)
    (hRepLen : ∀ r ∈ reps, r.length = 20 ∧ 0 < dot r r)
    (hK3 : ∀ r ∈ reps, (∀ p ∈ octData, Compat r (octV p)) ∧ ∀ q ∈ rootData, Compat r (rootV q))
    (hK4 : ∀ r ∈ reps, ∀ r' ∈ reps, ∀ gm ∈ grpM, (gm = 0 ∧ r' = r) ∨ Compat r (sgn (vecOf (signF gm)) r')) :
    (rootData.map rootV ++ octData.map octV ++ grpM.flatMap (fun gm => reps.map (sgn (vecOf (signF gm))))).Pairwise Compat := by
  have isS : ∀ gm, IsSign (vecOf (signF gm)) := isSign_signF
  have inv : ∀ gm (x : List Int), x.length = 20 → sgn (vecOf (signF gm)) (sgn (vecOf (signF gm)) x) = x := by
    intro gm x hx; exact sgn_invol _ x (isS gm) (by rw [length_vecOf, hx] <;> omega)
  have baseLen : ∀ x ∈ rootData.map rootV ++ octData.map octV, x.length = 20 := by
    intro x hx; simp only [List.mem_append, List.mem_map] at hx
    rcases hx with ⟨r, _, rfl⟩ | ⟨p, _, rfl⟩ <;> exact length_vecOf _
  have normO : ∀ p ∈ octData, dot (octV p) (octV p) = 8 := fun p hp => norm_octV p (hOct p hp).2.1
  have normR : ∀ r ∈ rootData, dot (rootV r) (rootV r) = 8 := by
    intro r hr; obtain ⟨h1, h2, h3, ha, hb⟩ := hRoot r hr; exact norm_rootV r h1 h2 h3 ha hb
  have baseClos : ∀ gm ∈ grpM, ∀ x ∈ rootData.map rootV ++ octData.map octV,
      sgn (vecOf (signF gm)) x ∈ rootData.map rootV ++ octData.map octV := by
    intro gm hg x hx; simp only [List.mem_append, List.mem_map] at hx ⊢
    rcases hx with ⟨r, hr, rfl⟩ | ⟨p, hp, rfl⟩
    · left; exact ⟨gR gm r, hClosR gm hg r hr, (sgn_rootV gm r (hRoot r hr).2.2.1).symm⟩
    · right; exact ⟨gO gm p, hClosO gm hg p hp, (sgn_octV gm p).symm⟩
  -- base pairwise
  have pR : (rootData.map rootV).Pairwise Compat := by
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ hRootNodup
    intro r r' hr hr' hne
    apply compat_of_le4 _ (normR r hr) (normR r' hr')
    rcases hRR r hr r' hr' with h | h
    · exact absurd h hne
    · exact h
  have pO : (octData.map octV).Pairwise Compat := by
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ hOctNodup
    intro p q hp hq hne
    apply compat_of_le4 _ (normO p hp) (normO q hq)
    obtain ⟨hpo, hp8, hpm, hps, hpl⟩ := hOct p hp; obtain ⟨hqo, _, hqm, hqs, hql⟩ := hOct q hq
    exact dot_octV_rec p q hp8 hpm hqm (fun h => hOctads p.1 hpo q.1 hqo h) hps hqs hpl hql hne
  have pB : (rootData.map rootV ++ octData.map octV).Pairwise Compat := by
    rw [List.pairwise_append]
    refine ⟨pR, pO, ?_⟩
    intro x hx y hy
    simp only [List.mem_map] at hx hy
    obtain ⟨r, hr, rfl⟩ := hx; obtain ⟨p, hp, rfl⟩ := hy
    apply compat_of_le4 _ (normR r hr) (normO p hp)
    obtain ⟨h1, h2, h3, ha, hb⟩ := hRoot r hr; exact dot_rootV_octV r p h1 h2 h3 ha hb
  -- base vs new
  have baseNew : ∀ x ∈ rootData.map rootV ++ octData.map octV, ∀ gm ∈ grpM, ∀ r ∈ reps,
      Compat x (sgn (vecOf (signF gm)) r) := by
    intro x hx gm hg r hr
    have hxl := baseLen x hx; have hrl := (hRepLen r hr).1
    rw [← compat_sgn (vecOf (signF gm)) x _ (isS gm) (by rw [length_vecOf, hxl] <;> omega)
        (by rw [length_sgn_vecOf gm r hrl, length_vecOf] <;> omega)]
    rw [inv gm r hrl]
    apply Compat.symm
    have hmem := baseClos gm hg x hx
    simp only [List.mem_append, List.mem_map] at hmem
    rcases hmem with ⟨q, hq, hqe⟩ | ⟨p, hp, hpe⟩
    · rw [← hqe]; exact (hK3 r hr).2 q hq
    · rw [← hpe]; exact (hK3 r hr).1 p hp
  -- new pairwise
  have zero_mem : (0 : Nat) ∈ grpM ∨ grpM = [] := by
    cases grpM with
    | nil => right; rfl
    | cons a t => left; have := hGrp a (by simp) a (by simp); rw [Nat.xor_self] at this; exact this
  have pN : (grpM.flatMap (fun gm => reps.map (sgn (vecOf (signF gm))))).Pairwise Compat := by
    rw [List.pairwise_flatMap]
    constructor
    · intro gm hg
      rw [List.pairwise_map]
      refine List.Pairwise.imp_of_mem ?_ hRepsNodup
      intro r r' hr hr' hne
      have hrl := (hRepLen r hr).1; have hrl' := (hRepLen r' hr').1
      rw [compat_sgn _ _ _ (isS gm) (by rw [length_vecOf, hrl] <;> omega) (by rw [length_vecOf, hrl'] <;> omega)]
      have h0 : (0 : Nat) ∈ grpM := by rcases zero_mem with h | h; exact h; subst h; simp at hg
      rcases hK4 r hr r' hr' 0 h0 with ⟨_, h⟩ | h
      · exact absurd h.symm hne
      · have e : sgn (vecOf (signF 0)) r' = r' := sgn_ones _ r' (by decide) (by rw [length_vecOf, hrl'] <;> omega)
        rw [e] at h; exact h
    · refine List.Pairwise.imp_of_mem ?_ hGrpNodup
      intro a b ha hb hab x hx y hy
      simp only [List.mem_map] at hx hy
      obtain ⟨r, hr, rfl⟩ := hx; obtain ⟨r', hr', rfl⟩ := hy
      have hrl := (hRepLen r hr).1; have hrl' := (hRepLen r' hr').1
      rw [← compat_sgn (vecOf (signF a)) _ _ (isS a) (by rw [length_sgn_vecOf a r hrl, length_vecOf] <;> omega)
          (by rw [length_sgn_vecOf b r' hrl', length_vecOf] <;> omega)]
      rw [inv a r hrl, sgn_sgn, sgn_signF_signF]
      rcases hK4 r hr r' hr' (a ^^^ b) (hGrp a ha b hb) with ⟨h, _⟩ | h
      · exfalso; apply hab
        have := congrArg (fun t => t ^^^ b) h
        simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] at this; exact this
      · exact h
  rw [List.pairwise_append]
  refine ⟨pB, pN, ?_⟩
  intro x hx y hy
  simp only [List.mem_flatMap, List.mem_map] at hy
  obtain ⟨gm, hg, r, hr, rfl⟩ := hy
  exact baseNew x hx gm hg r hr

end K19
/-! ## Part 7: generic final assembly from cheap, kernel-checkable data conditions. -/
namespace K19

def keyO' (p : Nat × Nat) : Nat := p.1 * 2 ^ 20 + p.2

def tsumT (v : List Int) : Int := v.getD 0 0 + v.getD 3 0 + v.getD 6 0 + v.getD 8 0

theorem getD_vecOf (f : Nat → Int) (k : Nat) (hk : k < 20) : (vecOf f).getD k 0 = f k := by
  unfold vecOf vecN; simp [List.getD_eq_getElem?_getD, hk]

theorem sgn_list_eq (s : Nat → Int) (r : List Int) (hr : r.length = 20) :
    sgn (vecOf s) r = vecOf (fun k => s k * r.getD k 0) := by
  have h := list_eq_vecN r; rw [hr] at h
  conv => lhs; rw [h]
  unfold vecOf; rw [sgn_vecN]

theorem nodup_of_strictInc_map {α : Type} (f : α → Nat) (l : List α) (h : strictInc (l.map f) = true) : l.Nodup :=
  List.Pairwise.of_map f (fun a b h hab => h (by rw [hab])) (strictInc_nodup _ h)

theorem testBit_of_and_zero (gm c k : Nat) (h : gm &&& c = 0) (hc : c.testBit k = true) :
    gm.testBit k = false := by
  have := congrArg (fun x => Nat.testBit x k) h
  simp only [Nat.testBit_and, hc, Bool.and_true, Nat.zero_testBit] at this
  exact this

theorem okOct_compat (r : List Int) (N : Int) (hN : dot r r = N) (x : List Int) (hx : dot x x = 8) (d : Int)
    (hd : dot r x = d) (h : (decide (d ≤ 0) || decide (4 * (d * d) ≤ N * 8)) = true) : Compat r x := by
  unfold Compat; rw [hd, hN, hx]; simpa using h

/-- everything assembled: if the cheap data conditions hold, the configuration is pairwise compatible,
has no repetitions, lies in the hyperplane, and has the stated length -/
theorem final_generic (octBlocks : List (Nat × List Nat)) (rootData : List (Nat × Nat × Int × Int))
    (reps : List (List Int)) (grpM : List Nat) (N : Nat)
    (cBlocks : ∀ b ∈ octBlocks, cnt 20 b.1 = 8 ∧ ∀ m ∈ b.2, cnt 20 (b.1 &&& m) % 2 = 1 ∧ m &&& b.1 = m ∧ m < 2 ^ 20 ∧
      octF b.1 m 0 + octF b.1 m 3 + octF b.1 m 6 + octF b.1 m 8 = 0)
    (cOctads : ∀ o ∈ octBlocks.map (·.1), ∀ o' ∈ octBlocks.map (·.1), o ≠ o' → cnt 20 (o &&& o') ≤ 4)
    (cOctKey : strictInc ((octBlocks.flatMap (fun b => b.2.map (fun m => (b.1, m)))).map keyO') = true)
    (cRootKey : strictInc (rootData.map keyR) = true)
    (cRoot : ∀ r ∈ rootData, r.1 < 20 ∧ r.2.1 < 20 ∧ r.1 ≠ r.2.1 ∧ (r.2.2.1 = 2 ∨ r.2.2.1 = -2) ∧
      (r.2.2.2 = 2 ∨ r.2.2.2 = -2) ∧ rootF r.1 r.2.1 r.2.2.1 r.2.2.2 0 + rootF r.1 r.2.1 r.2.2.1 r.2.2.2 3 +
        rootF r.1 r.2.1 r.2.2.1 r.2.2.2 6 + rootF r.1 r.2.1 r.2.2.1 r.2.2.2 8 = 0)
    (cRR : ∀ r ∈ rootData, ∀ r' ∈ rootData, r = r' ∨
      r.2.2.1 * rootF r'.1 r'.2.1 r'.2.2.1 r'.2.2.2 r.1 + r.2.2.2 * rootF r'.1 r'.2.1 r'.2.2.1 r'.2.2.2 r.2.1 ≤ 4)
    (cClosB : ∀ b ∈ octBlocks, ∀ gm ∈ grpM, ∀ m ∈ b.2, (m ^^^ (gm &&& b.1)) ∈ b.2)
    (cClosR : ∀ gm ∈ grpM, ∀ r ∈ rootData, gR gm r ∈ rootData)
    (cGrp : ∀ a ∈ grpM, ∀ b ∈ grpM, a ^^^ b ∈ grpM) (cGrpKey : strictInc grpM = true)
    (cGrpT : ∀ gm ∈ grpM, gm &&& 329 = 0)
    (cReps : reps.Nodup)
    (cRepLen : ∀ r ∈ reps, r.length = 20 ∧ 0 < dot r r ∧ tsumT r = 0)
    (cK3 : ∀ r ∈ reps, (∀ b ∈ octBlocks, ∀ m ∈ b.2,
        (decide (dotOct r (posList b.1) m ≤ 0) || decide (4 * (dotOct r (posList b.1) m * dotOct r (posList b.1) m) ≤ dot r r * 8)) = true) ∧
      ∀ q ∈ rootData, (decide (q.2.2.1 * r.getD q.1 0 + q.2.2.2 * r.getD q.2.1 0 ≤ 0) ||
        decide (4 * ((q.2.2.1 * r.getD q.1 0 + q.2.2.2 * r.getD q.2.1 0) * (q.2.2.1 * r.getD q.1 0 + q.2.2.2 * r.getD q.2.1 0)) ≤ dot r r * 8)) = true)
    (cK4 : ∀ r ∈ reps, ∀ r' ∈ reps, ∀ gm ∈ grpM, (gm = 0 ∧ r' = r) ∨ compatB r (sgn (vecOf (signF gm)) r') = true)
    (cLen : (rootData.map rootV ++ (octBlocks.flatMap (fun b => b.2.map (fun m => (b.1, m)))).map octV ++
      grpM.flatMap (fun gm => reps.map (sgn (vecOf (signF gm))))).length = N) :
    ∃ L : List (List Int), L.length = N ∧ L.Nodup ∧ (∀ v ∈ L, v.length = 20 ∧ tsumT v = 0 ∧ 0 < dot v v) ∧
      L.Pairwise Compat := by
  let octData := octBlocks.flatMap (fun b => b.2.map (fun m => (b.1, m)))
  have memOct : ∀ p ∈ octData, ∃ b ∈ octBlocks, p.2 ∈ b.2 ∧ p.1 = b.1 := by
    intro p hp; simp only [octData, List.mem_flatMap, List.mem_map] at hp
    obtain ⟨b, hb, m, hm, rfl⟩ := hp; exact ⟨b, hb, hm, rfl⟩
  have hOct : ∀ p ∈ octData, p.1 ∈ octBlocks.map (·.1) ∧ cnt 20 p.1 = 8 ∧ cnt 20 (p.1 &&& p.2) % 2 = 1 ∧
      p.2 &&& p.1 = p.2 ∧ p.2 < 2 ^ 20 := by
    intro p hp; obtain ⟨b, hb, hm, he⟩ := memOct p hp
    obtain ⟨h8, hms⟩ := cBlocks b hb; obtain ⟨h1, h2, h3, _⟩ := hms p.2 hm
    rw [he]; exact ⟨List.mem_map.2 ⟨b, hb, rfl⟩, h8, h1, h2, h3⟩
  have hRoot : ∀ r ∈ rootData, r.1 < 20 ∧ r.2.1 < 20 ∧ r.1 ≠ r.2.1 ∧ (r.2.2.1 = 2 ∨ r.2.2.1 = -2) ∧
      (r.2.2.2 = 2 ∨ r.2.2.2 = -2) := fun r hr => by
    obtain ⟨a, b, c, d, e, _⟩ := cRoot r hr; exact ⟨a, b, c, d, e⟩
  have hRR : ∀ r ∈ rootData, ∀ r' ∈ rootData, r = r' ∨ dot (rootV r) (rootV r') ≤ 4 := by
    intro r hr r' hr'
    rcases cRR r hr r' hr' with h | h
    · exact Or.inl h
    · right; obtain ⟨h1, h2, h3, _⟩ := hRoot r hr
      unfold rootV; rw [dot_vecOf, dot_root _ _ _ _ _ h3 h1 h2]; exact h
  have hClosO : ∀ gm ∈ grpM, ∀ p ∈ octData, gO gm p ∈ octData := by
    intro gm hg p hp; obtain ⟨b, hb, hm, he⟩ := memOct p hp
    simp only [octData, List.mem_flatMap, List.mem_map]
    refine ⟨b, hb, p.2 ^^^ (gm &&& b.1), cClosB b hb gm hg p.2 hm, ?_⟩
    unfold gO; rw [he]
  have hK3 : ∀ r ∈ reps, (∀ p ∈ octData, Compat r (octV p)) ∧ ∀ q ∈ rootData, Compat r (rootV q) := by
    intro r hr; obtain ⟨hrl, _, _⟩ := cRepLen r hr; obtain ⟨hk3o, hk3r⟩ := cK3 r hr
    constructor
    · intro p hp; obtain ⟨b, hb, hm, he⟩ := memOct p hp
      apply okOct_compat r (dot r r) rfl _ (norm_octV p (hOct p hp).2.1) _ (dot_octV_fast r hrl p)
      rw [he]; exact hk3o b hb p.2 hm
    · intro q hq; obtain ⟨h1, h2, h3, ha, hb⟩ := hRoot q hq
      exact okOct_compat r (dot r r) rfl _ (norm_rootV q h1 h2 h3 ha hb) _ (dot_rootV_fast r hrl q h1 h2 h3) (hk3r q hq)
  have hK4 : ∀ r ∈ reps, ∀ r' ∈ reps, ∀ gm ∈ grpM, (gm = 0 ∧ r' = r) ∨ Compat r (sgn (vecOf (signF gm)) r') := by
    intro r hr r' hr' gm hg
    rcases cK4 r hr r' hr' gm hg with h | h
    · exact Or.inl h
    · exact Or.inr ((compatB_iff _ _).1 h)
  have hPW := main_pairwise octData rootData (octBlocks.map (·.1)) reps grpM hOct
    (nodup_of_strictInc_map keyO' octData cOctKey) (nodup_of_strictInc_map keyR rootData cRootKey)
    cOctads hRoot hRR hClosO cClosR cGrp (strictInc_nodup grpM cGrpKey) cReps
    (fun r hr => ⟨(cRepLen r hr).1, (cRepLen r hr).2.1⟩) hK3 hK4
  -- properties of all points
  have hProp : ∀ v ∈ rootData.map rootV ++ octData.map octV ++ grpM.flatMap (fun gm => reps.map (sgn (vecOf (signF gm)))),
      v.length = 20 ∧ tsumT v = 0 ∧ 0 < dot v v := by
    intro v hv
    simp only [List.mem_append, List.mem_map, List.mem_flatMap] at hv
    rcases hv with (⟨q, hq, rfl⟩ | ⟨p, hp, rfl⟩) | ⟨gm, hg, r, hr, rfl⟩
    · obtain ⟨h1, h2, h3, ha, hb, ht⟩ := cRoot q hq
      refine ⟨length_vecOf _, ?_, by rw [norm_rootV q h1 h2 h3 ha hb]; decide⟩
      unfold tsumT rootV; rw [getD_vecOf _ 0 (by decide), getD_vecOf _ 3 (by decide), getD_vecOf _ 6 (by decide),
        getD_vecOf _ 8 (by decide)]; exact ht
    · obtain ⟨b, hb, hm, he⟩ := memOct p hp
      refine ⟨length_vecOf _, ?_, by rw [norm_octV p (hOct p hp).2.1]; decide⟩
      have ht := ((cBlocks b hb).2 p.2 hm).2.2.2
      unfold tsumT octV; rw [getD_vecOf _ 0 (by decide), getD_vecOf _ 3 (by decide), getD_vecOf _ 6 (by decide),
        getD_vecOf _ 8 (by decide), he]; exact ht
    · obtain ⟨hrl, hpos, ht⟩ := cRepLen r hr
      refine ⟨length_sgn_vecOf gm r hrl, ?_, ?_⟩
      · rw [sgn_list_eq _ r hrl]; unfold tsumT at ht ⊢
        rw [getD_vecOf _ 0 (by decide), getD_vecOf _ 3 (by decide), getD_vecOf _ 6 (by decide), getD_vecOf _ 8 (by decide)]
        have hT := cGrpT gm hg
        have s0 : signF gm 0 = 1 := by
          unfold signF; rw [testBit_of_and_zero gm 329 0 hT (by decide)]; rfl
        have s3 : signF gm 3 = 1 := by
          unfold signF; rw [testBit_of_and_zero gm 329 3 hT (by decide)]; rfl
        have s6 : signF gm 6 = 1 := by
          unfold signF; rw [testBit_of_and_zero gm 329 6 hT (by decide)]; rfl
        have s8 : signF gm 8 = 1 := by
          unfold signF; rw [testBit_of_and_zero gm 329 8 hT (by decide)]; rfl
        rw [s0, s3, s6, s8]; simpa using ht
      · rw [dot_sgn_sgn _ r r (isSign_signF gm) (by rw [length_vecOf, hrl] <;> omega)]; exact hpos
  refine ⟨_, cLen, ?_, hProp, hPW⟩
  exact List.Pairwise.imp_of_mem (fun {x y} hx _ hc => ne_of_compat (hProp x hx).2.2 hc) hPW

end K19
