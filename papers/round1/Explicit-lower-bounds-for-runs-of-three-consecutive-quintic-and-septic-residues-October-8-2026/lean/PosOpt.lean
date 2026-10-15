/-!
# Erdős Problem #436 — runs of three consecutive quintic residues

Certificate for: there is a prescribed assignment `g` of residues mod 5 to the primes
(`g p = 1` for all primes except 25 listed exceptions) such that EVERY function `f`
that is completely additive mod 5 on `[1, L]` and agrees with `g` on the primes `≤ L`
has no three consecutive zeros `f r ≡ f (r+1) ≡ f (r+2) ≡ 0 (mod 5)` with `1 ≤ r`, `r + 2 ≤ L`.

Applied to `f = ind_P (·) mod 5` (the quintic-residue index modulo a prime `P ≡ 1 (mod 5)`,
`P > L`, whose quintic characters on the primes `≤ L` are prescribed by `g`; infinitely many such
`P` exist by Kummer theory + Chebotarev, see README), this says `r(5,3,P) ≥ L - 1`,
hence `Λ(5,3) ≥ L - 1`.

Lean 4 core only (no Mathlib).  The large finite check is done by `native_decide`
(disclosed: it adds the native-evaluation axiom); all the reasoning from the check to the
theorem is kernel-checked.
-/

/-- The bound `L` up to which the certificate is checked. -/
def L : Nat := 15469

/-- An integer `B` with `(B+1)^2 > L` (so every prime factor `p` with `p*p ≤ L` is `≤ B`). -/
def B : Nat := 124

/-- Primality, defined from scratch. -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ d, d ∣ p → d = 1 ∨ d = p

def g (_p : Nat) : Nat := 1

/-! ## Computational part (only its *checked properties* are used in the proof) -/

/-- Sieve computing, for every `m ≤ n`, the value `Σ_{p^j ∣ m} g p  (mod 5)`. -/
def buildT (n : Nat) : ByteArray := Id.run do
  let mut t : ByteArray := ByteArray.emptyWithCapacity (n + 1)
  for _ in [0:n+1] do t := t.push 0
  let mut comp : ByteArray := ByteArray.emptyWithCapacity (n + 1)
  for _ in [0:n+1] do comp := comp.push 0
  for p in [2:n+1] do
    if comp.get! p == 0 then
      for i in [p:n/p+1] do comp := comp.set! (p * i) 1
      let gp := UInt8.ofNat (g p)
      if gp != 0 then
        let mut q := p
        for _ in [0:64] do
          if q ≤ n then
            for i in [1:n/q+1] do
              let m := q * i
              t := t.set! m ((t.get! m + gp) % 5)
            q := q * p
  return t

/-- The table (computed once). -/
def T : ByteArray := buildT L

/-- Table lookup as a function `ℕ → ℕ`. -/
def Tf (n : Nat) : Nat := (T.get! n).toNat

/-- `loopAll P n = true` iff `P k = true` for all `k < n` (tail-recursive loop). -/
def loopAll (P : Nat → Bool) : Nat → Bool
  | 0 => true
  | k + 1 => P k && loopAll P k

theorem loopAll_sound (P : Nat → Bool) : ∀ n, loopAll P n = true → ∀ k, k < n → P k = true := by
  intro n
  induction n with
  | zero => intro _ k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    intro h k hk
    simp only [loopAll, Bool.and_eq_true] at h
    by_cases hkn : k = n
    · subst hkn; exact h.1
    · exact ih h.2 k (by omega)

/-- Search for a divisor `e` with `d ≤ e`, `e * e ≤ n`. -/
def hsd (n : Nat) : Nat → Nat → Bool
  | _, 0 => false
  | d, fuel + 1 => if n < d * d then false else if n % d = 0 then true else hsd n (d + 1) fuel

theorem hsd_sound (n : Nat) : ∀ fuel d, hsd n d fuel = true → ∃ e, d ≤ e ∧ e * e ≤ n ∧ n % e = 0 := by
  intro fuel
  induction fuel with
  | zero => intro d h; simp [hsd] at h
  | succ fuel ih =>
    intro d h
    simp only [hsd] at h
    by_cases h1 : n < d * d
    · simp [h1] at h
    · by_cases h2 : n % d = 0
      · exact ⟨d, Nat.le_refl d, by omega, h2⟩
      · simp [h1, h2] at h
        obtain ⟨e, he1, he2, he3⟩ := ih (d + 1) h
        exact ⟨e, by omega, he2, he3⟩

/-- For a fixed `p` with table value `tp`, check `T[p*m] ≡ tp + T[m]` for all `2 ≤ m < n`. -/
def pairLoop (p tp : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => (k < 2 || (T.get! (p * k)).toNat % 5 == (tp + (T.get! k).toNat) % 5) && pairLoop p tp k

theorem pairLoop_sound (p tp : Nat) : ∀ n, pairLoop p tp n = true →
    ∀ m, 2 ≤ m → m < n → Tf (p * m) % 5 = (tp + Tf m) % 5 := by
  intro n
  induction n with
  | zero => intro _ m _ hm; exact absurd hm (Nat.not_lt_zero m)
  | succ n ih =>
    intro h m h2 hm
    simp only [pairLoop, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
    by_cases hmn : m = n
    · subst hmn
      rcases h.1 with h1 | h1
      · omega
      · exact h1
    · exact ih h.2 m h2 (by omega)

/-- Quick compositeness certificate: a divisor `e` with `2 ≤ e`, `e*e ≤ n`. -/
def quickComp (n : Nat) : Bool :=
  (4 ≤ n && n % 2 == 0) || (9 ≤ n && n % 3 == 0) || hsd n 5 n

theorem quickComp_sound (n : Nat) (h : quickComp n = true) : ∃ e, 2 ≤ e ∧ e * e ≤ n ∧ n % e = 0 := by
  simp only [quickComp, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with (h | h) | h
  · exact ⟨2, by omega, by omega, h.2⟩
  · exact ⟨3, by omega, by omega, h.2⟩
  · obtain ⟨e, he1, he2, he3⟩ := hsd_sound n n 5 h
    exact ⟨e, by omega, he2, he3⟩

/-- The table agrees with `g` at `n`, unless `n` is visibly composite. -/
def primeOK (n : Nat) : Bool :=
  n < 2 || (T.get! n).toNat % 5 == g n % 5 || quickComp n

/-- No run of three zeros of the table starting at `r`. -/
def winOK (r : Nat) : Bool :=
  r < 1 || L < r + 2 || !((T.get! r).toNat % 5 == 0 && (T.get! (r + 1)).toNat % 5 == 0 &&
    (T.get! (r + 2)).toNat % 5 == 0)

/-- The whole finite check. -/
def bigCheck : Bool :=
  decide (Tf 1 % 5 = 0) &&
  decide (L < (B + 1) * (B + 1)) &&
  loopAll (fun a => !(decide (2 ≤ a) && !(hsd a 2 a)) || pairLoop a (Tf a) (L / a + 1)) (B + 1) &&
  loopAll primeOK (L + 1) &&
  loopAll winOK (L + 1)

theorem bigCheck_true : bigCheck = true := by native_decide

/-! ## Kernel-checked reasoning from the finite check to the theorem -/

theorem no_small_div_of_prime (n : Nat) (hp : IsPrime n) : hsd n 2 n = false := by
  cases h : hsd n 2 n with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨e, he1, he2, he3⟩ := hsd_sound n n 2 h
    have hdvd : e ∣ n := Nat.dvd_of_mod_eq_zero he3
    rcases hp.2 e hdvd with h' | h'
    · omega
    · subst h'
      have : 2 * e ≤ e * e := Nat.mul_le_mul_right e he1
      omega

theorem T_one : Tf 1 % 5 = 0 := by
  have h := bigCheck_true
  simp only [bigCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.1

theorem L_lt_B : L < (B + 1) * (B + 1) := by
  have h := bigCheck_true
  simp only [bigCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.1.2

theorem T_pair (p m : Nat) (hp : IsPrime p) (hpB : p ≤ B) (hm : 2 ≤ m) (hpm : p * m ≤ L) :
    Tf (p * m) % 5 = (Tf p + Tf m) % 5 := by
  have h := bigCheck_true
  simp only [bigCheck, Bool.and_eq_true] at h
  have h1 := loopAll_sound _ (B + 1) h.1.1.2 p (by omega)
  have hns := no_small_div_of_prime p hp
  have h2p : decide (2 ≤ p) = true := decide_eq_true hp.1
  simp only [h2p, hns, Bool.not_false, Bool.and_true, Bool.not_true, Bool.false_or] at h1
  have hp0 : 0 < p := by have := hp.1; omega
  have hm' : m < L / p + 1 := by
    have : m ≤ L / p := (Nat.le_div_iff_mul_le hp0).2 (by rw [Nat.mul_comm]; exact hpm)
    omega
  exact pairLoop_sound p (Tf p) (L / p + 1) h1 m hm hm'

theorem T_prime (n : Nat) (hn : n ≤ L) (hp : IsPrime n) : Tf n % 5 = g n % 5 := by
  have h := bigCheck_true
  simp only [bigCheck, Bool.and_eq_true] at h
  have h1 := loopAll_sound _ (L + 1) h.1.2 n (by omega)
  simp only [primeOK, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
  rcases h1 with (h1 | h1) | h1
  · exact absurd hp.1 (by omega)
  · exact h1
  · obtain ⟨e, he1, he2, he3⟩ := quickComp_sound n h1
    have hdvd : e ∣ n := Nat.dvd_of_mod_eq_zero he3
    rcases hp.2 e hdvd with h' | h'
    · omega
    · subst h'
      have : 2 * e ≤ e * e := Nat.mul_le_mul_right e he1
      omega

theorem T_win (r : Nat) (h1 : 1 ≤ r) (h2 : r + 2 ≤ L) :
    ¬ (Tf r % 5 = 0 ∧ Tf (r + 1) % 5 = 0 ∧ Tf (r + 2) % 5 = 0) := by
  have h := bigCheck_true
  simp only [bigCheck, Bool.and_eq_true] at h
  have hw := loopAll_sound _ (L + 1) h.2 r (by omega)
  simp only [winOK, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.and_eq_false_iff,
    beq_eq_false_iff_ne] at hw
  intro ⟨z0, z1, z2⟩
  unfold Tf at z0 z1 z2
  rcases hw with (hw | hw) | hw
  · omega
  · omega
  · rcases hw with (hw | hw) | hw <;> contradiction

/-- A number `n ≥ 2` that is not prime is a product `a * b` with `2 ≤ a ≤ b`. -/
theorem split_composite (n : Nat) (h2 : 2 ≤ n) (hp : ¬ IsPrime n) :
    ∃ a b, n = a * b ∧ 2 ≤ a ∧ a ≤ b := by
  have hex : ∃ d, d ∣ n ∧ ¬ (d = 1 ∨ d = n) := by
    apply Classical.byContradiction
    intro hne
    apply hp
    refine ⟨h2, fun d hd => ?_⟩
    apply Classical.byContradiction
    intro hd'
    exact hne ⟨d, hd, hd'⟩
  obtain ⟨d, ⟨e, he⟩, hd⟩ := hex
  have hd1 : d ≠ 1 := fun h => hd (Or.inl h)
  have hdn : d ≠ n := fun h => hd (Or.inr h)
  have hd0 : d ≠ 0 := by intro h; subst h; simp at he; omega
  have he0 : e ≠ 0 := by intro h; subst h; simp at he; omega
  have he1 : e ≠ 1 := by intro h; subst h; simp at he; exact hdn he.symm
  by_cases hde : d ≤ e
  · exact ⟨d, e, he, by omega, hde⟩
  · exact ⟨e, d, by rw [he, Nat.mul_comm], by omega, by omega⟩

/-- Every `n ≥ 2` has a prime divisor. -/
theorem exists_prime_dvd : ∀ N n, n < N → 2 ≤ n → ∃ p, IsPrime p ∧ p ∣ n := by
  intro N
  induction N with
  | zero => intro n hn; exact absurd hn (Nat.not_lt_zero n)
  | succ N ih =>
    intro n hn h2
    by_cases hp : IsPrime n
    · exact ⟨n, hp, Nat.dvd_refl n⟩
    · obtain ⟨a, b, hab, ha, hab'⟩ := split_composite n h2 hp
      have hb2 : 2 ≤ b := by omega
      have h1 : a * 2 ≤ a * b := Nat.mul_le_mul_left a hb2
      obtain ⟨p, hpp, hpa⟩ := ih a (by omega) ha
      exact ⟨p, hpp, Nat.dvd_trans hpa ⟨b, hab⟩⟩

/-- Any completely-additive-mod-5 `f` agreeing with `g` on primes agrees with the table on `[1, L]`. -/
theorem agree (f : Nat → Nat)
    (hmul : ∀ a b, 1 ≤ a → 1 ≤ b → a * b ≤ L → f (a * b) % 5 = (f a + f b) % 5)
    (hprime : ∀ p, p ≤ L → IsPrime p → f p % 5 = g p % 5) :
    ∀ N n, n < N → 1 ≤ n → n ≤ L → f n % 5 = Tf n % 5 := by
  intro N
  induction N with
  | zero => intro n hn; exact absurd hn (Nat.not_lt_zero n)
  | succ N ih =>
    intro n hn h1 hL
    by_cases hlt : n < N
    · exact ih n hlt h1 hL
    · by_cases hn1 : n = 1
      · subst hn1
        have h11 := hmul 1 1 (Nat.le_refl 1) (Nat.le_refl 1) (by unfold L; omega)
        simp only [Nat.mul_one] at h11
        have := T_one
        omega
      · have h2 : 2 ≤ n := by omega
        by_cases hp : IsPrime n
        · rw [hprime n hL hp, T_prime n hL hp]
        · obtain ⟨a, b, hab, ha, hab'⟩ := split_composite n h2 hp
          obtain ⟨p, hpp, hpa⟩ := exists_prime_dvd (a + 1) a (by omega) ha
          have hpa' : p ≤ a := Nat.le_of_dvd (by omega) hpa
          have hpp2 := hpp.1
          have hsq1 : p * p ≤ a * a := Nat.mul_le_mul hpa' hpa'
          have hsq2 : a * a ≤ a * b := Nat.mul_le_mul_left a hab'
          have hpB : p ≤ B := by
            apply Classical.byContradiction
            intro hc
            have hc' : B + 1 ≤ p := by omega
            have : (B + 1) * (B + 1) ≤ p * p := Nat.mul_le_mul hc' hc'
            have := L_lt_B
            omega
          have hpn : p ∣ n := Nat.dvd_trans hpa ⟨b, hab⟩
          obtain ⟨m, hm⟩ := hpn
          have hp0 : 0 < p := by omega
          have hpm : p ≤ m := by
            have : p * p ≤ p * m := by omega
            exact Nat.le_of_mul_le_mul_left this hp0
          have hm2 : 2 ≤ m := by omega
          have hpm2 : p * 2 ≤ p * m := Nat.mul_le_mul_left p hm2
          have hmm : 2 * m ≤ p * m := Nat.mul_le_mul_right m hpp2
          have ihp := ih p (by omega) (by omega) (by omega)
          have ihm := ih m (by omega) (by omega) (by omega)
          have hf := hmul p m (by omega) (by omega) (by omega)
          have ht := T_pair p m hpp hpB hm2 (by omega)
          rw [hm, hf, ht, Nat.add_mod, ihp, ihm, ← Nat.add_mod]

/-- **Main theorem.** For the explicit prime assignment `g`, no completely additive (mod 5)
function agreeing with `g` on the primes has three consecutive zeros in `[1, L]`. -/
theorem no_three_consecutive_quintic_residues (f : Nat → Nat)
    (hmul : ∀ a b, 1 ≤ a → 1 ≤ b → a * b ≤ L → f (a * b) % 5 = (f a + f b) % 5)
    (hprime : ∀ p, p ≤ L → IsPrime p → f p % 5 = g p % 5) :
    ∀ r, 1 ≤ r → r + 2 ≤ L → ¬ (f r % 5 = 0 ∧ f (r + 1) % 5 = 0 ∧ f (r + 2) % 5 = 0) := by
  intro r h1 h2 hz
  have a0 := agree f hmul hprime (r + 1) r (by omega) h1 (by omega)
  have a1 := agree f hmul hprime (r + 2) (r + 1) (by omega) (by omega) (by omega)
  have a2 := agree f hmul hprime (r + 3) (r + 2) (by omega) (by omega) h2
  apply T_win r h1 h2
  rw [← a0, ← a1, ← a2]
  exact hz

#print axioms bigCheck_true
#print axioms no_three_consecutive_quintic_residues
