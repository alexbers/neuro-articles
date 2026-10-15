/-
  A12: a balanced 13-variable Boolean function with absolute indicator 112 < 2^7 = 128,
  of algebraic degree >= 3 -- a counterexample to the Zhang--Zheng (1995) conjecture for n = 13.
  Core Lean 4 only (no Mathlib). All computations are checked by the kernel (`decide +kernel`).
-/
set_option Elab.async false

namespace A12

/-! ## The function and the definitions used in the main theorem -/

/-- Truth table of `f : 𝔽₂¹³ → 𝔽₂`: bit `x` of `tt` is `f x`, where an input
`(x₀,…,x₁₂)` is encoded as the natural number `x = Σ xᵢ 2ⁱ < 2^13`. -/
def tt : Nat := 0xffeafdcdeba3a0e7e8cf885b8914b96efd80b4afd1d436dac5c60734de9228e9eff6d450ce35c8bee247f7205e69a3d8a137e438517b5b64f3b8861c1cd4a882e8aafe78e3253354a1ad0f67f4d1dafdb81d206beb7a0d0036e87987995ff3c18d171b6ef9255ac436122fce638b6861bb4ade94907d47a516e1f3758cc5815cf9d18dc9faed2f84b91f1c671b1b6675dc1398f244bf3c2aeb75f743b298feb28bd112a30c543d9bf99e6ed844e240510b2cfcc47ed3802b828662affa0be013c1f2463a538f78ecaed7586236c9a1705e6857480ceee0e8394a859b2c817d47de8e65d8b2a8c220c3102af3642b98334669f842fa4e7b37c4a0e176840767b5ef83b213c5b6f5c2fed9bce21cab85708e9317eb12a4693a539b478a2d3d6b73a6b5170fc2d4be0c20749eea1fe01988ac9b7a62ee7a244fde0882c0eab9cb5dc0dee64646188c5a55b536604ae7c28bbfc6d6b87ce9e2847570b9497011271215cf1da4bfe4a0206bede31e8511498f945d9039381c88bfbbd804dfa905035ba016af1c75295edc330fc4ae6ac0bcb1c8edf66f67d12c095a69a09298532b1136e969c5666a648545e0b8eda814fdd15b83249d8027928e1da1c0077bb2756fe3ac85b83c37e695da0c9880a14d4815b15f4301088def0b6821498bc2d45e5f607c79d7fe857119bb8935b96f8e5e6fe071d914a8132f3d8131116f3d3fdb76f8fb910b8b0d165af063de6cba36e409beeca7868bf0e91c17a4dddad4266e0080ec935e133bedcf47099c3068d35fd9375ad3ca643a918958e64fb369df2b1edd39cb32576b55afe54ca7609ff944e41d412e75d6aca88d12eaed010283c1859ca4d3ca2fc8691ce8f82a88583521fbe2bc4080940da145a9c8cad7a09e23b7b145b6f8ed68613c25794294d5b0379d27738e620e68785025c8ac2be008859f8eaaa42cf7688b817ae4e982fc59c5347b727a009b9635936f4546075c2f131d0636f1ee53a288658bebbd21c9044d15699ba8a3b84b06fdd12703427183d4fb923467a7c2401b875f9103b181918eef8edfe3d55175b2eb8dd60537155b77decd51136cc9ea46a16a321c9672fce2a00a5e55bbb1648dfd7cd8a451cab59f16f594f9f3ba387daa792fe20348b1019362d838968c00c71d8680631b188f06175b6cb8963d86f4773d2828cc382180372022f811ca90edb6dcc05675bba3e35726dad00b197192b79501492fd318d1ed46b38853f515152b2f9fdf493e377dfebd5a98a18466ce800ef55a3fec2d8776f6dd44f0d38185158c4620b720954327da4672ef700a410700c584b6e8ef519f2cc15d477193d4dba50df77137f967fe7c412aa02fc7a33eefacd1372a070793cacbc0930b268bd729fbd5ed33fd7dbee9003b16b2d703358985121f1dfb5ff690564f1713477dfe4eb75bfea7de3e68

/-- The Boolean function. -/
def f (x : Nat) : Bool := tt.testBit x

/-- `(-1)^b` -/
def sgn (b : Bool) : Int := if b then -1 else 1

/-- Autocorrelation `r_f(d) = Σ_{x ∈ 𝔽₂¹³} (-1)^(f(x) ⊕ f(x ⊕ d))` (`^^^` is bitwise xor). -/
def autocorr (d : Nat) : Int := ((List.range (2^13)).map (fun x => sgn (f x ^^ f (x ^^^ d)))).sum

/-- Hamming weight of `f` (number of inputs with `f x = 1`). -/
def weight : Nat := ((List.range (2^13)).filter f).length

/-- Coefficient of the monomial `∏_{i ∈ u} xᵢ` in the algebraic normal form of `f`
(binary Möbius transform): `a_u = ⊕_{x ⪯ u} f(x)`, where `x ⪯ u` iff `x &&& u = x`. -/
def anfCoeff (u : Nat) : Bool :=
  ((List.range (2^13)).filter (fun x => x &&& u == x)).foldl (fun b x => b ^^ f x) false

/-- Number of variables in the monomial `u` (popcount of `u < 2^13`). -/
def monoDeg (u : Nat) : Nat := ((List.range 13).filter (fun i => u.testBit i)).length

/-- **The certified statement** (proved at the end of the file as `main`, and as
`main_statement : MainStatement`): `f` is balanced, has algebraic degree `≥ 3`, and its absolute
indicator `Δ_f = max_{d ≠ 0} |r_f(d)|` is at most `112 < 2^7 = 128`. -/
def MainStatement : Prop :=
  weight = 2^12 ∧
  (∃ u, u < 2^13 ∧ 3 ≤ monoDeg u ∧ anfCoeff u = true) ∧
  (∀ d, 0 < d → d < 2^13 → (autocorr d).natAbs ≤ 112)

/-! ## Auxiliary machinery: fast, kernel-friendly evaluation of the autocorrelation -/

def N : Nat := 2^13

theorem sum_sgn (L : List Nat) (p : Nat → Bool) :
    (L.map (fun x => sgn (p x))).sum = (L.length : Int) - 2 * ((L.filter p).length : Int) := by
  induction L with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih, List.filter_cons]
    cases h : p a <;> simp [sgn] <;> omega

def cntBits (V m : Nat) : Nat := ((List.range m).filter (fun x => V.testBit x)).length

theorem cntBits_succ (V m : Nat) : cntBits V (m+1) = cntBits V m + (V.testBit m).toNat := by
  unfold cntBits
  rw [List.range_succ, List.filter_append, List.length_append]
  cases h : V.testBit m <;> simp [h]

theorem cntBits_zero (V : Nat) : cntBits V 0 = 0 := by simp [cntBits]

theorem cntBits_le (V m : Nat) : cntBits V m ≤ m := by
  induction m with
  | zero => simp [cntBits_zero]
  | succ m ih => rw [cntBits_succ]; cases V.testBit m <;> simp <;> omega

theorem cntBits_add (V a m : Nat) : cntBits V (a + m) = cntBits V a + cntBits (V >>> a) m := by
  induction m with
  | zero => simp [cntBits_zero]
  | succ m ih =>
    rw [← Nat.add_assoc, cntBits_succ, ih, cntBits_succ, Nat.testBit_shiftRight]
    omega

/-- `D q` has ones exactly at bit positions `14*j`, `j < q`. -/
theorem filter_len_congr (m : Nat) (p q : Nat → Bool) (h : ∀ x, x < m → p x = q x) :
    ((List.range m).filter p).length = ((List.range m).filter q).length := by
  congr 1
  apply List.filter_congr
  intro x hx
  exact h x (List.mem_range.mp hx)

def D : Nat → Nat
  | 0 => 0
  | q+1 => 2^14 * D q + 1

theorem and_D_succ (A E : Nat) : A &&& (2^14 * E + 1) = 2^14 * ((A >>> 14) &&& E) + A % 2 := by
  apply Nat.eq_of_testBit_eq
  intro j
  have h1 : (1:Nat) < 2^14 := by decide
  have h2 : A % 2 < 2^14 := by have := Nat.mod_lt A (show 0 < 2 by decide); omega
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2]
  by_cases hj : j < 14
  · simp only [hj, ite_true]
    have e2 : A % 2 = A % 2^1 := rfl
    have e1 : (1:Nat) = 2^0 := rfl
    rw [e2, Nat.testBit_mod_two_pow, e1, Nat.testBit_two_pow]
    by_cases h0 : j = 0
    · subst h0; simp
    · have : ¬ (j < 1) := by omega
      simp [this]; intro; omega
  · simp only [hj, ite_false, Nat.testBit_and, Nat.testBit_shiftRight]
    have : 14 + (j - 14) = j := by omega
    rw [this]

def sum14 (g : Nat → Nat) : Nat :=
  g 0 + g 1 + g 2 + g 3 + g 4 + g 5 + g 6 + g 7 + g 8 + g 9 + g 10 + g 11 + g 12 + g 13

/-- `Y V q = Σ_{t<14} ((V >>> t) &&& D q)`: its base-2^14 digits are the bit counts of the
14-bit blocks of `V`. -/
def Y (V q : Nat) : Nat := sum14 (fun t => (V >>> t) &&& D q)

theorem cntBits_14 (V : Nat) : cntBits V 14 = sum14 (fun t => (V.testBit t).toNat) := by
  simp only [sum14, cntBits_succ, cntBits_zero]
  omega

theorem Y_succ (V q : Nat) : Y V (q+1) = 2^14 * Y (V >>> 14) q + cntBits V 14 := by
  have key : ∀ t, (V >>> t) &&& D (q+1) = 2^14 * ((V >>> 14 >>> t) &&& D q) + (V.testBit t).toNat := by
    intro t
    show (V >>> t) &&& (2^14 * D q + 1) = _
    rw [and_D_succ, ← Nat.shiftRight_add, ← Nat.shiftRight_add, Nat.add_comm t 14,
      Nat.toNat_testBit]
    simp only [Nat.shiftRight_eq_div_pow]
  simp only [Y, sum14, key, cntBits_14]
  omega

theorem Y_mod (q : Nat) : ∀ V, Y V q % 16383 = cntBits V (14 * q) % 16383 := by
  induction q with
  | zero => intro V; simp [Y, sum14, D, cntBits_zero]
  | succ q ih =>
    intro V
    rw [Y_succ, Nat.mul_succ, Nat.add_comm (14*q) 14, cntBits_add]
    have h16 : (2^14 : Nat) = 16383 + 1 := rfl
    rw [Nat.add_mod, h16, Nat.add_mul, Nat.one_mul, Nat.add_mod (16383 * _) _, Nat.mul_mod_right,
      Nat.zero_add, Nat.mod_mod, ih, ← Nat.add_mod, Nat.add_comm]


/-- `M i` has a one exactly at the positions `x < 2^13` whose bit `i` is zero. -/
def M (i : Nat) : Nat := (2^(2^i) - 1) * ((2^N - 1) / (2^(2^(i+1)) - 1))

/-- swap the two halves of every block of length `2^(i+1)`: realises `x ↦ x xor 2^i` on bit indices -/
def swapBlk (i U : Nat) : Nat := ((U >>> 2^i) &&& M i) ||| ((U &&& M i) <<< 2^i)

def factOK (i x : Nat) : Bool :=
  decide (x ^^^ 2^i < N) &&
  (if x.testBit i then
    (!(M i).testBit x) && decide (2^i ≤ x) && (x ^^^ 2^i == x - 2^i) && (M i).testBit (x - 2^i)
  else
    (M i).testBit x && (x ^^^ 2^i == 2^i + x) && (!decide (2^i ≤ x) || !(M i).testBit (x - 2^i)))

theorem facts0 : ((List.range N).all fun x => factOK 0 x) = true := by decide +kernel
theorem facts1 : ((List.range N).all fun x => factOK 1 x) = true := by decide +kernel
theorem facts2 : ((List.range N).all fun x => factOK 2 x) = true := by decide +kernel
theorem facts3 : ((List.range N).all fun x => factOK 3 x) = true := by decide +kernel
theorem facts4 : ((List.range N).all fun x => factOK 4 x) = true := by decide +kernel
theorem facts5 : ((List.range N).all fun x => factOK 5 x) = true := by decide +kernel
theorem facts6 : ((List.range N).all fun x => factOK 6 x) = true := by decide +kernel
theorem facts7 : ((List.range N).all fun x => factOK 7 x) = true := by decide +kernel
theorem facts8 : ((List.range N).all fun x => factOK 8 x) = true := by decide +kernel
theorem facts9 : ((List.range N).all fun x => factOK 9 x) = true := by decide +kernel
theorem facts10 : ((List.range N).all fun x => factOK 10 x) = true := by decide +kernel
theorem facts11 : ((List.range N).all fun x => factOK 11 x) = true := by decide +kernel
theorem facts12 : ((List.range N).all fun x => factOK 12 x) = true := by decide +kernel

theorem facts_i : ∀ i, i < 13 → ((List.range N).all fun x => factOK i x) = true
  | 0, _ => facts0
  | 1, _ => facts1
  | 2, _ => facts2
  | 3, _ => facts3
  | 4, _ => facts4
  | 5, _ => facts5
  | 6, _ => facts6
  | 7, _ => facts7
  | 8, _ => facts8
  | 9, _ => facts9
  | 10, _ => facts10
  | 11, _ => facts11
  | 12, _ => facts12
  | _+13, h => absurd h (by omega)

theorem fact_of {i x : Nat} (hi : i < 13) (hx : x < N) : factOK i x = true := by
  have h := facts_i i hi
  simp only [List.all_eq_true, List.mem_range] at h
  exact h x hx

theorem swapBlk_testBit (U : Nat) {i x : Nat} (hi : i < 13) (hx : x < N) :
    (swapBlk i U).testBit x = U.testBit (x ^^^ 2^i) := by
  have h := fact_of hi hx
  simp only [factOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨_, h⟩ := h
  simp only [swapBlk, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  split at h
  · simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    rw [h1, h4, h3]
    simp [h2]
  · simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at h
    obtain ⟨⟨h1, h3⟩, h4⟩ := h
    rw [h1, h3]
    rcases h4 with h4 | h4
    · simp [h4, Nat.add_comm]
    · simp [h4, Nat.add_comm]

theorem xor_lt_of_fact {i x : Nat} (hi : i < 13) (hx : x < N) : x ^^^ 2^i < N := by
  have h := fact_of hi hx
  simp only [factOK, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

/-- apply `swapBlk i` for every bit `i < 13` of `d` -/
def permAux (d : Nat) : Nat → Nat → Nat → Nat
  | 0, _, U => U
  | k+1, i, U => permAux d k (i+1) (if d.testBit i then swapBlk i U else U)

def accAux (d : Nat) : Nat → Nat → Nat → Nat
  | 0, _, a => a
  | k+1, i, a => accAux d k (i+1) (if d.testBit i then a ^^^ 2^i else a)

theorem permAux_spec (T d : Nat) : ∀ k i U a, i + k ≤ 13 →
    (∀ x, x < N → U.testBit x = T.testBit (x ^^^ a)) →
    ∀ x, x < N → (permAux d k i U).testBit x = T.testBit (x ^^^ accAux d k i a) := by
  intro k
  induction k with
  | zero => intro i U a _ hU x hx; exact hU x hx
  | succ k ih =>
    intro i U a hik hU x hx
    simp only [permAux, accAux]
    apply ih (i+1) _ _ (by omega) _ x hx
    intro y hy
    by_cases hb : d.testBit i
    · simp only [hb, ite_true]
      rw [swapBlk_testBit U (by omega) hy, hU _ (xor_lt_of_fact (by omega) hy), Nat.xor_assoc,
        Nat.xor_comm (2^i) a]
    · simp only [hb]; exact hU y hy

def perm (d U : Nat) : Nat := permAux d 13 0 U

def accAll : Bool := (List.range N).all fun d => accAux d 13 0 0 == d
theorem accAll_true : accAll = true := by decide +kernel

theorem perm_testBit (T : Nat) {d x : Nat} (hd : d < N) (hx : x < N) :
    (perm d T).testBit x = T.testBit (x ^^^ d) := by
  have h := permAux_spec T d 13 0 T 0 (by omega) (by intro y _; rw [Nat.xor_zero]) x hx
  have hacc : accAux d 13 0 0 = d := by
    have := accAll_true
    simp only [accAll, List.all_eq_true, List.mem_range, beq_iff_eq] at this
    exact this d hd
  rw [hacc] at h
  exact h

/-- fast population count of the low `2^13` bits of `V`, via `Y` and reduction mod `2^14 - 1` -/
def popc (V : Nat) : Nat := Y (V &&& (2^N - 1)) 586 % 16383

theorem popc_eq (V : Nat) : popc V = cntBits V N := by
  have h1 := Y_mod 586 (V &&& (2^N - 1))
  have hsplit : cntBits (V &&& (2^N - 1)) (14 * 586) = cntBits (V &&& (2^N - 1)) N + cntBits ((V &&& (2^N - 1)) >>> N) 12 := by
    have e : (14 * 586 : Nat) = N + 12 := rfl
    rw [e, cntBits_add]
  have hhigh : cntBits ((V &&& (2^N - 1)) >>> N) 12 = 0 := by
    have : ∀ m, m ≤ 12 → cntBits ((V &&& (2^N - 1)) >>> N) m = 0 := by
      intro m
      induction m with
      | zero => intro; exact cntBits_zero _
      | succ m ih =>
        intro hm
        rw [cntBits_succ, ih (by omega), Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
        simp
    exact this 12 (by omega)
  have hlow : cntBits (V &&& (2^N - 1)) N = cntBits V N := by
    unfold cntBits
    apply filter_len_congr
    intro x hx
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    simp [hx]
  have hle := cntBits_le V N
  have hN : N = 8192 := rfl
  unfold popc
  rw [h1, hsplit, hhigh, hlow, Nat.add_zero]
  apply Nat.mod_eq_of_lt
  omega

/-- the count `#{x < 2^13 : f x ≠ f (x ⊕ d)}` lies in `[4040, 4152]` -/
def acOK (d : Nat) : Bool :=
  let c := popc (tt ^^^ perm d tt)
  decide (4040 ≤ c) && decide (c ≤ 4152)

theorem chk0 : ((List.range 1024).all fun j => (1024*0 + j == 0) || acOK (1024*0 + j)) = true := by decide +kernel
theorem chk1 : ((List.range 1024).all fun j => (1024*1 + j == 0) || acOK (1024*1 + j)) = true := by decide +kernel
theorem chk2 : ((List.range 1024).all fun j => (1024*2 + j == 0) || acOK (1024*2 + j)) = true := by decide +kernel
theorem chk3 : ((List.range 1024).all fun j => (1024*3 + j == 0) || acOK (1024*3 + j)) = true := by decide +kernel
theorem chk4 : ((List.range 1024).all fun j => (1024*4 + j == 0) || acOK (1024*4 + j)) = true := by decide +kernel
theorem chk5 : ((List.range 1024).all fun j => (1024*5 + j == 0) || acOK (1024*5 + j)) = true := by decide +kernel
theorem chk6 : ((List.range 1024).all fun j => (1024*6 + j == 0) || acOK (1024*6 + j)) = true := by decide +kernel
theorem chk7 : ((List.range 1024).all fun j => (1024*7 + j == 0) || acOK (1024*7 + j)) = true := by decide +kernel

theorem acOK_all (d : Nat) (hd0 : 0 < d) (hd : d < N) : acOK d = true := by
  have hN : N = 8192 := rfl
  have key : ∀ k, k < 8 → ((List.range 1024).all fun j => (1024*k + j == 0) || acOK (1024*k + j)) = true := by
    intro k hk
    match k, hk with
    | 0, _ => exact chk0
    | 1, _ => exact chk1
    | 2, _ => exact chk2
    | 3, _ => exact chk3
    | 4, _ => exact chk4
    | 5, _ => exact chk5
    | 6, _ => exact chk6
    | 7, _ => exact chk7
    | _+8, h => exact absurd h (by omega)
  have h := key (d / 1024) (by omega)
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  have hd' : 1024 * (d / 1024) + d % 1024 = d := Nat.div_add_mod d 1024
  rcases h (d % 1024) (Nat.mod_lt _ (by omega)) with h | h
  · omega
  · rw [hd'] at h; exact h

theorem autocorr_eq (d : Nat) (hd : d < N) :
    autocorr d = 8192 - 2 * (popc (tt ^^^ perm d tt) : Int) := by
  unfold autocorr
  rw [sum_sgn, List.length_range, popc_eq]
  have : ((List.range (2^13)).filter (fun x => f x ^^ f (x ^^^ d))).length = cntBits (tt ^^^ perm d tt) N := by
    unfold cntBits
    apply filter_len_congr
    intro x hx
    rw [Nat.testBit_xor, perm_testBit tt hd hx]
    rfl
  rw [this]
  rfl

theorem weight_eq : weight = 2^12 := by
  have h : weight = popc tt := by
    rw [popc_eq]; rfl
  rw [h]
  decide +kernel

/-! ## Main theorem -/

/-- **Main theorem.** `f` is a balanced Boolean function of 13 variables, of algebraic degree at
least 3, whose absolute indicator `Δ_f = max_{d ≠ 0} |r_f(d)|` is at most 112 < 2^7 = 128.
This disproves the Zhang--Zheng conjecture `Δ_f ≥ 2^⌊(n+1)/2⌋` for `n = 13`. -/
theorem main :
    weight = 2^12 ∧
    (∃ u, u < 2^13 ∧ 3 ≤ monoDeg u ∧ anfCoeff u = true) ∧
    (∀ d, 0 < d → d < 2^13 → (autocorr d).natAbs ≤ 112) := by
  refine ⟨weight_eq, ⟨7, by decide, by decide +kernel, by decide +kernel⟩, ?_⟩
  intro d hd0 hd
  have h := acOK_all d hd0 hd
  simp only [acOK, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [autocorr_eq d hd]
  omega

theorem main_statement : MainStatement := main

/-- The Zhang--Zheng bound `2^⌊(13+1)/2⌋ = 128` fails for this balanced degree-≥3 function. -/
theorem zhang_zheng_fails_n13 :
    ∃ g : Nat → Bool,
      ((List.range (2^13)).filter g).length = 2^12 ∧
      (∃ u, u < 2^13 ∧ 3 ≤ monoDeg u ∧
        ((List.range (2^13)).filter (fun x => x &&& u == x)).foldl (fun b x => b ^^ g x) false = true) ∧
      (∀ d, 0 < d → d < 2^13 →
        (((List.range (2^13)).map (fun x => sgn (g x ^^ g (x ^^^ d)))).sum).natAbs < 2^((13+1)/2)) := by
  obtain ⟨h1, h2, h3⟩ := main
  refine ⟨f, h1, h2, fun d hd0 hd => ?_⟩
  have := h3 d hd0 hd
  unfold autocorr at this
  have : (2:Nat)^((13+1)/2) = 128 := rfl
  omega

end A12

#print axioms A12.main
#print axioms A12.main_statement
#print axioms A12.zhang_zheng_fails_n13
