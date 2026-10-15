/-
  Heilbronn's triangle problem: new best-known configurations (B07, October 14, 2026).

  For a finite planar point set S, m(S) is the least area of a triangle with vertices in S.
  * square   variant: S ⊆ [0,1]²                                   value m(S)
  * triangle variant: S ⊆ T = conv{(0,0),(1,0),(0,1)} (area 1/2)  value m(S)/area(T) = 2·m(S)
    (the problem is affine invariant, so this is the value for every triangle of area 1)
  * convex   variant: S arbitrary                                   value m(S)/area(conv S)

  Every theorem below exhibits an explicit configuration with exact rational coordinates and proves a
  rational lower bound for its value.  Core Lean 4 only (no Mathlib); all arithmetic is checked by the
  kernel (`decide +kernel`) through a Boolean checker whose soundness is proved (`allTriples_sound`).
  No `native_decide`, no `sorry`, no axioms beyond the standard ones.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! ### Shared definitions -/

/-- A point of the plane with rational coordinates. -/
abbrev Pt := Rat × Rat

/-- Twice the signed area of the triangle `a b c`. -/
def cross (a b c : Pt) : Rat := (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

/-- Absolute value on `Rat`. -/
def qabs (x : Rat) : Rat := if x < 0 then -x else x

/-- (Unsigned) area of the triangle `a b c`. -/
def area (a b c : Pt) : Rat := qabs (cross a b c) / 2

/-- `p` lies in the closed unit square `[0,1]²` (area 1). -/
def inSquare (p : Pt) : Prop := 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1
instance (p : Pt) : Decidable (inSquare p) := by unfold inSquare; exact inferInstance

/-- `p` lies in the closed triangle with vertices (0,0), (1,0), (0,1) (area 1/2). -/
def inTriangle (p : Pt) : Prop := 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1
instance (p : Pt) : Decidable (inTriangle p) := by unfold inTriangle; exact inferInstance

/-- Directed edges of the polygon with vertex list `h` (cyclically). -/
def edges (h : List Pt) : List (Pt × Pt) := h.zip (h.rotateLeft 1)

/-- Shoelace area of the polygon with vertex list `h` (positive if counter-clockwise). -/
def polyArea (h : List Pt) : Rat :=
  (((edges h).map (fun e => e.1.1 * e.2.2 - e.2.1 * e.1.2)).foldl (· + ·) 0) / 2

/-- `p` lies in the closed polygon `h`: on the left of, or on, every directed edge. -/
def inPoly (h : List Pt) (p : Pt) : Prop := ∀ e ∈ edges h, 0 ≤ cross e.1 e.2 p

/-- Strict convexity: every vertex not on an edge lies strictly to the left of it. -/
def strictlyConvex (h : List Pt) : Prop :=
  ∀ e ∈ edges h, ∀ p ∈ h, p ≠ e.1 → p ≠ e.2 → 0 < cross e.1 e.2 p

/-! ### Executable checker and its soundness -/

theorem eq_le_trans {x y z : Rat} (h : x = y) (h' : y ≤ z) : x ≤ z := h ▸ h'

def allPairs (g : Pt → Pt → Bool) : List Pt → Bool
  | [] => true
  | b :: rest => rest.all (g b) && allPairs g rest

def allTriples (f : Pt → Pt → Pt → Bool) : List Pt → Bool
  | [] => true
  | a :: rest => allPairs (f a) rest && allTriples f rest

theorem allPairs_sound (g : Pt → Pt → Bool) : ∀ (l : List Pt), allPairs g l = true →
    ∀ b c, List.Sublist [b, c] l → g b c = true
  | [], _, b, c, h => by cases h
  | x :: rest, h, b, c, hs => by
    simp only [allPairs, Bool.and_eq_true, List.all_eq_true] at h
    cases hs with
    | cons _ h2 => exact allPairs_sound g rest h.2 b c h2
    | cons_cons _ h2 => exact h.1 c (h2.subset (List.mem_singleton_self c))

/-- Soundness: if the checker accepts `l`, then `f` holds on every 3-element sublist
    (i.e. on every triple of points of `l`, taken in list order). -/
theorem allTriples_sound (f : Pt → Pt → Pt → Bool) : ∀ (l : List Pt), allTriples f l = true →
    ∀ a b c, List.Sublist [a, b, c] l → f a b c = true
  | [], _, a, b, c, h => by cases h
  | x :: rest, h, a, b, c, hs => by
    simp only [allTriples, Bool.and_eq_true] at h
    cases hs with
    | cons _ h2 => exact allTriples_sound f rest h.2 a b c h2
    | cons_cons _ h2 => exact allPairs_sound (f x) rest h.1 b c h2

/-- Specialisation used for the area bounds (the bound `B` is a variable here, so no large
    literal is ever unfolded by the elaborator). -/
theorem allTriples_area (B : Rat) (l : List Pt)
    (h : allTriples (fun a b c => decide (B ≤ area a b c)) l = true) :
    ∀ a b c, List.Sublist [a, b, c] l → B ≤ area a b c :=
  fun a b c hs => of_decide_eq_true (allTriples_sound _ l h a b c hs)

theorem allTriples_area2 (B : Rat) (l : List Pt)
    (h : allTriples (fun a b c => decide (B ≤ 2 * area a b c)) l = true) :
    ∀ a b c, List.Sublist [a, b, c] l → B ≤ 2 * area a b c :=
  fun a b c hs => of_decide_eq_true (allTriples_sound _ l h a b c hs)


/-! ### Triangle35: triangle variant, n = 35
   exact value of the configuration ≈ 0.004254272489764; certified bound (10635681 / 2500000000 : Rat) ≈ 0.004254272400 -/
namespace Triangle35

/-- The configuration: 35 points (exact decimal coordinates). -/
def config : List Pt := [
  (0.520594042893369172982755669549, 0.140445706835851655575140195442),
  (0.359734053869786375326479469408, 0.517068154112468006514770809220),
  (0.148699971775781610054431535888, 0.516511228459677155277951965697),
  (0.496976903815745458627703037961, 0.376635575408147660657063302926),
  (0.623923886022125119147585702034, 0.349961723103002416430954621417),
  (0.372224113988189366087477614197, 0.036873263957307268612776356987),
  (0.034827666073376531949283334124, 0.655514706260621812376024533413),
  (0.338672718792320846869001697674, 0.632185990732090161524753912780),
  (0.036681308708786258146846549755, 0.372560902926687568102450099130),
  (0.645022394769082250283799456482, 0.033100727926895507507631596126),
  (0.217142614608547674444483116268, 0.782857385391452325555516883732),
  (0.783812112412599202735724170379, 0),
  (0.773417963052923174659771300344, 0.226582036947076825340228699656),
  (0, 0.807193751557804642022037306352),
  (0.006400686913590753664119043675, 0.909611651824121496978784611382),
  (0.022318478295791174373614935360, 0.110702700612560948665904692734),
  (0.261390894749313489111777257490, 0.254814079579031770235426935017),
  (0.246146127097307920770921236017, 0.538552542763836087368814598399),
  (0.527808235310301738624910711365, 0.248433102030968620446993838087),
  (0.187361314636719580022373167498, 0.738721108685523612882542099915),
  (0.131211510948467261327546413473, 0.024611296061329379419909130034),
  (0.099454024525776153946603581214, 0.883780380263575272997631121955),
  (0, 0),
  (0.153920588570581666808209707712, 0.389190445242634699594945264513),
  (0.112171429694268668722190047751, 0.196520391746624858293295827662),
  (0.339235940385385802172862459186, 0.351982597816530209663381206337),
  (0.725536704786036818133922449855, 0.187563119828602489373429054725),
  (0.092083480801931341809911520231, 0.746530511902415370720903406812),
  (0.217034710420189517742449437005, 0.093268907521145663706395743273),
  (0.913688406684297975709388941876, 0.006451240763827268689265244418),
  (0.384163097827336444168936113265, 0.140960279799806838922564498226),
  (0.006400686913590753664119043675, 0.244952913286116121796437494085),
  (0.892325643591237051218224924464, 0.099824890665081192043928687942),
  (0.254238132619490641317213674800, 0.006451240763827268689265244418),
  (0.730787840912826037014239684376, 0.089451195084556861049189289787)]

/-- 35 points in the triangle (0,0),(1,0),(0,1); every triangle they span has (normalised) area ≥ (10635681 / 2500000000 : Rat). -/
theorem main :
    config.length = 35 ∧ (∀ p ∈ config, inTriangle p) ∧
    ∀ a b c : Pt, List.Sublist [a, b, c] config → (10635681 / 2500000000 : Rat) ≤ 2 * area a b c := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · have h : config.all (fun p => decide (inTriangle p)) = true := by decide +kernel
    simpa [List.all_eq_true] using h
  · have h : allTriples (fun a b c => decide ((10635681 / 2500000000 : Rat) ≤ 2 * area a b c)) config = true := by decide +kernel
    exact allTriples_area2 _ config h

end Triangle35

#print axioms Triangle35.main

/-! ### Triangle23: triangle variant, n = 23
   exact value of the configuration ≈ 0.009279055872833; certified bound (1855811 / 200000000 : Rat) ≈ 0.009279055000 -/
namespace Triangle23

/-- The configuration: 23 points (exact decimal coordinates). -/
def config : List Pt := [
  (0.082090447737483445538925066901, 0),
  (0.722835659724518476901595196658, 0.201227121710194908974814094158),
  (0.354823538172297594289615343356, 0.521768373157688194189702044498),
  (0.021383872983332584860355075031, 0.043342534686133365840142470260),
  (0.501345843130695866478866292695, 0.477270283885971548660778632272),
  (0.178288676768485042018585213168, 0.238883209505955966919630249026),
  (0.374255042776349027126942446828, 0.416614507180005801579714526245),
  (0.268855360943547629963398277192, 0.021028508567370430529783912156),
  (0.344014953014288722635895885198, 0.102732816023249360637345158005),
  (0.553252230962461916726758956795, 0.102732816023249360637345158005),
  (0.710116130489081939506817810650, 0.021028508567370430529783912156),
  (0.582828113725558991061784537805, 0.238883209505955966919630249026),
  (0.935273592330534049299502454707, 0.043342534686133365840142470260),
  (0, 0.329363837939718164700980921831),
  (0.670636162060281835299019078168, 0.329363837939718164700980921832),
  (0.209130450043645171293343026926, 0.416614507180005801579714526245),
  (0.917909552262516554461074933098, 0),
  (0.021383872983332584860355075031, 0.477270283885971548660778632272),
  (0.075937218565286614123590709183, 0.201227121710194908974814094158),
  (0.123408088670014211520682612145, 0.521768373157688194189702044498),
  (0.123875466015593268747796905395, 0.752249067968813462504406189209),
  (0.201760478744279815968142622396, 0.798239521255720184031857377604),
  (0, 0.798239521255720184031857377603)]

/-- 23 points in the triangle (0,0),(1,0),(0,1); every triangle they span has (normalised) area ≥ (1855811 / 200000000 : Rat). -/
theorem main :
    config.length = 23 ∧ (∀ p ∈ config, inTriangle p) ∧
    ∀ a b c : Pt, List.Sublist [a, b, c] config → (1855811 / 200000000 : Rat) ≤ 2 * area a b c := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · have h : config.all (fun p => decide (inTriangle p)) = true := by decide +kernel
    simpa [List.all_eq_true] using h
  · have h : allTriples (fun a b c => decide ((1855811 / 200000000 : Rat) ≤ 2 * area a b c)) config = true := by decide +kernel
    exact allTriples_area2 _ config h

end Triangle23

#print axioms Triangle23.main
