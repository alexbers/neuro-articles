/-!
# New lower bounds for hypergraph Ramsey numbers (B02, October 14, 2026)

Five explicit colourings, each checked by the Lean kernel (`decide +kernel`, no `native_decide`):
* `R453.main`: R(4,5;3) ≥ 38  (2-colouring of the triples of {0,…,36}, no red K₄^(3), no blue K₅^(3))
* `R453f.main`: the same bound, re-checked without using any symmetry (kernel search over all tuples)
* `R553.main`: R(5,5;3) ≥ 98  (2-colouring of the triples of {0,…,96}, no monochromatic K₅^(3))
* `R463.main`: R(4,6;3) ≥ 68  (2-colouring of the triples of {0,…,66}, no red K₄^(3), no blue K₆^(3))
* `R554.main`: R(5,5;4) ≥ 38  (2-colouring of the 4-sets of {0,…,36}, no monochromatic K₅^(4))
* `R564.main`: R(5,6;4) ≥ 80  (2-colouring of the 4-sets of {0,…,78}, no red K₅^(4), no blue K₆^(4))

A colouring of the r-subsets of {0,…,N-1} is given as a Boolean function `col` on increasing r-tuples
(true = red). Each colouring is defined from the differences to the smallest element, hence it is
translation invariant; the kernel checks that no monochromatic clique contains the vertex 0, and
`col_shift` reduces an arbitrary clique to one containing 0.
-/

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

#print axioms R453.main


namespace R453f

/-- the colouring: the triple `x<y<z` of `{0,…,36}` is red iff bit `x*1369+y*37+z` of `Fmask` is 1 -/
def Fmask : Nat := 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000006000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000001c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000007800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000002400000000f000000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000000000000000000000008000000004800000001e000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000300000000000000000080000000050000000009000000003c0000000a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000e000000000000000003000000001a00000000120000000078000000340000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006000000003c0000000100000000060000000034000000002400000000f0000000e8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000004000000000000000000c00000000f800000006000000000c0000000068000000004800000001e0000001d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000008000000000000000005800000001f00000000c000000001800000004d0000000009000000103c000000ba00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000001000000000a000000001000000000000000001b000000003e000000018000000023000000019a00000000120000002078000001740000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000c00000000200000000140000000020000000000000000076000000007c0000001300000000c60000000734000000202400000040f0000002e80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000006000000003800000000400000000a800000004400000000000000001ec00000000f800000026000000018c0000000e68000000c04800000081e0000025d0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000c0000000070000000048000000035000000018800000000000000007d800000001f00000004c0000000b180000001cd0000003809000000103c000004ba0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000001800000000e000000019000000006a00000007100000000000000000fb000000003e000000098000000163000000039a00000070120000042078000029740000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000020000000020000000013000000001c00000007200000000d40000001e200000000000000001f6000000207c0000011300000002c60000000734000002e02400001840f00000d2e8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000060000000020000000004000000004000000002600000002380000000e400000009a80000003c400000000000000013ec00000040f800000226000000258c0000010e6800000dc04800003081e00001a5d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000003000000001c00000000c0000000008000000028000000004c00000004700000001c8000000335000000078800000080000000067d800000081f00000044c0000004b180000021cd000001b809000016103c000034ba00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000006000000003800000003800000000100000000d0000000009800000028e000000039000000066a0000000f10000003000000000cfb000000903e000004898000000963000001439a000003701200002c2078000069740000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000004000000000c000000007000000007000000000200000001a0000000113000000051c0000000720000002cd40000001e2000000e0000000019f6000001207c0000091300000092c60000028734000006e02400015840f00008d2e80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000028000000008000000001800000004e00000000e00000001040000000b400000002260000002a380000000e4000000d9a80000003c4000003c0000000033ec00000a40f800001226000001258c0000050e6800008dc0480006b081e00031a5d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000400000000000000000100000000050000000050000000003000000019c00000009c0000000608000000168000000144c00000054700000001c8000001b35000000078800000780000000067d800003481f00001244c00000a4b1800000a1cd000011b8090001d6103c000634ba000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000018000000000000000006000000000a00000000a000000000600000003380000001380000000c100000002d00000002898000002a8e000001039000000366a0000040f1000002f000000000cfb000006903e000064898000034963000001439a0000a370120003ac2078002c697400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000003000000002000000001c0000000014000000014000000000c000000067000000027000000058200000005a0000000513000000551c0000020720000006cd40000081e200000de0000000419f600002d207c0001c91300000692c60000028734000146e02400175840f00058d2e80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008000000002000000000000000001600000000c0000000078000000002800000012800000000180000004ce00000024e0000000b040000008b40000004a26000002aa380000140e4000000d9a80000103c400001bc0000000833ec00005a40f80003922600000d258c0000050e6800028dc048002eb081e000b1a5d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000040000000010000000004000000000000000002c00000001800000000f00000000850000000250000000203000000099c00000049c0000001608000001168000000944c00000d54700000681c8000001b3500000207880000b780000005067d80002b481f00017244c00009a4b1800000a1cd000251b8090015d6103c001634ba00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000080000000020000000008000000000000000005800000003000000005e000000010a00000014a000000040600000053380000029380000002c1000000a2d0000001289800001aa8e00001d039000000366a0000040f1000016f0000000a0cfb000056903e0002e4898000334963000101439a000ca37012006bac2078022c69740000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000010000000024000000001000000008000000000b00000002600000000bc0000000a14000000694000000280c000000a67000000527000000458200000145a000000251300000b551c00003a0720000006cd40000081e20000ade0000001419f60000ad207c0015c9130000e692c60002028734001946e02400d75840f00458d2e800000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000001200000000c8000000042000000030000000011600000004c00000001780000003428000001d2800000050180000054ce000000a4e0000008b0400000a8b40000004a26000016aa380001740e4000000d9a80004103c400035bc0000002833ec00015a40f8002b92260003cd258c0014050e6800328dc04801aeb081e008b1a5d00000000000000000000000000000000000000000000000000000000000000000002000000001400000000000000000640000000190000000184000000060000000022c00000009800000002f00000006850000003a50000000a03000001a99c00000149c0000051608000015168000000944c00002d54700002e81c8000201b350001820788000eb780000005067d80002b481f00157244c000f9a4b1800280a1cd002651b8090035d6103c011634ba00000000000000000000000000000000000000000000000000000000010000000004000000006800000000000000000c80000000b200000007080000000c0000000045800000093000000005e0000002d0a00000074a0000001406000003533800002293800001a2c1000002a2d0000041289800025aa8e00015d039000040366a0003040f10001d6f0000000a0cfb000056903e002ae4898001f34963001501439a004ca37012006bac2078222c69740000000000000000000000000000000000000000000000008000000002000000000800000000d000000000000000005900000003640000000e1000000098000000008b00000032600000010bc000000da14000000e94000002280c000006a6700000c527000007458200000545a000008251300004b551c0002ba0720002806cd40006081e20003ade0000001419f60000ad207c0055c9130003e692c6006a028734029946e02410d75840f0c458d2e80000000000000000000000000000000000000040000000030000000004000000001000000001a00000002000000000b200000006c80000001c20000003300000000116000000e4c0000006178000001b428000001d28000004501800004d4ce000038a4e00000e8b0400008a8b40000104a26000096aa380015740e4000500d9a8004c103c400275bc0000102833ec00015a40f804ab92260007cd258c00d4050e6805328dc04821aeb081e188b1a5d00000000000
def col (x y z : Nat) : Bool := Fmask.testBit (x * 1369 + y * 37 + z)

def chkRed : Bool :=
  (List.range 37).all fun v0 => (List.range 37).all fun v1 => !(v0 < v1) || ((List.range 37).all fun v2 => !(v1 < v2 && col v0 v1 v2) || ((List.range 37).all fun v3 => !(v2 < v3 && col v0 v1 v3 && col v0 v2 v3 && col v1 v2 v3)))

def chkBlue : Bool :=
  (List.range 37).all fun v0 => (List.range 37).all fun v1 => !(v0 < v1) || ((List.range 37).all fun v2 => !(v1 < v2 && !(col v0 v1 v2)) || ((List.range 37).all fun v3 => !(v2 < v3 && !(col v0 v1 v3) && !(col v0 v2 v3) && !(col v1 v2 v3)) || ((List.range 37).all fun v4 => !(v3 < v4 && !(col v0 v1 v4) && !(col v0 v2 v4) && !(col v0 v3 v4) && !(col v1 v2 v4) && !(col v1 v3 v4) && !(col v2 v3 v4)))))

theorem chkRed_ok : chkRed = true := by decide +kernel
theorem chkBlue_ok : chkBlue = true := by decide +kernel

/-- `col` (a colouring of the triples `x<y<z` of `{0,…,N-1}`) contains a `K_4^(3)` of colour `χ`. -/
def HasMonoK4 (N : Nat) (col : Nat → Nat → Nat → Bool) (χ : Bool) : Prop :=
  ∃ a b c d : Nat, a < b ∧ b < c ∧ c < d ∧ d < N ∧ col a b c = χ ∧ col a b d = χ ∧ col a c d = χ ∧ col b c d = χ
/-- `col` (a colouring of the triples `x<y<z` of `{0,…,N-1}`) contains a `K_5^(3)` of colour `χ`. -/
def HasMonoK5 (N : Nat) (col : Nat → Nat → Nat → Bool) (χ : Bool) : Prop :=
  ∃ a b c d e : Nat, a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < N ∧ col a b c = χ ∧ col a b d = χ ∧ col a b e = χ ∧ col a c d = χ ∧ col a c e = χ ∧ col a d e = χ ∧ col b c d = χ ∧ col b c e = χ ∧ col b d e = χ ∧ col c d e = χ

theorem noRedK : ¬ HasMonoK4 37 col true := by
  rintro ⟨a, b, c, d, l0, l1, l2, hn, h0, h1, h2, h3⟩
  have hc := chkRed_ok
  unfold chkRed at hc
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at hc
  rcases hc a (by omega) b (by omega) with h | h
  · omega
  rcases h c (by omega) with h | h
  · simp_all
  rcases h d (by omega) with h | h
  all_goals simp_all

theorem noBlueK : ¬ HasMonoK5 37 col false := by
  rintro ⟨a, b, c, d, e, l0, l1, l2, l3, hn, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  have hc := chkBlue_ok
  unfold chkBlue at hc
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at hc
  rcases hc a (by omega) b (by omega) with h | h
  · omega
  rcases h c (by omega) with h | h
  · simp_all
  rcases h d (by omega) with h | h
  · simp_all
  rcases h e (by omega) with h | h
  all_goals simp_all

/-- **R(4,5;3) ≥ 38** -/
theorem main : ∃ col : Nat → Nat → Nat → Bool, ¬ HasMonoK4 37 col true ∧ ¬ HasMonoK5 37 col false :=
  ⟨col, noRedK, noBlueK⟩

end R453f

#print axioms R453f.main


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

#print axioms R553.main


namespace R463

/-- `Fmask` encodes the colour of the triples `{0, d₁, d₂}` (0 < d₁ < d₂ < 67): bit `d₁*67+d₂` (1 = red). -/
def Fmask : Nat := 0x2000000000000000000000000000000000600000000000000000000000000000000080000000000000006a0000000000000005800000000000000006000000000000002a8000000000000004c60000000000000024000000000000000352000000000000013940000000000000000200000000000000d9200000000000001032000000000000162000000000000002ab08000000000000ac4c60000000000006316a00000000000360d8c000000000001044400000000000002b840000000000018428880000000000106650800000000001a0083400000000001307410000000000090000c60000000001028a20a0000000004293d05800000000041a796000000000007e889028000000003050a0c22000000001c150046c000000000800c0fb00000000056c0850ae000000023a0d9b310000000054986198240000000709e303444000000000a65bc980000000111e627814000000008217180d3e00000034a71e0871400000054824cb200000000002406ac0ac200000600808b4890c00000a0102d4ec80200000ce84f104419800000103a9302c2bc00005439826c180040000860bb2d87823000010a49c0882525000004da010a02b9600006c2e001e39122400001283952816920001218006474534420014a5a2828a0063a00409429e50046960006600c846044a298010a981142286c0e600b6ea045f0411024019436185098036100a280d10558cd00b809823266a0a14128421300a4123019d54a00000000000000000

/-- The colouring of the triple `x < y < z` of `{0,…,66}`: the colour of `{0, y-x, z-x}`
(true = red). It is translation invariant by construction. -/
def col (x y z : Nat) : Bool := Fmask.testBit ((y - x) * 67 + (z - x))

/-- pruned search: no red `K_4^(3)` containing the vertex 0 -/
def chkRed : Bool :=
  (List.range 67).all fun v1 => v1 == 0 || ((List.range 67).all fun v2 => !(v1 < v2 && col 0 v1 v2) || ((List.range 67).all fun v3 => !(v2 < v3 && col 0 v1 v3 && col 0 v2 v3 && col v1 v2 v3)))

/-- pruned search: no blue `K_6^(3)` containing the vertex 0 -/
def chkBlue : Bool :=
  (List.range 67).all fun v1 => v1 == 0 || ((List.range 67).all fun v2 => !(v1 < v2 && !(col 0 v1 v2)) || ((List.range 67).all fun v3 => !(v2 < v3 && !(col 0 v1 v3) && !(col 0 v2 v3) && !(col v1 v2 v3)) || ((List.range 67).all fun v4 => !(v3 < v4 && !(col 0 v1 v4) && !(col 0 v2 v4) && !(col 0 v3 v4) && !(col v1 v2 v4) && !(col v1 v3 v4) && !(col v2 v3 v4)) || ((List.range 67).all fun v5 => !(v4 < v5 && !(col 0 v1 v5) && !(col 0 v2 v5) && !(col 0 v3 v5) && !(col 0 v4 v5) && !(col v1 v2 v5) && !(col v1 v3 v5) && !(col v1 v4 v5) && !(col v2 v3 v5) && !(col v2 v4 v5) && !(col v3 v4 v5))))))

theorem chkRed_ok : chkRed = true := by decide +kernel
theorem chkBlue_ok : chkBlue = true := by decide +kernel

end R463

namespace R463

theorem noRed0 (x1 x2 x3 : Nat) (h1 : 0 < x1) (h2 : x1 < x2) (h3 : x2 < x3) (hn : x3 < 67)
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

theorem noBlue0 (x1 x2 x3 x4 x5 : Nat) (h1 : 0 < x1) (h2 : x1 < x2) (h3 : x2 < x3) (h4 : x3 < x4) (h5 : x4 < x5) (hn : x5 < 67)
    (r0 : col 0 x1 x2 = false) (r1 : col 0 x1 x3 = false) (r2 : col 0 x1 x4 = false) (r3 : col 0 x1 x5 = false) (r4 : col 0 x2 x3 = false) (r5 : col 0 x2 x4 = false) (r6 : col 0 x2 x5 = false) (r7 : col 0 x3 x4 = false) (r8 : col 0 x3 x5 = false) (r9 : col 0 x4 x5 = false) (r10 : col x1 x2 x3 = false) (r11 : col x1 x2 x4 = false) (r12 : col x1 x2 x5 = false) (r13 : col x1 x3 x4 = false) (r14 : col x1 x3 x5 = false) (r15 : col x1 x4 x5 = false) (r16 : col x2 x3 x4 = false) (r17 : col x2 x3 x5 = false) (r18 : col x2 x4 x5 = false) (r19 : col x3 x4 x5 = false) : False := by
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
  · simp_all
  rcases h x5 (by omega) with h | h
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

/-- `col` (a colouring of the triples `x<y<z` of `{0,…,N-1}`) contains a `K_6^(3)` of colour `χ`:
6 vertices all of whose triples have colour `χ`. -/
def HasMonoK6 (N : Nat) (col : Nat → Nat → Nat → Bool) (χ : Bool) : Prop :=
  ∃ a b c d e f : Nat, a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < f ∧ f < N ∧ col a b c = χ ∧ col a b d = χ ∧ col a b e = χ ∧ col a b f = χ ∧ col a c d = χ ∧ col a c e = χ ∧ col a c f = χ ∧ col a d e = χ ∧ col a d f = χ ∧ col a e f = χ ∧ col b c d = χ ∧ col b c e = χ ∧ col b c f = χ ∧ col b d e = χ ∧ col b d f = χ ∧ col b e f = χ ∧ col c d e = χ ∧ col c d f = χ ∧ col c e f = χ ∧ col d e f = χ

theorem noRedK : ¬ HasMonoK4 67 col true := by
  rintro ⟨a, b, c, d, l0, l1, l2, hn, h0, h1, h2, h3⟩
  have s0 := col_shift a a b c (by omega) (by omega) (by omega)
  have s1 := col_shift a a b d (by omega) (by omega) (by omega)
  have s2 := col_shift a a c d (by omega) (by omega) (by omega)
  have s3 := col_shift a b c d (by omega) (by omega) (by omega)
  simp only [Nat.sub_self] at s0 s1 s2 s3
  exact noRed0 (b - a) (c - a) (d - a) (by omega) (by omega) (by omega) (by omega) (by rw [s0, h0]) (by rw [s1, h1]) (by rw [s2, h2]) (by rw [s3, h3])

theorem noBlueK : ¬ HasMonoK6 67 col false := by
  rintro ⟨a, b, c, d, e, f, l0, l1, l2, l3, l4, hn, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩
  have s0 := col_shift a a b c (by omega) (by omega) (by omega)
  have s1 := col_shift a a b d (by omega) (by omega) (by omega)
  have s2 := col_shift a a b e (by omega) (by omega) (by omega)
  have s3 := col_shift a a b f (by omega) (by omega) (by omega)
  have s4 := col_shift a a c d (by omega) (by omega) (by omega)
  have s5 := col_shift a a c e (by omega) (by omega) (by omega)
  have s6 := col_shift a a c f (by omega) (by omega) (by omega)
  have s7 := col_shift a a d e (by omega) (by omega) (by omega)
  have s8 := col_shift a a d f (by omega) (by omega) (by omega)
  have s9 := col_shift a a e f (by omega) (by omega) (by omega)
  have s10 := col_shift a b c d (by omega) (by omega) (by omega)
  have s11 := col_shift a b c e (by omega) (by omega) (by omega)
  have s12 := col_shift a b c f (by omega) (by omega) (by omega)
  have s13 := col_shift a b d e (by omega) (by omega) (by omega)
  have s14 := col_shift a b d f (by omega) (by omega) (by omega)
  have s15 := col_shift a b e f (by omega) (by omega) (by omega)
  have s16 := col_shift a c d e (by omega) (by omega) (by omega)
  have s17 := col_shift a c d f (by omega) (by omega) (by omega)
  have s18 := col_shift a c e f (by omega) (by omega) (by omega)
  have s19 := col_shift a d e f (by omega) (by omega) (by omega)
  simp only [Nat.sub_self] at s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19
  exact noBlue0 (b - a) (c - a) (d - a) (e - a) (f - a) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [s0, h0]) (by rw [s1, h1]) (by rw [s2, h2]) (by rw [s3, h3]) (by rw [s4, h4]) (by rw [s5, h5]) (by rw [s6, h6]) (by rw [s7, h7]) (by rw [s8, h8]) (by rw [s9, h9]) (by rw [s10, h10]) (by rw [s11, h11]) (by rw [s12, h12]) (by rw [s13, h13]) (by rw [s14, h14]) (by rw [s15, h15]) (by rw [s16, h16]) (by rw [s17, h17]) (by rw [s18, h18]) (by rw [s19, h19])

/-- **R(4,6;3) ≥ 68**: there is a red/blue colouring of the triples of `{0,…,66}` with no red
`K_4^(3)` and no blue `K_6^(3)`. -/
theorem main : ∃ col : Nat → Nat → Nat → Bool, ¬ HasMonoK4 67 col true ∧ ¬ HasMonoK6 67 col false :=
  ⟨col, noRedK, noBlueK⟩

end R463

#print axioms R463.main


namespace R554

/-- `row d₁` encodes the colours of the 4-sets `{0, d₁, d₂, d₃}` (0 < d₁ < d₂ < d₃ < 37): bit `d₂*37+d₃`
(a binary decision tree on `d₁`, for fast kernel evaluation). -/
def row (d : Nat) : Nat := if d < 18 then (if d < 9 then (if d < 4 then (if d < 2 then (if d < 1 then (0x0) else (0x80000000020000000000000000018000000000800000007600000003f000000011c0000000d800000001e80000002d8800000127800000070e0000003314000002e8f8000006ae000000745c800002f51e000007d2a00001623f2000079ba5000032e7ac00034e59c000194897a000562966000774e430002707c8a00189e33640083c9e9b8014d2c87e02855fdf400b11cfb30022fccc5a84bd909bd20000000000000000000)) else (if d < 3 then (0x3000000000c000000001800000001a00000002a80000000780000000f200000007880000002830000001f4c000000f4780000049ca000001ffc000000ada800000c2f48000060ec000001c72000000f161a00008753080006416fc00013cd2b00004897dc0006b87f2000735598800076a3d280176d0d0a00beb42468007033eec033718bfd00c36fdb0c0ad199fa200000000000000000000000000000) else (0x6000000001000000001000000000b8000000036000000011000000001e0000000e900000003ce00000016180000004c4000000829800000533000000389b000000b92a00000134e800004d7780000255df00001ef46a0000b9e490000608f360001925d980019ab524000e9bd038003505bc40016332a3801af250f600ec1f8610019ac3598017fa31d980337ce23400000000000000000000000000000000000000))) else (if d < 6 then (if d < 5 then (0x80000000000000000028000000006000000002800000002400000001e00000001f000000001c80000004d200000000d80000011d20000000730000005a62000003999800001e86800000ad528000051ace00003dc30000019a8e600005da1a800063ab66000338814800154fc50000f5ccbc0006d7df9000156c85f8013c528f200430fc1b80377cc0e0005f7f542800000000000000000000000000000000000000000000000) else (0x2000000002800000000c00000000d800000003200000001680000001d20000000b880000003100000002f28000000b0e0000004af8000005b3800000143e800001038a00000a622000000b28a0000092a7800018bebe0000032be00000659aa00016d88080005e9992000b2bc908005dc03ba003f426d5001bc293d600b1216be807e134b28000000000000000000000000000000000000000000000000000000000)) else (if d < 7 then (0x8000000002000000000000000000e000000005800000003200000002e80000001b40000000c200000004b40000001b58000000e1a0000009c50000002a74000000ea68000017898000008a77000004ca5600003d92480000a77bc0000bf43500002b68100000c7a8780011b4b62000849ea680009fbeb60038a998d00142c2dba00ecbc9e08000000000000000000000000000000000000000000000000000000000000000000) else (if d < 8 then (0x80000000040000000000000000006000000007000000006800000001e00000000080000000ff00000006560000002690000001b0400000016980000026e600000097c8000012d7600000bbcd0000037864000010b5980001eabe40000e9b6100001d3cb80003c2bc600012665e80001e99d780023da0ac002978adc0009b31e460000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x8000000002000000001800000001e00000000a000000004c00000001980000000b400000000f00000003860000000bb8000001988000000b0e8000007f88000002ff0800001e3880000057428000019dde00002276b0000087f840000436cb80000816d400020236d000028fcaa000e05ecb800119aace000a27c1c80000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))) else (if d < 13 then (if d < 11 then (if d < 10 then (0x8000000004000000003800000000e000000009000000006200000002880000000ee0000000de00000003f400000001100000014ea0000008c78000005922000001b79800000962800000e19f000002168400001adc8800009f55e00005617e8000559a60000250239800092b56600027f0eb0000c272ee00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x4000000000000000001e00000000300000000400000000310000000044000000014800000008e0000003e7000000018e00000096380000032860000006db000001cfce000007cc3800007bb980000335a100000f7b9400003ea60000066d5c60003374930000efa448000334a35000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if d < 12 then (0x80000000040000000018000000004000000009800000002600000003500000000ac000000057000000054400000005c8000000bc00000004be0000005dba000001b6c00000051a400000a17500000261ec00002493780001f5f460000ac2dd00006cf1060001a967900017a44a6000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x80000000060000000018000000012000000003000000003200000002a8000000122000000097000000017c0000000cf0000001c0e0000003e9000000614c0000033db000000471e0000059ee800006a53200003ca92000019c5660000493ce80003f68260000734e58000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))) else (if d < 15 then (if d < 14 then (0x60000000028000000006000000003000000005a00000001480000001d20000000f080000005fa0000001e600000000f4000000e34800000449a0000021fe800001bad200000772880000514d00000018778000158bde000086570800035e74c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x4000000003800000001a00000000c800000003a000000002000000014a00000008780000003e80000002740000001c60000000f1880000011fe0000027d2000000647a000002232800007358a00001f7548000161a3c000052ecf00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if d < 16 then (0x8000000000000000003800000001a0000000048000000018000000008000000012e000000074800000022a0000001cf80000015ca000000b868000006764000002cae000001470200000a55a800001eeb20000009c7000013f11a00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if d < 17 then (0x20000000010000000012000000009000000005c000000025000000011200000007500000007100000001100000000466000000cb40000002e54000002f85000000585e00000b964000000370600000a97c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x60000000010000000016000000009800000005a00000002a80000000d400000009400000002fc0000003ba000000083600000051c8000001cda00000333380000152740000097a18000078af4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))))) else (if d < 27 then (if d < 22 then (if d < 20 then (if d < 19 then (0x40000000038000000016000000006000000004c000000015800000008800000003d800000061c00000012c800000161c000000fa9000000465a000001b2380000056d4000009d170000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x38000000018000000006000000006400000001180000001dc00000007800000006a600000035b0000001c340000006700000000cca0000007ff0000001d580000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if d < 21 then (0x8000000002000000002800000001200000000c800000000200000002280000000b400000007f80000002d200000029e80000012e2000000ca08000005392000003e2e80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x6000000003000000000800000000600000000460000000330000000040000000021800000008c00000036000000008c8000000f1780000028cc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))) else (if d < 24 then (if d < 23 then (0x6000000003000000001e000000004800000003200000000f00000000b600000008e80000004b200000030d0000000cbe000000387000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x8000000002000000000000000001c000000002800000001600000002e800000012e00000009c000000073c0000001828000000792000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if d < 25 then (0x8000000002000000003800000001e000000007000000004c00000002d000000003e00000004b800000011e0000002368000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if d < 26 then (0x2000000003000000001800000000d000000004c00000000f00000001e000000002780000001780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x8000000004000000000000000001c00000000d8000000024000000011000000007800000000d80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))) else (if d < 32 then (if d < 29 then (if d < 28 then (0x8000000002000000000000000000c00000000a000000006c00000002a80000000e200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x8000000004000000002800000001800000000e800000005800000001f800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if d < 30 then (0x8000000004000000002800000000200000000c000000006e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if d < 31 then (0x1000000000c0000000080000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x800000000600000000180000000060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))) else (if d < 34 then (if d < 33 then (0x0) else (0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if d < 35 then (0x800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if d < 36 then (0x0) else (0x0))))))

/-- The colouring of the 4-set `x < y < z < w` of `{0,…,36}`: the colour of `{0, y-x, z-x, w-x}`
(true = red); translation invariant by construction. -/
def col (x y z w : Nat) : Bool := (row (y - x)).testBit ((z - x) * 37 + (w - x))

def chkRed (v1 : Nat) : Bool :=
  (List.range 37).all fun v2 => !(v1 < v2) || ((List.range 37).all fun v3 => !(v2 < v3 && col 0 v1 v2 v3) || ((List.range 37).all fun v4 => !(v3 < v4 && col 0 v1 v2 v4 && col 0 v1 v3 v4 && col 0 v2 v3 v4 && col v1 v2 v3 v4)))

def chkBlue (v1 : Nat) : Bool :=
  (List.range 37).all fun v2 => !(v1 < v2) || ((List.range 37).all fun v3 => !(v2 < v3 && !(col 0 v1 v2 v3)) || ((List.range 37).all fun v4 => !(v3 < v4 && !(col 0 v1 v2 v4) && !(col 0 v1 v3 v4) && !(col 0 v2 v3 v4) && !(col v1 v2 v3 v4))))

theorem cr1 : chkRed 1 = true := by decide +kernel
theorem cr2 : chkRed 2 = true := by decide +kernel
theorem cr3 : chkRed 3 = true := by decide +kernel
theorem cr4 : chkRed 4 = true := by decide +kernel
theorem cr5 : chkRed 5 = true := by decide +kernel
theorem cr6 : chkRed 6 = true := by decide +kernel
theorem cr7 : chkRed 7 = true := by decide +kernel
theorem cr8 : chkRed 8 = true := by decide +kernel
theorem cr9 : chkRed 9 = true := by decide +kernel
theorem cr10 : chkRed 10 = true := by decide +kernel
theorem cr11 : chkRed 11 = true := by decide +kernel
theorem cr12 : chkRed 12 = true := by decide +kernel
theorem cr13 : chkRed 13 = true := by decide +kernel
theorem cr14 : chkRed 14 = true := by decide +kernel
theorem cr15 : chkRed 15 = true := by decide +kernel
theorem cr16 : chkRed 16 = true := by decide +kernel
theorem cr17 : chkRed 17 = true := by decide +kernel
theorem cr18 : chkRed 18 = true := by decide +kernel
theorem cr19 : chkRed 19 = true := by decide +kernel
theorem cr20 : chkRed 20 = true := by decide +kernel
theorem cr21 : chkRed 21 = true := by decide +kernel
theorem cr22 : chkRed 22 = true := by decide +kernel
theorem cr23 : chkRed 23 = true := by decide +kernel
theorem cr24 : chkRed 24 = true := by decide +kernel
theorem cr25 : chkRed 25 = true := by decide +kernel
theorem cr26 : chkRed 26 = true := by decide +kernel
theorem cr27 : chkRed 27 = true := by decide +kernel
theorem cr28 : chkRed 28 = true := by decide +kernel
theorem cr29 : chkRed 29 = true := by decide +kernel
theorem cr30 : chkRed 30 = true := by decide +kernel
theorem cr31 : chkRed 31 = true := by decide +kernel
theorem cr32 : chkRed 32 = true := by decide +kernel
theorem cr33 : chkRed 33 = true := by decide +kernel
theorem cr34 : chkRed 34 = true := by decide +kernel
theorem cr35 : chkRed 35 = true := by decide +kernel
theorem cr36 : chkRed 36 = true := by decide +kernel
theorem chkRed_all (v : Nat) (h0 : 0 < v) (hv : v < 37) : chkRed v = true :=
  match v, h0, hv with
  | 0, h, _ => absurd h (Nat.lt_irrefl 0)
  | 1, _, _ => cr1
  | 2, _, _ => cr2
  | 3, _, _ => cr3
  | 4, _, _ => cr4
  | 5, _, _ => cr5
  | 6, _, _ => cr6
  | 7, _, _ => cr7
  | 8, _, _ => cr8
  | 9, _, _ => cr9
  | 10, _, _ => cr10
  | 11, _, _ => cr11
  | 12, _, _ => cr12
  | 13, _, _ => cr13
  | 14, _, _ => cr14
  | 15, _, _ => cr15
  | 16, _, _ => cr16
  | 17, _, _ => cr17
  | 18, _, _ => cr18
  | 19, _, _ => cr19
  | 20, _, _ => cr20
  | 21, _, _ => cr21
  | 22, _, _ => cr22
  | 23, _, _ => cr23
  | 24, _, _ => cr24
  | 25, _, _ => cr25
  | 26, _, _ => cr26
  | 27, _, _ => cr27
  | 28, _, _ => cr28
  | 29, _, _ => cr29
  | 30, _, _ => cr30
  | 31, _, _ => cr31
  | 32, _, _ => cr32
  | 33, _, _ => cr33
  | 34, _, _ => cr34
  | 35, _, _ => cr35
  | 36, _, _ => cr36
  | v + 37, _, h => absurd h (by omega)

theorem cb1 : chkBlue 1 = true := by decide +kernel
theorem cb2 : chkBlue 2 = true := by decide +kernel
theorem cb3 : chkBlue 3 = true := by decide +kernel
theorem cb4 : chkBlue 4 = true := by decide +kernel
theorem cb5 : chkBlue 5 = true := by decide +kernel
theorem cb6 : chkBlue 6 = true := by decide +kernel
theorem cb7 : chkBlue 7 = true := by decide +kernel
theorem cb8 : chkBlue 8 = true := by decide +kernel
theorem cb9 : chkBlue 9 = true := by decide +kernel
theorem cb10 : chkBlue 10 = true := by decide +kernel
theorem cb11 : chkBlue 11 = true := by decide +kernel
theorem cb12 : chkBlue 12 = true := by decide +kernel
theorem cb13 : chkBlue 13 = true := by decide +kernel
theorem cb14 : chkBlue 14 = true := by decide +kernel
theorem cb15 : chkBlue 15 = true := by decide +kernel
theorem cb16 : chkBlue 16 = true := by decide +kernel
theorem cb17 : chkBlue 17 = true := by decide +kernel
theorem cb18 : chkBlue 18 = true := by decide +kernel
theorem cb19 : chkBlue 19 = true := by decide +kernel
theorem cb20 : chkBlue 20 = true := by decide +kernel
theorem cb21 : chkBlue 21 = true := by decide +kernel
theorem cb22 : chkBlue 22 = true := by decide +kernel
theorem cb23 : chkBlue 23 = true := by decide +kernel
theorem cb24 : chkBlue 24 = true := by decide +kernel
theorem cb25 : chkBlue 25 = true := by decide +kernel
theorem cb26 : chkBlue 26 = true := by decide +kernel
theorem cb27 : chkBlue 27 = true := by decide +kernel
theorem cb28 : chkBlue 28 = true := by decide +kernel
theorem cb29 : chkBlue 29 = true := by decide +kernel
theorem cb30 : chkBlue 30 = true := by decide +kernel
theorem cb31 : chkBlue 31 = true := by decide +kernel
theorem cb32 : chkBlue 32 = true := by decide +kernel
theorem cb33 : chkBlue 33 = true := by decide +kernel
theorem cb34 : chkBlue 34 = true := by decide +kernel
theorem cb35 : chkBlue 35 = true := by decide +kernel
theorem cb36 : chkBlue 36 = true := by decide +kernel
theorem chkBlue_all (v : Nat) (h0 : 0 < v) (hv : v < 37) : chkBlue v = true :=
  match v, h0, hv with
  | 0, h, _ => absurd h (Nat.lt_irrefl 0)
  | 1, _, _ => cb1
  | 2, _, _ => cb2
  | 3, _, _ => cb3
  | 4, _, _ => cb4
  | 5, _, _ => cb5
  | 6, _, _ => cb6
  | 7, _, _ => cb7
  | 8, _, _ => cb8
  | 9, _, _ => cb9
  | 10, _, _ => cb10
  | 11, _, _ => cb11
  | 12, _, _ => cb12
  | 13, _, _ => cb13
  | 14, _, _ => cb14
  | 15, _, _ => cb15
  | 16, _, _ => cb16
  | 17, _, _ => cb17
  | 18, _, _ => cb18
  | 19, _, _ => cb19
  | 20, _, _ => cb20
  | 21, _, _ => cb21
  | 22, _, _ => cb22
  | 23, _, _ => cb23
  | 24, _, _ => cb24
  | 25, _, _ => cb25
  | 26, _, _ => cb26
  | 27, _, _ => cb27
  | 28, _, _ => cb28
  | 29, _, _ => cb29
  | 30, _, _ => cb30
  | 31, _, _ => cb31
  | 32, _, _ => cb32
  | 33, _, _ => cb33
  | 34, _, _ => cb34
  | 35, _, _ => cb35
  | 36, _, _ => cb36
  | v + 37, _, h => absurd h (by omega)


theorem noRed0 (x1 x2 x3 x4 : Nat) (h1 : 0 < x1) (h2 : x1 < x2) (h3 : x2 < x3) (h4 : x3 < x4) (hn : x4 < 37)
    (r0 : col 0 x1 x2 x3 = true) (r1 : col 0 x1 x2 x4 = true) (r2 : col 0 x1 x3 x4 = true) (r3 : col 0 x2 x3 x4 = true) (r4 : col x1 x2 x3 x4 = true) : False := by
  have h := chkRed_all x1 (by omega) (by omega)
  unfold chkRed at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
  rcases h x2 (by omega) with h | h
  · omega
  rcases h x3 (by omega) with h | h
  · simp_all
  rcases h x4 (by omega) with h | h
  all_goals simp_all

theorem noBlue0 (x1 x2 x3 x4 : Nat) (h1 : 0 < x1) (h2 : x1 < x2) (h3 : x2 < x3) (h4 : x3 < x4) (hn : x4 < 37)
    (r0 : col 0 x1 x2 x3 = false) (r1 : col 0 x1 x2 x4 = false) (r2 : col 0 x1 x3 x4 = false) (r3 : col 0 x2 x3 x4 = false) (r4 : col x1 x2 x3 x4 = false) : False := by
  have h := chkBlue_all x1 (by omega) (by omega)
  unfold chkBlue at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
  rcases h x2 (by omega) with h | h
  · omega
  rcases h x3 (by omega) with h | h
  · simp_all
  rcases h x4 (by omega) with h | h
  all_goals simp_all

/-- translation: the colour of `x<y<z<w` only depends on the differences to `x` -/
theorem col_shift (a x y z w : Nat) (hx : a ≤ x) (hxy : x < y) (hyz : y < z) (hzw : z < w) :
    col (x - a) (y - a) (z - a) (w - a) = col x y z w := by
  unfold col
  rw [show y - a - (x - a) = y - x by omega, show z - a - (x - a) = z - x by omega,
    show w - a - (x - a) = w - x by omega]

/-- `col` (a colouring of the 4-sets `x<y<z<w` of `{0,…,N-1}`) contains a `K_5^(4)` of colour `χ`. -/
def HasMonoK5 (N : Nat) (col : Nat → Nat → Nat → Nat → Bool) (χ : Bool) : Prop :=
  ∃ a b c d e : Nat, a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < N ∧ col a b c d = χ ∧ col a b c e = χ ∧ col a b d e = χ ∧ col a c d e = χ ∧ col b c d e = χ

theorem noRedK : ¬ HasMonoK5 37 col true := by
  rintro ⟨a, b, c, d, e, l0, l1, l2, l3, hn, h0, h1, h2, h3, h4⟩
  have s0 := col_shift a a b c d (by omega) (by omega) (by omega) (by omega)
  have s1 := col_shift a a b c e (by omega) (by omega) (by omega) (by omega)
  have s2 := col_shift a a b d e (by omega) (by omega) (by omega) (by omega)
  have s3 := col_shift a a c d e (by omega) (by omega) (by omega) (by omega)
  have s4 := col_shift a b c d e (by omega) (by omega) (by omega) (by omega)
  simp only [Nat.sub_self] at s0 s1 s2 s3 s4
  exact noRed0 (b - a) (c - a) (d - a) (e - a) (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [s0, h0]) (by rw [s1, h1]) (by rw [s2, h2]) (by rw [s3, h3]) (by rw [s4, h4])

theorem noBlueK : ¬ HasMonoK5 37 col false := by
  rintro ⟨a, b, c, d, e, l0, l1, l2, l3, hn, h0, h1, h2, h3, h4⟩
  have s0 := col_shift a a b c d (by omega) (by omega) (by omega) (by omega)
  have s1 := col_shift a a b c e (by omega) (by omega) (by omega) (by omega)
  have s2 := col_shift a a b d e (by omega) (by omega) (by omega) (by omega)
  have s3 := col_shift a a c d e (by omega) (by omega) (by omega) (by omega)
  have s4 := col_shift a b c d e (by omega) (by omega) (by omega) (by omega)
  simp only [Nat.sub_self] at s0 s1 s2 s3 s4
  exact noBlue0 (b - a) (c - a) (d - a) (e - a) (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [s0, h0]) (by rw [s1, h1]) (by rw [s2, h2]) (by rw [s3, h3]) (by rw [s4, h4])

/-- **R(5,5;4) ≥ 38**: a red/blue colouring of the 4-subsets of `{0,…,36}` with no red
`K_5^(4)` and no blue `K_5^(4)`. -/
theorem main : ∃ col : Nat → Nat → Nat → Nat → Bool, ¬ HasMonoK5 37 col true ∧ ¬ HasMonoK5 37 col false :=
  ⟨col, noRedK, noBlueK⟩

end R554

#print axioms R554.main


namespace R564

/-- `row d₁` encodes the colours of the 4-sets `{0, d₁, d₂, d₃}` (0 < d₁ < d₂ < d₃ < 79): bit `d₂*79+d₃`
(a binary decision tree on `d₁`, for fast kernel evaluation). -/
def row (d : Nat) : Nat := if d < 39 then (if d < 19 then (if d < 9 then (if d < 4 then (if d < 2 then (if d < 1 then (0x0) else (0x2000000000000000000000000000000000000000c0000000000000000000200000000000000000010000000000000000000300000000000000000006a0000000000000000015a000000000000000000da00000000000000000628000000000000000004f4000000000000000009140000000000000000188a0000000000000000014a0000000000000000012200000000000000006c2e0000000000000000d0820000000000000004584e0000000000000004241000000000000000117df600000000000000088502000000000000001a66ae000000000000000c29520000000000000042402e00000000000002041a14000000000000020b754800000000000005dc1f420000000000001dd4504200000000000004e52a4e0000000000001d0703520000000000003241c3480000000000018d103040000000000000b8c107a8000000000007612e42020000000000064e08341000000000000a40d4887000000000003b2231300000000000000c62c0c1de00000000008c4009600a0000000000035d642994000000000041ad183b940000000002c3579633cc000000000234848367d60000000004c0377722b0000000001b4e8d471e5c0000000003018a865068000000001aa0de54184e00000001ea3a997e00ce00000000a7daa15da10e00000004c7c1a6400c8a0000000d14465c2d621800000006ac6c6506bd6800000018e9cb405804820000003919290e6e0746000000112125925c0a7e0000007b0f965abab31e00000018fbc84f0a92060000024240a3419d220800000101c430acc1d2fa00000eb7766119092786000001a00a64201065ca00004e425c086ea9321a00001194bf1ab9960e6e000102f0280ba41503520000a01c41b514bc837c0005049bc2fd040940a40008657a48f0559a345800054da89ca1940009d2002c245cac880291a12200514b32ca40a260b1560030b22754b1c2c07880011416a56366865820c000787573b60920513812073d3196404a11804600095f024404487390544814280a1229402c00adae0000000000000000000000000000000000000000)) else (if d < 3 then (0x200000000000000000000000000000000000000040000000000000000001000000000000000000000000000000000000000580000000000000000005a0000000000000000011c0000000000000000020c0000000000000000052000000000000000000902000000000000000013da000000000000000005280000000000000000144a000000000000000034cc000000000000000012dc000000000000000191460000000000000002f8dc0000000000000008f9440000000000000001887e000000000000001e86620000000000000070e06e00000000000000105d3a00000000000000a6036000000000000000eb219800000000000005799ce0000000000000034042cc0000000000000290e8860000000000000a83924e0000000000000a9712960000000000000823242c00000000000002461d560000000000009cd224540000000000046f8f01fe000000000000f90a4a260000000000044384aa9e0000000000189b42ba76000000000059240c20400000000000322e92030a0000000000035106f56400000000030397f175940000000000e98e3f6a3c0000000000c0ea3988240000000001029c1150cc000000000bcc341cce7c0000000064e9250c23e400000000807a04e9b1ac00000001431682749efe0000000018849a020474000000020119aa0519840000000c2018a944211000000010cd5042a5355200000024284d1d199042000000320061928ae41800000031f9f803dd1a860000019169662f9831c000000171f998998a922e0000013220a288c1d3a4000002b8fe91264412fe000008a4492166a18ca4000003f10a35222531a600006606348a4f09b19c00000524380978053ae000015a04da081d6a62200001e059030827aa980a0006423413688c22780a0002edc0d8ab8a37c44000012e803b232f4a8b2c0017b6830e549024822c006e0ba34a02923c20000016b8d4a2e207b001a000c237af41083130106002ce32205b92ca40950802200cd0008846594cd605cf040e2f09258a0008000000000000000000000000000000000000000000000000000000000000) else (0x200000000000000000006000000000000000000080000000000000000000c000000000000000000180000000000000000004800000000000000000088000000000000000001c40000000000000000031c0000000000000000037a00000000000000000a040000000000000000016e000000000000000007780000000000000000631a0000000000000000f2be00000000000000002ac20000000000000000ed10000000000000000264460000000000000009239200000000000000132814000000000000000ccc8a0000000000000020064200000000000000ae153c00000000000000105068000000000000020c069a0000000000000502006a0000000000000131f31a000000000000017ed9c200000000000030580cae0000000000000447646e000000000000460570e2000000000000c05658260000000000002f60229c0000000000028456d2600000000000064a79052600000000000a63544d2800000000002c04802458000000000000e2ac924600000000004d50c98682000000000108802d58380000000000d9368a15cc0000000006e54623ca5000000000028e0a2e3644000000000903a5550e1a000000001b82409b09c00000000009116960033600000000b538212c9048000000009d509207199e00000000203b1f63118000000002958b85d0db8c0000000ad88a2110360a000000178010c922650c0000001488b58036660a000000007f9d53208a8c000000001f48098e59a6000000108390825c9ec80000005e52521086bfa4000001d890a5a4b0b010000000311ece75d600b600000b07540c07b11b10000022d000d3b3140386000009940bcd39494e3c0000473045c8045c242e00003279d5dba601240e00037110e0500acc725c00055e06fd068437d1300004394908e9060aeeaa000060b2a0c03e61e07e0000606010126c9cf0460014b1ffc8c026c82cee00105e23124069fe226c00cb1452094551820228004468ce89e090661a1800f131a2dd0733a21bca00000000000000000000000000000000000000000000000000000000000000000000000000000000))) else (if d < 6 then (if d < 5 then (0x40000000000000000001a000000000000000000200000000000000000005000000000000000000092000000000000000000100000000000000000010a0000000000000000005200000000000000000028000000000000000015da0000000000000000314200000000000000007c300000000000000000334e0000000000000001c4500000000000000001a1580000000000000006755e0000000000000004807800000000000000101790000000000000003b86220000000000000049401200000000000000432a8400000000000000a10900000000000000038753c40000000000000711b1a6000000000000089b0440000000000000092018840000000000002130b8cc0000000000005e1801400000000000000f107ad80000000000010b46ea96000000000002aba453da00000000000287037882000000000001e3a3103c0000000000066b06aed60000000000067d42d37a0000000000035b0d4c100000000000c85d4318b20000000000188b84fffc00000000002148421756000000000481c87064920000000001f448b494a400000000041baf03449c000000003da0d6289e5400000000286945294b70000000002380335325e60000000000330d645e80000000004e96220514200000000336cc1424a68800000002f4cd248161c000000017ec4463c2004e00000019976943d2540000000078240c1f60024e0000002d9a20b826da500000004cadb7f010b280000000aecb805440c21e0000045718ecc0450eda000000e4400fe384b2740000032a8e38c00e04f80000284e49152b2c4334000069ac05da8c0a208800008a488427a63086780000023dcf80a221cc08000082863816817913160000a5090f2a89aa34020000e172598e8c181198000cf0ec1a08491122ca001a1675ca57282175760048181411e1b250511400205dc102c632c6ac160063a4bb406400a808ea02103085c2986ee6c1540000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x20000000000000000000000000000000000000000000000000000000000000000000000000000003c0000000000000000000c000000000000000000e8000000000000000000b60000000000000000002c000000000000000003280000000000000000000a00000000000000000ca200000000000000003c040000000000000000229e00000000000000009c28000000000000000138f40000000000000000a0340000000000000007551e0000000000000007d6040000000000000016588c000000000000001d30800000000000000015b88a00000000000000fd814000000000000000403ba000000000000002fc26a200000000000003b248800000000000000b02bb400000000000001814403400000000000001dc214400000000000018c121b40000000000000c66039e000000000001a0a700a400000000000222ae602200000000000332984b5400000000000f0221c564000000000018d012d420000000000004dc874c7c000000000005d5900530000000000091cb02d0a00000000001a0601d29340000000000601107d02a000000000404cab99c3c000000000038b940210c0000000007414c98bb6200000000004492c2d6e8000000000b08b41c0c8c00000000e5b614f5d5e800000001d449d92170880000000102297d70e1200000000360e731580e800000000a33891131251c0000000ae6a121874660000000308806b1ba012e000000547c622e42db0c0000000755005841c1c60000000aeb3d70208cd40000004322320829c986000000463a51218a61900000015d8618667104c0000016ad2710c8e759200000040cb158685054620000111a3818ca58c02a000038155217412ae21000000782819221153f8c000175598650d02459a8000724386aaba7382852000b6d75a3c91981672e000f07cd050922888520000553a0daae80cbc8a00012c698a413cd8ace220031578ca607c01adfc200660a4699c958289230000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if d < 7 then (0x20000000000000000000c0000000000000000001000000000000000000016000000000000000000280000000000000000004a000000000000000000180000000000000000025a000000000000000001c600000000000000000be00000000000000000128a00000000000000001242000000000000000005960000000000000000c04000000000000000009a6200000000000000015a100000000000000001c3f6000000000000000f8950000000000000000148000000000000000005b5ec000000000000004dc27200000000000000c42092000000000000019ca2c40000000000000029b6f6000000000000063b8050000000000000009715c0000000000000163480c40000000000001405834600000000000040446afa0000000000005d2c4756000000000000114146be0000000000022e4c72a40000000000004354d04a0000000000087473a18a00000000001467fd66180000000000063c30b094000000000002e780830000000000006106074b0e0000000001140a0247bc00000000030584c00b9200000000058b016f232000000000027050d2c0ec000000000918a2054014000000000e2a823e90060000000010c3927405da00000000c454a911055a00000000317a0e10247600000002a38839083e4a000000040a092e92a2760000000428f082164bce0000000e7a521704b95000000019aa248080bc4c0000003227bd5129afa200000003050bd507034c000000340ac674d644c400000089b77cd3417a86000005543c01de089d5400000f80994020f8c6de0000145069507d0012140000203018959432947c00000634da42aefaf4d400001a9420b1b58074060000164177fc0c0e165800025002b13619608e1c0001b18b4224220c04c20000ae5594a00ca661d8000061203c94a1ec81c200066a10111e5984140a0015af074e06894df2e6003c30c63d43a233841c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if d < 8 then (0x2000000000000000000000000000000000000000c000000000000000000000000000000000000001200000000000000000026000000000000000000c8000000000000000000a0000000000000000002d2000000000000000003d80000000000000000044200000000000000001020000000000000000012a000000000000000006004000000000000000092d40000000000000000c28e000000000000000045160000000000000005d7ee000000000000000b99b4000000000000000156680000000000000000697c000000000000007a34ac00000000000000410d48000000000000014e058200000000000002638980000000000000016415d00000000000000166213e0000000000001b2055080000000000001021223e00000000000065522634000000000000150076e4000000000000758cc6a80000000000038a85d396000000000000633414d20000000000046980519200000000000331280f4e000000000015a2f410d200000000000e31e008b8000000000008f3e937820000000001b013a032c000000000000a49502114000000000544340e28c0000000000650eb1d35940000000006a3623498da000000000e72a38849f0000000005424407110b8000000000d05091b0464000000000124a5908818000000029c21b924545c00000007764c55082b4400000001aa69383ed1b4000000030907ea2291fc000000104c091a2770e00000000194848958145000000022fc4090c690a2000001cb21428a60826800000085842c9106e13200000543b5f32132608800000919a441229aa0c4000001a50cd2aa099102000001182c6326f0e0ac000023880b6045d0f58c00009142a0853e412d600000252892d4407302820002a49dc0b1203bd374000300a990b86a740a42000bcd390ad0abe798c0000eb55594846a4773820039069c8be08b0682a80055af03f206c19106b80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x200000000000000000000000000000000000000080000000000000000001400000000000000000000000000000000000000240000000000000000001200000000000000000012000000000000000003e6000000000000000001700000000000000000060800000000000000001bb20000000000000000112200000000000000001d800000000000000000418400000000000000015c1e000000000000000001aa00000000000000044000000000000000000b8a64000000000000001024a800000000000000009106000000000000001e4a68000000000000008a26620000000000000009fa200000000000000319d1ce000000000000022ab8f40000000000000f0b108c0000000000001392822a000000000000175285080000000000002a841874000000000000a72d3a5c00000000000059e69388000000000001d218bb2000000000000065a4c8a200000000000b46811942000000000000d8aca1de0000000000141d311b76000000000031227e53c400000000001868809762000000000010ed24351000000000010aa935498800000000005e0898d5e800000000056542148424000000000cd030ad25920000000038e1b8a809040000000028c68ca04062000000009085846c623200000000858860949560000000006421a8438a880000000404095af2a0ea00000007483d19075a92000000019549812d0b940000001d030945a964b400000041cc66059200ae000000e063e522ba9a0000000050a9422b0963c2000002cb8402abca4012000000e1ab01aca452cc000006a10522e5caf8f0000006c806293f33b59c0000195ea94a8029300000006584138013210312000028d589081d46db4a00000d0472b6e452011c0003a84d181c5466631e0000280acc608aca74440006ccc5c4b011077bec000816545e14d023b118002c4a3d00253762600e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))) else (if d < 14 then (if d < 11 then (if d < 10 then (0xa000000000000000000080000000000000000002800000000000000000028000000000000000000e000000000000000000084000000000000000000940000000000000000072800000000000000000e80000000000000000007da000000000000000032e600000000000000006f360000000000000000410a000000000000000100180000000000000000164a000000000000000418560000000000000003591600000000000000072a5e0000000000000000199a00000000000000748f560000000000000060c27a000000000000006b240800000000000003c31120000000000000079b894a0000000000000a0150f800000000000000442d400000000000000ad6a614000000000000667e0b0000000000000003e1161c0000000000018c1652360000000000007150162a0000000000020904060a0000000000030a7ca04e00000000000f28569252000000000031021c30d000000000007aa844b3cc00000000000213a27f48000000000018884fe114000000000210020892d400000000020446a98804000000000a6e5a28222a000000000801c4394fda0000000007a0da4ee7d000000000030a691173f200000000120b360c66c600000000e2c21f443ec600000001ea2816ae2100000000008b840d0b942e000000068a832dc198000000000c0972c214807a0000001e599c56108d640000003117c81f4427100000006611a99a02e34a0000001e4ace0a4a3014000000fd44d85298629000000447405a6c4ab928000004e85ce9364014c00000031470c40d140e4000002e894c7437dd20cc0000453c66dd64b190980000c0ac158c1db85a28000040b4292cc509c2c80002c156a7307b0b034400005200a7230b2403480001e249061850b282aa0012828725a05923c9cc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x20000000000000000000200000000000000000006000000000000000000040000000000000000000000000000000000000070000000000000000000a800000000000000000050000000000000000000200000000000000000042e000000000000000005500000000000000000144000000000000000000078000000000000000040da0000000000000000d4c80000000000000001fc6200000000000000024f160000000000000002e2600000000000000008045000000000000000030408000000000000000d0468000000000000005e680000000000000000220ac600000000000000990b5a000000000000025ac42e000000000000009cbc2800000000000005d00a320000000000000a0184d4000000000000242e635400000000000073652af0000000000000c3d20460000000000001502b72360000000000010740df1800000000000040d8f99a000000000000e6a2a530000000000001704b481c0000000000151999815400000000004434294b88000000000017d19c883000000000010322b2d02800000000019439e0e0f800000000063d99e30c2a00000000037b0fa0628000000000112011b09e0600000000299347c248c400000000134252880ec4000000005f5948a11088000000010ec45626230800000002b0828565e68000000001013b855dc0520000000cd75884bc4486000000022e3233c3c46800000007c5a49048c2800000003f0d600ec0398c000000ef02acc7e5128a000001cb68a33e378c5e0000014029389a800592000004ae406ae0b304220000028359d2a42b18b800000022724fd840e688000001e250a30629651200005259e06cd2d48c24000002789694000fe35400015a02236ed1f5d82c0003cc82c43d002846300001396804c8612c87820004068c44dc1e0826060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if d < 12 then (0x2000000000000000000000000000000000000000c0000000000000000000a000000000000000000100000000000000000003200000000000000000028000000000000000000200000000000000000020600000000000000000188000000000000000000a40000000000000000106400000000000000001c30000000000000000013860000000000000000ec080000000000000001f00000000000000000000a2c00000000000000044500000000000000000e3a500000000000000016006800000000000000282c280000000000000004311e000000000000002c0c68000000000000001caa4000000000000000ccb14200000000000006002b400000000000000615b8ae00000000000014c2894000000000000028a2529c00000000000048a0d802000000000000aed68430000000000001d186359e0000000000025063cea80000000000019d99a00400000000000b41b496ac000000000007ec895142000000000002624ae83a000000000039c9fe9e5000000000000449237c9000000000001590aa69240000000003d68110949e0000000003d2720121040000000004135259e53000000000082f5104ed0000000000026a8c81c01c000000002a1c1aa82110000000001c1442029f4000000001976546d0601a00000000000ac5803a1c000000022da342695c220000000a2150e1589f240000000bf080ab6140820000002247ce1742dd3000000010c549d0a00c960000004795984c40672000000083640285ea0a88000000d10882c61f126e000000810acc042dabc40000002ce8dae004b2060000102e526300176c4800000542f358c988856a00004ec8755a067a38200000154997b1024323100000f948c9033a60b822000290047cbcadb921220003526a1c395bd2224c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if d < 13 then (0x2000000000000000000080000000000000000000e0000000000000000002400000000000000000022000000000000000000520000000000000000005800000000000000000180000000000000000001920000000000000000011c000000000000000000bc00000000000000000c600000000000000000534400000000000000009ac60000000000000001b164000000000000000001e800000000000000001f160000000000000004b34c000000000000001c984e0000000000000003d21e0000000000000024159c000000000000004554a0000000000000006558d4000000000000010460c600000000000005e93b880000000000000b0e3a0c00000000000007d298d80000000000002013c33c0000000000004e5d4c2e00000000000078a23282000000000001000f1072000000000000414614a40000000000041a3050980000000000011144012200000000000195c6ca3e000000000003d0a5d59c00000000006263711bb000000000005d60413b080000000001ead014d3d600000000000b32620a200000000002202304299200000000083967b154d8000000000d044b1017d00000000030515a06bf0e00000000556c5f30f39800000000f290a600e904000000014288973008140000000149784c8e509a00000000027c21163b6a0000000824e1e51c5596000000093600405c8b520000001cafc5688a9128000000068a52809a700c00000000499721bb58a000000050ccbc3623d36000000316ad90c08850b2000004017c5248015aa40000013800114885b2b60000116968980310024600003a0a12929cee5d640000426398fb552e74bc0000b15184d09237991400014ea40f05e0380bf20000a101100138966dd400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x2000000000000000000000000000000000000000000000000000000000002000000000000000000020000000000000000001a0000000000000000004e0000000000000000011a000000000000000001980000000000000000056a00000000000000000934000000000000000019080000000000000000282c00000000000000000cec000000000000000078d60000000000000000278600000000000000002d020000000000000000399000000000000000010aaa000000000000001942c800000000000000118316000000000000007a4a00000000000000000b36440000000000000051a1c800000000000000f8e04e0000000000000116c03e000000000000026b31d00000000000000049ae6200000000000006802e600000000000007075731400000000000030d69a0400000000000107083200000000000003c8f409220000000000044b210eaa00000000000487d638d600000000001ee248a4860000000000180a542bb600000000003cc83cda82000000000080499482040000000000239a842a4e0000000000cd0c8e215400000000006bb458a6420000000002dcd95e0c100000000003cc0458016c000000002182890bec12000000001ac87206119c00000000d841e2c924e800000000172d2a2426b200000003a11a2a5662040000000020935095b8a800000003f0c884e81d120000000851a9565078640000001236304613ab600000003415455ae061520000002421c648a04ca6000001e881a10a5688e0000002604388a127030a00000233001c9e6b180e00000c408654092ca41c00000f03c10ce1c9603800002d6802c945b83c2a000013292e86dd30a81c000034a8c1f2312a42b800010ac8a13d281e22300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))) else (if d < 16 then (if d < 15 then (0x2000000000000000000060000000000000000001000000000000000000000000000000000000000220000000000000000007000000000000000000138000000000000000002880000000000000000016c0000000000000000010e000000000000000015a80000000000000000061400000000000000006760000000000000000050e8000000000000000014b200000000000000026c2000000000000000000142000000000000000c51a4000000000000001893f000000000000000255140000000000000006f3a38000000000000009830240000000000000103cd980000000000000182ac28000000000000010b55d2000000000000012c4c08000000000000170074a000000000000036aa083000000000000001129320000000000000e124d3120000000000004908eea4000000000002da2c4a54000000000002e08e1c4200000000000a9013811c000000000014d423852400000000003171175e5c000000000026340aca6200000000006de161e5120000000001c64682d830000000000201333c9c68000000000043c92300a400000000008094c3957a00000000150256804cf00000000015460fb846d800000000590ad59140da0000000092a180f3384800000000920324599c00000000011adc8a1340ae000000001d270884c20c000000043c27c2c36022000000088d65d3a7b510000000211e908313d10a0000004e151088c69204000000a194942681a556000000cff4b74bc25088000001e506a0311120e2000004ec9a373727c22400000922040106a68dfe00000ac7003cc2a4c4ca00003431b12484340d9200007223c9ab001eef480000a3998aa03534d698000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x2000000000000000000000000000000000000000000000000000000000014000000000000000000200000000000000000007000000000000000000062000000000000000000ae0000000000000000036c0000000000000000028c00000000000000000408000000000000000000c600000000000000000e1000000000000000005530000000000000000066e4000000000000000008c00000000000000002c584000000000000000079d2000000000000000aca4c000000000000001900be000000000000002934ba0000000000000026c3b00000000000000007c06c0000000000000003fe44000000000000003e56c2000000000000022a8a8000000000000004c0e758000000000000169085220000000000001d51c1840000000000000905982c000000000000591a90000000000000002ce8ba7400000000000250610ca0000000000006c983c9540000000000004c8a232800000000001054894e20000000000028244ad61400000000007bd385e52800000000003cb023ea4a00000000017216519c5400000000001b810b733600000000071902034e60000000000211d7218d4800000000112a7ce00d800000000014265a60c1900000000004821617e80200000000e42cc1e1c800000000002697028893540000000031d08110bd4c00000006e44c219388280000000f51bd70c3a75400000004a11b22cc6dc00000000024678c14e9400000005be12643538220000000689260620c826400000098f8a77c90315e0000004808f60cb45004000002906fdc750091f400000b892492304f04c400001041abc02472803e00001505f022750b1cd00000621a823993b21ce800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if d < 17 then (0x4000000000000000000020000000000000000000000000000000000000040000000000000000000c00000000000000000003200000000000000000398000000000000000001a40000000000000000000a00000000000000000a90000000000000000006ba00000000000000001c840000000000000000030e00000000000000008704000000000000000029ae00000000000000019422000000000000000f7c1600000000000000046860000000000000002b15000000000000000020546400000000000000348040000000000000016e618400000000000003654d240000000000000047c3320000000000000309ae0400000000000016b2451a0000000000000b5340280000000000002002e4f40000000000001223c290000000000000e944280a00000000000391f2035e0000000000013605d8860000000000008081ce6c00000000000cb08a8124000000000010320a8228000000000010b906d8da0000000000674264941000000000006cdd4255220000000001200c38cc4000000000052de59141780000000000824903a8140000000006c327a888820000000009d612c41460000000002c238025030e000000004ae6069cb42e000000011894f36790c6000000020061574424000000000011a600212b58000000058b6b710152560000001a9c9434a703d4000000040e644562f7100000004458c41598b0b0000000ff004f8922407000000129a0b5b567f4700000018fc38cc826a6ce00000180062d672123e8000009151924c23900e000000db5348c1ea2005400002ec44892a3621f300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if d < 18 then (0x40000000000000000000800000000000000000018000000000000000000080000000000000000007800000000000000000020000000000000000001a000000000000000000384000000000000000003ce0000000000000000091c00000000000000001384000000000000000021c400000000000000003d220000000000000000d85000000000000000019040000000000000000389300000000000000002c588000000000000000c66a0000000000000001b298e00000000000000077e42000000000000003913d80000000000000080d126000000000000015178b8000000000000012344ba000000000000006ac1c000000000000002a093400000000000000094730c0000000000003b4b040a000000000000136248900000000000001db0a002000000000000d010366a000000000002700e001200000000000410c7604a000000000007552ac4ce000000000008157ab038000000000021c0334e44000000000010aab88a7400000000005225654900000000000052d853c83400000000008b18c7563000000000041b8122e45400000000044db0f2c01e000000000082df031824000000002149b0581f3c000000001c411009bc240000000011724097428e00000001421c04cf5f040000000188d632191908000000004134208c31f000000008b690234be36a0000001a810edc8ac694000000210013c689c28600000064ac27b630a5180000004e85580218e58200000083532042cb1014000001ee600497a60e28000002a4a39725cd8be000000dd40e3f8372043c00001a1f4faa5032c400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x18000000000000000000000000000000000000001800000000000000000044000000000000000000cc000000000000000000c0000000000000000001c4000000000000000006c80000000000000000112a000000000000000024620000000000000000550e000000000000000054000000000000000000521c00000000000000004a300000000000000004f81c000000000000000249120000000000000003a88800000000000000152448000000000000001084de00000000000000d4420200000000000001688088000000000000001dd36600000000000000a015c6000000000000070e741400000000000002f93692000000000000345f271e0000000000000e17032a0000000000009089a0660000000000007c2d12460000000000032a0809ca00000000000407a8219800000000000021b410c6000000000000bea661200000000000382b60333e000000000064656b244000000000000713c1ab1c000000000020a99072a000000000001524c4135e00000000011a02743a000000000002200bc343ce0000000019f9848270f0000000003f30e87d1bbc0000000065234ba069680000000036287a0cb74e00000001e54099e406620000000096c5ae12026a000000012041da2458c20000000f5205098124800000000da047222d983a0000003fc3cfc0c118c40000004526180005986a000000e60801bb88df6000000102ed0c6086446c00000200b2322e591a2000000349840dd06b5872000008c4591c66b40bb200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))))) else (if d < 29 then (if d < 24 then (if d < 21 then (if d < 20 then (0x4000000000000000000040000000000000000000000000000000000000032000000000000000000280000000000000000006c00000000000000000028000000000000000000640000000000000000041a0000000000000000057200000000000000000e9e00000000000000003244000000000000000026280000000000000000587e0000000000000000bf10000000000000000020920000000000000001a5c000000000000000062a62000000000000001c1b2600000000000000020b0e000000000000004e910e000000000000006110c600000000000000821526000000000000001e910000000000000004523c8200000000000008320ea00000000000000eca1242000000000000208ac0020000000000000d0d238c000000000000510a0c34000000000000b70e63dc00000000000023d9232000000000000151e02a8c00000000000c1c5823e400000000001884c9e20a00000000000a18980a280000000000092340048a0000000000a024366d1c0000000001c108598e000000000002c5210badc00000000002dc4cfa820e00000000081c12d44c26000000000fda359e416000000000065d225cf480000000004238c93c8140000000007f8851b81210000000007a26716e442800000000931a8e5c200800000007ca236745711200000000a1a50a72d7460000000469c1104cad6c0000000d8130c6450fc00000002140082a80692a000000132dc0486a65d2000001dd588593218c3e0000013a670b0cbaf0000000020d022b1f53cdcc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x20000000000000000000400000000000000000002000000000000000000060000000000000000006c000000000000000000940000000000000000000a0000000000000000001000000000000000000216000000000000000008a800000000000000001892000000000000000035a20000000000000000521a0000000000000000eee0000000000000000062ea00000000000000029b08000000000000000700e80000000000000008048a000000000000001cca000000000000000010a45e0000000000000002110600000000000000b3918000000000000000b0e23e0000000000000130320000000000000000181ce80000000000000080b568000000000000102ee022000000000000128059c60000000000000feb40f2000000000000f318d2e0000000000001a9ae404c00000000000357d836ae000000000007e0da39d4000000000006985d213600000000000220114986000000000006f48e942000000000002588b824040000000000ea8812392000000000004d814a67c20000000002afa292026a0000000000005c1c6a48000000000873a0101ce8000000000443bc1923040000000011761c42020a00000000731862d2ac1000000000242e2864729400000000005d7e8593380000000241c308c7916e00000003779951480c5a000000063144d89826740000000aa4e0901ca5200000000ac170c5522c48000000030ed268954024000000195328226627a600000174006884b42034000002e4202bc89af93a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if d < 22 then (0x800000000000000000018000000000000000000340000000000000000004c000000000000000000060000000000000000011400000000000000000348000000000000000002c4000000000000000006bc00000000000000000df600000000000000001c94000000000000000072300000000000000000bb42000000000000000175d40000000000000003c12c0000000000000007646000000000000000056d88000000000000000ba02000000000000000391ca20000000000000039351000000000000000a2285a000000000000010101a800000000000000e5498c000000000000002824a20000000000000b250910000000000000012006a800000000000028ad343600000000000040f8c52c000000000000028d19d8000000000001e964c150000000000001ea018782000000000006c322961c00000000000518ce467c0000000000140c21550400000000003502600d8a000000000061148bca8000000000004c90163d8800000000013a2d2611c20000000001251b2641c0000000000508ae860e780000000001c038ac31820000000010560881e83800000000343506f485200000000033c9e08353640000000018973fb22e0000000001df2481204c920000000218f1213500d8000000032e01056a608800000000e8f06aa691e40000000101d21b33a0e4000000200931f215121400000052ae3088390e28000000e698c84223f28c0000018928467121c81000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if d < 23 then (0x40000000000000000001e000000000000000000020000000000000000001a0000000000000000005a00000000000000000120000000000000000000cc00000000000000000080000000000000000009800000000000000000015800000000000000000d840000000000000000098800000000000000000ce8000000000000000112a00000000000000000a4200000000000000002836e000000000000000e22140000000000000004015000000000000000036ac800000000000000580ca60000000000000000e6b200000000000001dd0c120000000000000388bc10000000000000008aea0400000000000001780d2a0000000000001959252a000000000000018f4a160000000000000250e136000000000000d4d000c8000000000000343f86220000000000015580a00a000000000004804e6860000000000002a04c2450000000000015a30614d4000000000030329b8202000000000051c44750980000000000740f4c1b820000000000104da4a894000000000114800a364a0000000003151cf832480000000006c8245a04480000000000626019be4e0000000020122d21815c0000000035eca5c02e2200000000a4d2287236e80000000012272487832a000000000350444c3a0a00000004be8265c0a486000000085072e78b108400000019c74104212ea40000003e880a04c732a20000004f730c2c8c12f0000000b48311ed4866d40000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x60000000000000000000a00000000000000000010000000000000000000180000000000000000001e000000000000000000a80000000000000000006a00000000000000000060000000000000000002e2000000000000000009100000000000000000180e0000000000000000040000000000000000000242000000000000000086c200000000000000003a800000000000000001602c000000000000000451da0000000000000002052e000000000000001a970c0000000000000016c8460000000000000004758c00000000000000d97d04000000000000004611700000000000000083c43400000000000000f4e61000000000000004c2e1480000000000001c901a0000000000000034d68980000000000000402be4240000000000006ef44d0200000000000024a14da8000000000002252dc52000000000000508ae5452000000000004a9e90722000000000019a196244c00000000002049446c900000000000502004278c000000000050923288ea0000000000845f5814a80000000000c7c08d99460000000001ad43a5ad90000000000449749ecd240000000001ccd05920b6000000002b0fc29089a00000000046c474e63e0000000000b0a0523009240000000031a004f86a2600000003537a018f9906000000000c269192845200000000393d9dc4162000000004c28de5e06a340000002810b64b58045400000062c43a42b64168000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))) else (if d < 26 then (if d < 25 then (0x60000000000000000000a000000000000000000000000000000000000000c0000000000000000000c000000000000000000e0000000000000000001c000000000000000000254000000000000000001a200000000000000000e3000000000000000000a5400000000000000000624000000000000000063620000000000000000b18c0000000000000001aa180000000000000000334a00000000000000022118000000000000000bc0a2000000000000000261c6000000000000002949040000000000000045144c000000000000000183d80000000000000191493400000000000000a04d7a00000000000000c71b2c00000000000000f896a800000000000003a18cea000000000000112d12b2000000000000152880d8000000000000414c521c00000000000111406482000000000001650b1c1a0000000000057305b4a00000000000082a83544200000000000a1328cda6000000000000a3f5019600000000002111466eb0000000000018e70d98f00000000000134f8445140000000001f2e9c210dc00000000030228863894000000000005792cabd6000000001edc11d91618000000000c30ab3969d200000000245c3d1ac7d0000000009091391ac482000000008f1763438130000000003c919160519a0000000225e8886555ae0000000300301c0072bc00000000c916145353100000003954c3876740c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x20000000000000000000c0000000000000000001400000000000000000002000000000000000000560000000000000000001e00000000000000000182000000000000000000ac0000000000000000048c00000000000000000be00000000000000000020c000000000000000008180000000000000000189000000000000000008d660000000000000001069c0000000000000001518c000000000000000742b40000000000000009604000000000000000060f42000000000000000a778e0000000000000036c706000000000000008aa63e00000000000001aa6a900000000000000024eed4000000000000026a40400000000000000a0c0946000000000000020f621c0000000000003b11be4c00000000000010a53a120000000000006214bc4200000000000017a9d6f00000000000009a0350d20000000000000c0c9f8c00000000000d00a49a2e0000000000100230520c000000000007a980e4d000000000005003c502e4000000000028c60a915a000000000190dd652a860000000002e80344205c00000000050cc100273a000000000948612530f400000000041b263c45f8000000003969820820140000000015603ab10f1a0000000084884c56171400000001242726136304000000011a12270dd5c400000005745da6273b240000000212872a008b7200000000918a2c4107ba0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if d < 27 then (0x2000000000000000000040000000000000000000400000000000000000010000000000000000000020000000000000000000400000000000000000028000000000000000001080000000000000000000e0000000000000000045a0000000000000000002e000000000000000009060000000000000000034e000000000000000043d800000000000000003ad60000000000000000f6c00000000000000001834c0000000000000004472e000000000000000beb48000000000000000e881200000000000000119c4400000000000000404c4000000000000000430732000000000000015bab0400000000000003c3204200000000000005c03612000000000000066806da000000000000064d1e2800000000000002d25ed00000000000001e211326000000000000bdc0d13400000000000018704c160000000000020e1fe23e000000000006e8c0d4020000000000020479228e00000000001d2805204e0000000000020fe1c10200000000004d0b4a0054000000000081806444640000000000f064108178000000000149102ed8400000000000eb140aa542000000000909e205091c000000000de22dd0044c000000001fcc32cca28200000000070a4cc209f8000000000ac5251c129a000000010e649884e5420000000233836489d8420000000201dca4848d02000000005f485c081a5c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if d < 28 then (0x2000000000000000000000000000000000000000000000000000000000014000000000000000000200000000000000000000800000000000000000060000000000000000000d80000000000000000029c000000000000000004f400000000000000000b9400000000000000001a4800000000000000002844000000000000000003860000000000000000207e00000000000000001830000000000000000107e20000000000000000300200000000000000083344000000000000001d85260000000000000000e786000000000000004d2a38000000000000007866b2000000000000008090840000000000000222088800000000000007bc038600000000000001044344000000000000001c71ec00000000000024142272000000000000037404c20000000000001f0c1b0a0000000000001954fb02000000000000bc329034000000000003a12526bc00000000000309784534000000000000f92325920000000000001bef2352000000000008385029340000000000261c132a100000000001557e8c25740000000003641c240b10000000000000f9b8828e0000000003030680ba040000000017490e2460de0000000014917c35c3120000000028b18c829874000000006244241c99360000000154abd2238a0400000001f694b0c804b200000005b0462228133000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x20000000000000000000a000000000000000000080000000000000000002c0000000000000000001000000000000000000014000000000000000001440000000000000000030a00000000000000000722000000000000000008000000000000000000136200000000000000000c04000000000000000073c60000000000000000b508000000000000000092480000000000000003054200000000000000008208000000000000000ce040000000000000000246dc00000000000000299472000000000000000402f200000000000000032a5c00000000000000200ea4000000000000013b6440000000000000059181a2000000000000009421b0000000000000190302ec0000000000001c1d162a00000000000061ac0232000000000000b382fc60000000000001cc139334000000000000219acd06000000000004b1aaea6000000000000e9c502c82000000000003ac22542c0000000000208a83b886000000000035f8a486980000000000503921c4b0000000000096485955740000000001626907d5a0000000000498f03a50440000000004bb910b1820000000000f300a53cb060000000016578f4e0dc0000000002b5c5c5fb0c200000000e94207022432000000018d1ad396c1c800000003002770d1c9e20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))) else (if d < 34 then (if d < 31 then (if d < 30 then (0x200000000000000000006000000000000000000080000000000000000001200000000000000000004000000000000000000580000000000000000001a00000000000000000118000000000000000000ec00000000000000000080000000000000000004e000000000000000001a840000000000000000393a000000000000000060d60000000000000000024a000000000000000182be0000000000000000a1c400000000000000048ffe0000000000000003c7a800000000000000046100000000000000002595740000000000000054d110000000000000005a00200000000000000020102000000000000002858cb200000000000002639a9c0000000000000e4a90660000000000001e2621f2000000000000235961800000000000006d74325800000000000083f0222c0000000000010d4e0184000000000001065981da000000000002e7f210a400000000000059213880000000000009511c550a0000000000160c24052000000000000db10ad184000000000010388f57ce0000000000704355c8d20000000001a65cd52ed8000000000638c1c404d40000000009e23d1141a6000000000d8819ae027a000000000c3dc0fd80a000000000628ad690790200000000f49f70012780000000015013aaae5c18000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x20000000000000000000400000000000000000014000000000000000000280000000000000000002a000000000000000000a000000000000000000048000000000000000003900000000000000000020200000000000000000c80000000000000000003200000000000000000178000000000000000000024000000000000000036a60000000000000000a82000000000000000026474000000000000000519380000000000000005965200000000000000111a520000000000000026c0720000000000000068ac600000000000000090a84800000000000000bf33120000000000000082729e0000000000000471d802000000000000005c29800000000000001441182000000000000019190d20000000000000628eac0200000000000034bc76980000000000006884961800000000000000c2daa00000000000008781bbd4000000000004fa994a3a000000000010318000900000000000283fc35126000000000008c3017dba000000000044d044b87a0000000000df809258300000000001c12800ed7e00000000070460028dde0000000004432538e5c60000000002670172fb0000000000263c50274d88000000006d0c03d8d44800000000803df0a03ed000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if d < 32 then (0xc0000000000000000000200000000000000000062000000000000000000f6000000000000000000a400000000000000000142000000000000000000940000000000000000013c000000000000000008300000000000000000171a000000000000000010520000000000000000a47000000000000000015948000000000000000064b000000000000000030d120000000000000004255c00000000000000133dc400000000000000190898000000000000004506d200000000000000225884000000000000013ec46800000000000000924b8800000000000000d07c440000000000000784040e000000000000090ccd860000000000003c2510ae0000000000004000f14200000000000028694162000000000000b3862bf20000000000030096025c0000000000001412e0a6000000000009ba23643400000000000d81d0894600000000001e42173b18000000000033c7b0c4a0000000000005f053aa6800000000002d131210a400000000030f98cd79200000000006c8d0d164140000000006c47c70c818000000001d110a216196000000001631903b0a2a00000000129c34544d000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if d < 33 then (0x4000000000000000000080000000000000000000200000000000000000028000000000000000000620000000000000000003000000000000000000110000000000000000000260000000000000000002c00000000000000000a22000000000000000014820000000000000000380a000000000000000008f40000000000000000d208000000000000000024dc00000000000000000d0600000000000000025294000000000000000f41ea000000000000001800000000000000000009e430000000000000004513420000000000000002284e0000000000000126919e00000000000000cce1a0000000000000028dd3b0000000000000023c6d6e000000000000153501a80000000000002b50e830000000000000652067800000000000000827005e000000000000baaa1500000000000000ca150ab80000000000075d929d0000000000000804c3e45e000000000016c4bef05e000000000029c9182c0600000000000384055468000000000057b57889340000000001c302225682000000000030b4c01e800000000004a68a221b30000000000cc709990822000000001caca175258000000000068231303e32000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0xa000000000000000000040000000000000000000200000000000000000074000000000000000000e4000000000000000000780000000000000000000400000000000000000014000000000000000002380000000000000000005000000000000000000d2a00000000000000002032000000000000000078540000000000000001958800000000000000020c8000000000000000028d18000000000000000a5686000000000000001c89280000000000000020cfd6000000000000000130400000000000000092912000000000000001c68822000000000000032686c00000000000000241420a00000000000008c96c28000000000000169a2c1a0000000000003b48c256000000000000307302240000000000002405c74000000000000110d1ecca000000000000467bc89c00000000000378110e0800000000000105066942000000000016b19299840000000000075122f406000000000041081706040000000000318000d2d0000000000196a61818520000000002ef11102a9a0000000000301c524b2a0000000005d32c30c23a0000000002b08497e8f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))) else (if d < 36 then (if d < 35 then (0x8000000000000000000000000000000000000001a00000000000000000030000000000000000000c000000000000000000174000000000000000001c0000000000000000004100000000000000000004a00000000000000000d52000000000000000037c0000000000000000006b0000000000000000026080000000000000000425600000000000000016608000000000000000720180000000000000007e818000000000000000380c0000000000000002dd276000000000000000175020000000000000043a1d800000000000000859e6c00000000000001874092000000000000029cc1120000000000000e83d2b000000000000018064014000000000000077bac840000000000006c3189e0000000000000d1c0198000000000000074b9c02600000000000141a03800000000000005810a231a00000000000d42c907a8000000000016a8fc2c4000000000002ed8914840000000000059c865dc0a000000000058341464a20000000001a6a23005f80000000001c784616a5400000000078c52ba20aa00000000083d15f6b0060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x6000000000000000000060000000000000000001200000000000000000024000000000000000000000000000000000000000000000000000000000062000000000000000000300000000000000000063c00000000000000000cb600000000000000000d040000000000000000264e0000000000000000030e0000000000000000de3e000000000000000029200000000000000003751800000000000000060a38000000000000000dae10000000000000001926c60000000000000014122000000000000000330e4c00000000000000cc0a5a00000000000000440b960000000000000282a1020000000000000481a5bc000000000000071095dc00000000000000887a6a00000000000018123162000000000000621c860c000000000000f5787a34000000000000668a08460000000000012b8ca85000000000000416ca362800000000000cb6afa54400000000001a8612b188000000000020c031121800000000001c0330d19a00000000007c6c08aa86000000000145c00ca00e000000000318a58b222a00000000009d93084960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if d < 37 then (0x140000000000000000000000000000000000000002000000000000000000200000000000000000005c00000000000000000140000000000000000007820000000000000000088200000000000000000ffa000000000000000021e800000000000000003c6200000000000000009a3000000000000000011a7c000000000000000050f00000000000000006bc260000000000000002f2a00000000000000004966c0000000000000001503a0000000000000042580400000000000000b4504800000000000000ba62080000000000000121864c00000000000001e28d44000000000000061234040000000000000beaf01a0000000000003113805e00000000000061621c6c00000000000099180808000000000000f97d1480000000000002932c01500000000000061018bcf200000000000a304e8d0000000000000901448e080000000000127f628bd000000000004f31c2952400000000000c92c3ab04000000000190a065678600000000008f46e8e06000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if d < 38 then (0x8000000000000000000120000000000000000000600000000000000000010000000000000000001a0000000000000000002060000000000000000014e00000000000000000bf600000000000000000ec200000000000000002740000000000000000068500000000000000000d4800000000000000000c68600000000000000024916000000000000000303020000000000000009449e0000000000000014c4e00000000000000013f4340000000000000010871600000000000000a2856600000000000000b9a4580000000000000010662200000000000001e9d1c0000000000000018b5c2000000000000010a113a80000000000000ee828d20000000000004097c02e0000000000000a4d1094000000000000e3348bd000000000000354448c80000000000004301417720000000000032481340c0000000000033b310030000000000024a425b0a000000000002a0a59c0440000000000a09134fb000000000000ed50e6c20a0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x20000000000000000000200000000000000000002000000000000000000080000000000000000003a0000000000000000005c0000000000000000001a0000000000000000009400000000000000000008000000000000000004aa0000000000000000050600000000000000000028000000000000000004c80000000000000000300800000000000000001ed800000000000000002baa00000000000000008ec200000000000000002ec800000000000000009eb00000000000000000824a000000000000003003c4000000000000002ba18c00000000000000113f2400000000000001159816000000000000007c435600000000000004713cd20000000000000f0490b200000000000000f7d00200000000000004140e680000000000001c43244400000000000013e23554000000000000161b59a60000000000004dfd2122000000000003e2f227d40000000000008408698e0000000000065f88282a0000000000296c1bd00000000000000d50f3505800000000009606e49604000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))))) else (if d < 59 then (if d < 49 then (if d < 44 then (if d < 41 then (if d < 40 then (0x40000000000000000001c000000000000000000200000000000000000001600000000000000000018000000000000000000a2000000000000000002ca000000000000000005fe000000000000000004a200000000000000000882000000000000000001f800000000000000007ec80000000000000000731c000000000000000134480000000000000003928000000000000000008e0c0000000000000002889e0000000000000001fa160000000000000009f65a00000000000000287f04000000000000001102c800000000000001845e0a00000000000002b92820000000000000022ab27800000000000005512a3a0000000000000d36c4560000000000000881970000000000000027e95132000000000000a8e0a1440000000000010c01271c000000000003258f2182000000000003b061601c00000000000d9488085e000000000016639a2c08000000000037568850a00000000000600418203200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x200000000000000000004000000000000000000080000000000000000000c0000000000000000002e0000000000000000004000000000000000000010000000000000000000c000000000000000000224000000000000000000300000000000000000021c0000000000000000024600000000000000003e7800000000000000002b0a00000000000000004998000000000000000049300000000000000002a064000000000000000505400000000000000002818000000000000000093456000000000000000621be000000000000005a3b6e0000000000000040ee4a000000000000003c1f12000000000000036ae38400000000000004998c2000000000000005134e0e00000000000004d8b04200000000000011a429cc000000000000100a04b80000000000005674562a0000000000000697661e000000000000bc8cf46c0000000000022e20051000000000000443e588c000000000000cfd610d4400000000001f0a28d4e80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if d < 42 then (0x40000000000000000000000000000000000000016000000000000000000020000000000000000003c000000000000000000c6000000000000000000b400000000000000000114000000000000000002a00000000000000000027600000000000000000224000000000000000015d400000000000000004c220000000000000000a3c80000000000000000380600000000000000028d320000000000000002202c000000000000000bc920000000000000000d607a0000000000000002026a00000000000000508518000000000000007412480000000000000005795000000000000000c01460000000000000060706a0000000000000007812d20000000000000ecc4272000000000000056afe060000000000000c0d5612000000000000b4b82e22000000000001d48c0ace000000000002590920a00000000000008844a6ca000000000004e1489e0a00000000000a8a184a44000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if d < 43 then (0x6000000000000000000080000000000000000000200000000000000000000000000000000000000620000000000000000006000000000000000000006000000000000000003e20000000000000000074000000000000000000f1800000000000000000e200000000000000000105800000000000000001e1a00000000000000002a1600000000000000000280000000000000000301ba0000000000000002e3ae000000000000000590c0000000000000000853c000000000000000045812000000000000000a48e800000000000000b66ff80000000000000101fc90000000000000005155360000000000000402541200000000000003f0c99a000000000000090401920000000000001f24ad28000000000000225c8ce800000000000047c79084000000000001fd2cc2d0000000000001bf1951b2000000000003d0c20980000000000005f22384f800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x200000000000000000004000000000000000000080000000000000000000c00000000000000000028000000000000000000400000000000000000004e000000000000000000b6000000000000000001560000000000000000009e000000000000000009380000000000000000091000000000000000001a1600000000000000004106000000000000000070ea000000000000000103d6000000000000000290d400000000000000070e4c0000000000000000d97000000000000000009c16000000000000002c9776000000000000002c109c0000000000000033152a000000000000006152ee000000000000010946d600000000000004a143c800000000000000e84a40000000000000032252940000000000001529040a00000000000014292c8200000000000058036938000000000000278505de000000000001b50c1b48000000000005261812000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))) else (if d < 46 then (if d < 45 then (0x800000000000000000006000000000000000000200000000000000000004a0000000000000000009000000000000000000068000000000000000001d6000000000000000000540000000000000000088c00000000000000001950000000000000000001cc00000000000000000e26000000000000000019660000000000000000dc6000000000000000010e0a0000000000000005064c000000000000000050f80000000000000004004e000000000000000ac0000000000000000030cabc000000000000004162aa000000000000018062100000000000000201394000000000000006d6e43a0000000000000a5140980000000000000facc48400000000000028e9686800000000000021ae7f0a000000000000827274c00000000000009e34d11a0000000000018924c400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x20000000000000000000400000000000000000000000000000000000000020000000000000000000200000000000000000064000000000000000000a0000000000000000000020000000000000000024c000000000000000000200000000000000000022800000000000000000a5800000000000000002742000000000000000000c600000000000000002e240000000000000000c9a00000000000000001966200000000000000008884000000000000000291e4000000000000001e14660000000000000025cdb400000000000000082186000000000000006680780000000000000000b046000000000000001c9c7200000000000000ba78f40000000000000b74a8b00000000000000d00a74a000000000000028c824200000000000038dc90380000000000007975091400000000000042e6351000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if d < 47 then (0xa000000000000000000140000000000000000001600000000000000000002000000000000000000ce0000000000000000003000000000000000000100000000000000000005160000000000000000016a00000000000000000c8a0000000000000000095c0000000000000000202800000000000000004e4200000000000000018e1000000000000000023e4e00000000000000040e1600000000000000009602000000000000000b221e000000000000000ede24000000000000001011a400000000000000c9892800000000000001140e8200000000000001c828740000000000000464a518000000000000021a80a200000000000008901310000000000000282e12260000000000003809b460000000000000609c50840000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if d < 48 then (0x80000000000000000001a0000000000000000002000000000000000000024000000000000000000aa000000000000000000b20000000000000000008a000000000000000001640000000000000000038a000000000000000006e8000000000000000028bc00000000000000007d920000000000000000d4400000000000000000c9200000000000000000a010000000000000000028e600000000000000064188000000000000000511d60000000000000005f1380000000000000062c89400000000000000a29980000000000000005c147a00000000000003d7c93e000000000000002b26980000000000000848820a000000000000080e26c200000000000011244b2a00000000000073c0f16c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x12000000000000000000160000000000000000001a000000000000000000cc00000000000000000114000000000000000002a0000000000000000003e8000000000000000000d2000000000000000011a40000000000000000005800000000000000005920000000000000000074000000000000000000c2040000000000000003f0aa000000000000000185aa000000000000000c3b9000000000000000014be4000000000000002b4c8600000000000000194c76000000000000005c8782000000000000010e4550000000000000006419980000000000000105a1820000000000000a3c04b00000000000001a8272200000000000003e271c2600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))) else (if d < 54 then (if d < 51 then (if d < 50 then (0x2000000000000000000040000000000000000000a0000000000000000000a0000000000000000003c0000000000000000004a000000000000000000ce0000000000000000000400000000000000000208000000000000000000120000000000000000094a0000000000000000065000000000000000000420000000000000000000800000000000000000d02600000000000000001d1000000000000000026c1a00000000000000004400000000000000000026b6000000000000000b113800000000000000064ea2000000000000002f0ee000000000000000f0d44400000000000000542e0000000000000000130cfa0000000000000314ab38000000000000053888bc00000000000014b124c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x6000000000000000000020000000000000000001800000000000000000026000000000000000000660000000000000000005800000000000000000192000000000000000003b0000000000000000005600000000000000000000c00000000000000000b9200000000000000001314000000000000000003660000000000000000035c0000000000000001813000000000000000034aae00000000000000070830000000000000000a4670000000000000001352980000000000000018425000000000000000672e3000000000000000477420000000000000004d170c000000000000008c825a0000000000000015c7460000000000000a4881c2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if d < 52 then (0x4000000000000000000000000000000000000000800000000000000000014000000000000000000200000000000000000002800000000000000000182000000000000000000320000000000000000068a00000000000000000df2000000000000000001a60000000000000000289800000000000000006e100000000000000000aeb0000000000000000033b00000000000000002193000000000000000009aa4000000000000000c4408000000000000000b835a0000000000000029e6b2000000000000001384100000000000000040c41200000000000001dc135200000000000000577a6000000000000000469c2e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if d < 53 then (0x200000000000000000000000000000000000000060000000000000000000200000000000000000018000000000000000000040000000000000000003a000000000000000001d200000000000000000188000000000000000000f200000000000000000026000000000000000002ae0000000000000000021a0000000000000000556a00000000000000008668000000000000000041cc00000000000000030242000000000000000310ac0000000000000000a05c00000000000000081a0e0000000000000018934e000000000000005900060000000000000020ae76000000000000014433fa0000000000000043001c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x800000000000000000006000000000000000000160000000000000000000a0000000000000000000e000000000000000001380000000000000000005a000000000000000000b200000000000000000ca4000000000000000000000000000000000000129a0000000000000000260c000000000000000072500000000000000000644600000000000000011cb600000000000000005b1c00000000000000026504000000000000001a6214000000000000001120420000000000000065e794000000000000008a265600000000000001e64824000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))) else (if d < 56 then (if d < 55 then (0x2000000000000000000040000000000000000000a0000000000000000002800000000000000000054000000000000000000080000000000000000001a000000000000000001b00000000000000000037e00000000000000000c00000000000000000003240000000000000000284a00000000000000001d9000000000000000001c0200000000000000012d1c0000000000000000d14000000000000000062230000000000000000443fa0000000000000012ef2c0000000000000018759200000000000000278f0000000000000000e7c13000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0xe0000000000000000001800000000000000000016000000000000000000740000000000000000002c000000000000000000a40000000000000000023e00000000000000000504000000000000000000c2000000000000000004900000000000000000322200000000000000006342000000000000000009980000000000000001060e000000000000000141a6000000000000000687540000000000000003cd0800000000000000134bd0000000000000002aec84000000000000006545000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if d < 57 then (0xa000000000000000000020000000000000000000400000000000000000030000000000000000000ce00000000000000000020000000000000000000e2000000000000000000be0000000000000000045000000000000000001228000000000000000009a00000000000000000588e000000000000000023b80000000000000000ad86000000000000000132980000000000000003d0e2000000000000000500cc000000000000000b5404000000000000003d2484000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if d < 58 then (0x2000000000000000000020000000000000000000000000000000000000004000000000000000000260000000000000000002a000000000000000000e6000000000000000001f4000000000000000003240000000000000000064000000000000000000a0c000000000000000000100000000000000000347e000000000000000044580000000000000000fcc60000000000000001120c0000000000000002633a00000000000000008544000000000000000ea0020000000000000014310000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x400000000000000000004000000000000000000020000000000000000001e00000000000000000038000000000000000000e000000000000000000096000000000000000001a6000000000000000005e60000000000000000003a000000000000000004a0000000000000000011e00000000000000000280c00000000000000000b460000000000000001ea200000000000000001216200000000000000022340000000000000000056d00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))))) else (if d < 69 then (if d < 64 then (if d < 61 then (if d < 60 then (0x2000000000000000000000000000000000000000400000000000000000008000000000000000000200000000000000000001c000000000000000000d60000000000000000014000000000000000000006000000000000000001ec000000000000000005080000000000000000050000000000000000003d04000000000000000001700000000000000000081a000000000000000133100000000000000003600e0000000000000007e0c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0xa000000000000000000160000000000000000000e0000000000000000007e0000000000000000001800000000000000000034000000000000000001900000000000000000000800000000000000000e480000000000000000086800000000000000000c4c000000000000000038e2000000000000000064200000000000000000d1000000000000000002986000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if d < 62 then (0xa0000000000000000001e0000000000000000001400000000000000000046000000000000000000c80000000000000000004e000000000000000000dc0000000000000000027e00000000000000000570000000000000000011ae00000000000000000888000000000000000071200000000000000000c194000000000000000172580000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if d < 63 then (0xa000000000000000000000000000000000000003800000000000000000022000000000000000001680000000000000000005a000000000000000003b600000000000000000a0c0000000000000000066c00000000000000001e04000000000000000002080000000000000000df16000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x1000000000000000000006000000000000000000e80000000000000000000400000000000000000290000000000000000003d40000000000000000005000000000000000001f96000000000000000008000000000000000000529000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))) else (if d < 66 then (if d < 65 then (0x60000000000000000000a000000000000000000000000000000000000001800000000000000000020000000000000000000c2000000000000000000a400000000000000000026000000000000000002a000000000000000000cea0000000000000000052c000000000000000034060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x600000000000000000000000000000000000000040000000000000000003c000000000000000000040000000000000000002400000000000000000054000000000000000002a0000000000000000001a4000000000000000008a400000000000000000fc8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if d < 67 then (0x6000000000000000000020000000000000000000c0000000000000000002200000000000000000044000000000000000000cc00000000000000000166000000000000000000b2000000000000000005080000000000000000002e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if d < 68 then (0x200000000000000000006000000000000000000020000000000000000000600000000000000000008000000000000000000400000000000000000001400000000000000000192000000000000000001b0000000000000000000a20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x20000000000000000000a00000000000000000012000000000000000000020000000000000000006e000000000000000000ea0000000000000000009400000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))) else (if d < 74 then (if d < 71 then (if d < 70 then (0x2000000000000000000000000000000000000000e000000000000000000020000000000000000003000000000000000000072000000000000000000040000000000000000018200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x6000000000000000000080000000000000000000e0000000000000000003c00000000000000000000000000000000000000960000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if d < 72 then (0x400000000000000000008000000000000000000040000000000000000000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if d < 73 then (0x600000000000000000002000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x6000000000000000000140000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)))) else (if d < 76 then (if d < 75 then (0x20000000000000000000400000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (0x200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)) else (if d < 77 then (0x20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) else (if d < 78 then (0x0) else (0x0)))))))

/-- The colouring of the 4-set `x < y < z < w` of `{0,…,78}`: the colour of `{0, y-x, z-x, w-x}`
(true = red); translation invariant by construction. -/
def col (x y z w : Nat) : Bool := (row (y - x)).testBit ((z - x) * 79 + (w - x))

def chkRed (v1 : Nat) : Bool :=
  (List.range 79).all fun v2 => !(v1 < v2) || ((List.range 79).all fun v3 => !(v2 < v3 && col 0 v1 v2 v3) || ((List.range 79).all fun v4 => !(v3 < v4 && col 0 v1 v2 v4 && col 0 v1 v3 v4 && col 0 v2 v3 v4 && col v1 v2 v3 v4)))

def chkBlue (v1 : Nat) : Bool :=
  (List.range 79).all fun v2 => !(v1 < v2) || ((List.range 79).all fun v3 => !(v2 < v3 && !(col 0 v1 v2 v3)) || ((List.range 79).all fun v4 => !(v3 < v4 && !(col 0 v1 v2 v4) && !(col 0 v1 v3 v4) && !(col 0 v2 v3 v4) && !(col v1 v2 v3 v4)) || ((List.range 79).all fun v5 => !(v4 < v5 && !(col 0 v1 v2 v5) && !(col 0 v1 v3 v5) && !(col 0 v1 v4 v5) && !(col 0 v2 v3 v5) && !(col 0 v2 v4 v5) && !(col 0 v3 v4 v5) && !(col v1 v2 v3 v5) && !(col v1 v2 v4 v5) && !(col v1 v3 v4 v5) && !(col v2 v3 v4 v5)))))

theorem cr1 : chkRed 1 = true := by decide +kernel
theorem cr2 : chkRed 2 = true := by decide +kernel
theorem cr3 : chkRed 3 = true := by decide +kernel
theorem cr4 : chkRed 4 = true := by decide +kernel
theorem cr5 : chkRed 5 = true := by decide +kernel
theorem cr6 : chkRed 6 = true := by decide +kernel
theorem cr7 : chkRed 7 = true := by decide +kernel
theorem cr8 : chkRed 8 = true := by decide +kernel
theorem cr9 : chkRed 9 = true := by decide +kernel
theorem cr10 : chkRed 10 = true := by decide +kernel
theorem cr11 : chkRed 11 = true := by decide +kernel
theorem cr12 : chkRed 12 = true := by decide +kernel
theorem cr13 : chkRed 13 = true := by decide +kernel
theorem cr14 : chkRed 14 = true := by decide +kernel
theorem cr15 : chkRed 15 = true := by decide +kernel
theorem cr16 : chkRed 16 = true := by decide +kernel
theorem cr17 : chkRed 17 = true := by decide +kernel
theorem cr18 : chkRed 18 = true := by decide +kernel
theorem cr19 : chkRed 19 = true := by decide +kernel
theorem cr20 : chkRed 20 = true := by decide +kernel
theorem cr21 : chkRed 21 = true := by decide +kernel
theorem cr22 : chkRed 22 = true := by decide +kernel
theorem cr23 : chkRed 23 = true := by decide +kernel
theorem cr24 : chkRed 24 = true := by decide +kernel
theorem cr25 : chkRed 25 = true := by decide +kernel
theorem cr26 : chkRed 26 = true := by decide +kernel
theorem cr27 : chkRed 27 = true := by decide +kernel
theorem cr28 : chkRed 28 = true := by decide +kernel
theorem cr29 : chkRed 29 = true := by decide +kernel
theorem cr30 : chkRed 30 = true := by decide +kernel
theorem cr31 : chkRed 31 = true := by decide +kernel
theorem cr32 : chkRed 32 = true := by decide +kernel
theorem cr33 : chkRed 33 = true := by decide +kernel
theorem cr34 : chkRed 34 = true := by decide +kernel
theorem cr35 : chkRed 35 = true := by decide +kernel
theorem cr36 : chkRed 36 = true := by decide +kernel
theorem cr37 : chkRed 37 = true := by decide +kernel
theorem cr38 : chkRed 38 = true := by decide +kernel
theorem cr39 : chkRed 39 = true := by decide +kernel
theorem cr40 : chkRed 40 = true := by decide +kernel
theorem cr41 : chkRed 41 = true := by decide +kernel
theorem cr42 : chkRed 42 = true := by decide +kernel
theorem cr43 : chkRed 43 = true := by decide +kernel
theorem cr44 : chkRed 44 = true := by decide +kernel
theorem cr45 : chkRed 45 = true := by decide +kernel
theorem cr46 : chkRed 46 = true := by decide +kernel
theorem cr47 : chkRed 47 = true := by decide +kernel
theorem cr48 : chkRed 48 = true := by decide +kernel
theorem cr49 : chkRed 49 = true := by decide +kernel
theorem cr50 : chkRed 50 = true := by decide +kernel
theorem cr51 : chkRed 51 = true := by decide +kernel
theorem cr52 : chkRed 52 = true := by decide +kernel
theorem cr53 : chkRed 53 = true := by decide +kernel
theorem cr54 : chkRed 54 = true := by decide +kernel
theorem cr55 : chkRed 55 = true := by decide +kernel
theorem cr56 : chkRed 56 = true := by decide +kernel
theorem cr57 : chkRed 57 = true := by decide +kernel
theorem cr58 : chkRed 58 = true := by decide +kernel
theorem cr59 : chkRed 59 = true := by decide +kernel
theorem cr60 : chkRed 60 = true := by decide +kernel
theorem cr61 : chkRed 61 = true := by decide +kernel
theorem cr62 : chkRed 62 = true := by decide +kernel
theorem cr63 : chkRed 63 = true := by decide +kernel
theorem cr64 : chkRed 64 = true := by decide +kernel
theorem cr65 : chkRed 65 = true := by decide +kernel
theorem cr66 : chkRed 66 = true := by decide +kernel
theorem cr67 : chkRed 67 = true := by decide +kernel
theorem cr68 : chkRed 68 = true := by decide +kernel
theorem cr69 : chkRed 69 = true := by decide +kernel
theorem cr70 : chkRed 70 = true := by decide +kernel
theorem cr71 : chkRed 71 = true := by decide +kernel
theorem cr72 : chkRed 72 = true := by decide +kernel
theorem cr73 : chkRed 73 = true := by decide +kernel
theorem cr74 : chkRed 74 = true := by decide +kernel
theorem cr75 : chkRed 75 = true := by decide +kernel
theorem cr76 : chkRed 76 = true := by decide +kernel
theorem cr77 : chkRed 77 = true := by decide +kernel
theorem cr78 : chkRed 78 = true := by decide +kernel
theorem chkRed_all (v : Nat) (h0 : 0 < v) (hv : v < 79) : chkRed v = true :=
  match v, h0, hv with
  | 0, h, _ => absurd h (Nat.lt_irrefl 0)
  | 1, _, _ => cr1
  | 2, _, _ => cr2
  | 3, _, _ => cr3
  | 4, _, _ => cr4
  | 5, _, _ => cr5
  | 6, _, _ => cr6
  | 7, _, _ => cr7
  | 8, _, _ => cr8
  | 9, _, _ => cr9
  | 10, _, _ => cr10
  | 11, _, _ => cr11
  | 12, _, _ => cr12
  | 13, _, _ => cr13
  | 14, _, _ => cr14
  | 15, _, _ => cr15
  | 16, _, _ => cr16
  | 17, _, _ => cr17
  | 18, _, _ => cr18
  | 19, _, _ => cr19
  | 20, _, _ => cr20
  | 21, _, _ => cr21
  | 22, _, _ => cr22
  | 23, _, _ => cr23
  | 24, _, _ => cr24
  | 25, _, _ => cr25
  | 26, _, _ => cr26
  | 27, _, _ => cr27
  | 28, _, _ => cr28
  | 29, _, _ => cr29
  | 30, _, _ => cr30
  | 31, _, _ => cr31
  | 32, _, _ => cr32
  | 33, _, _ => cr33
  | 34, _, _ => cr34
  | 35, _, _ => cr35
  | 36, _, _ => cr36
  | 37, _, _ => cr37
  | 38, _, _ => cr38
  | 39, _, _ => cr39
  | 40, _, _ => cr40
  | 41, _, _ => cr41
  | 42, _, _ => cr42
  | 43, _, _ => cr43
  | 44, _, _ => cr44
  | 45, _, _ => cr45
  | 46, _, _ => cr46
  | 47, _, _ => cr47
  | 48, _, _ => cr48
  | 49, _, _ => cr49
  | 50, _, _ => cr50
  | 51, _, _ => cr51
  | 52, _, _ => cr52
  | 53, _, _ => cr53
  | 54, _, _ => cr54
  | 55, _, _ => cr55
  | 56, _, _ => cr56
  | 57, _, _ => cr57
  | 58, _, _ => cr58
  | 59, _, _ => cr59
  | 60, _, _ => cr60
  | 61, _, _ => cr61
  | 62, _, _ => cr62
  | 63, _, _ => cr63
  | 64, _, _ => cr64
  | 65, _, _ => cr65
  | 66, _, _ => cr66
  | 67, _, _ => cr67
  | 68, _, _ => cr68
  | 69, _, _ => cr69
  | 70, _, _ => cr70
  | 71, _, _ => cr71
  | 72, _, _ => cr72
  | 73, _, _ => cr73
  | 74, _, _ => cr74
  | 75, _, _ => cr75
  | 76, _, _ => cr76
  | 77, _, _ => cr77
  | 78, _, _ => cr78
  | v + 79, _, h => absurd h (by omega)

theorem cb1 : chkBlue 1 = true := by decide +kernel
theorem cb2 : chkBlue 2 = true := by decide +kernel
theorem cb3 : chkBlue 3 = true := by decide +kernel
theorem cb4 : chkBlue 4 = true := by decide +kernel
theorem cb5 : chkBlue 5 = true := by decide +kernel
theorem cb6 : chkBlue 6 = true := by decide +kernel
theorem cb7 : chkBlue 7 = true := by decide +kernel
theorem cb8 : chkBlue 8 = true := by decide +kernel
theorem cb9 : chkBlue 9 = true := by decide +kernel
theorem cb10 : chkBlue 10 = true := by decide +kernel
theorem cb11 : chkBlue 11 = true := by decide +kernel
theorem cb12 : chkBlue 12 = true := by decide +kernel
theorem cb13 : chkBlue 13 = true := by decide +kernel
theorem cb14 : chkBlue 14 = true := by decide +kernel
theorem cb15 : chkBlue 15 = true := by decide +kernel
theorem cb16 : chkBlue 16 = true := by decide +kernel
theorem cb17 : chkBlue 17 = true := by decide +kernel
theorem cb18 : chkBlue 18 = true := by decide +kernel
theorem cb19 : chkBlue 19 = true := by decide +kernel
theorem cb20 : chkBlue 20 = true := by decide +kernel
theorem cb21 : chkBlue 21 = true := by decide +kernel
theorem cb22 : chkBlue 22 = true := by decide +kernel
theorem cb23 : chkBlue 23 = true := by decide +kernel
theorem cb24 : chkBlue 24 = true := by decide +kernel
theorem cb25 : chkBlue 25 = true := by decide +kernel
theorem cb26 : chkBlue 26 = true := by decide +kernel
theorem cb27 : chkBlue 27 = true := by decide +kernel
theorem cb28 : chkBlue 28 = true := by decide +kernel
theorem cb29 : chkBlue 29 = true := by decide +kernel
theorem cb30 : chkBlue 30 = true := by decide +kernel
theorem cb31 : chkBlue 31 = true := by decide +kernel
theorem cb32 : chkBlue 32 = true := by decide +kernel
theorem cb33 : chkBlue 33 = true := by decide +kernel
theorem cb34 : chkBlue 34 = true := by decide +kernel
theorem cb35 : chkBlue 35 = true := by decide +kernel
theorem cb36 : chkBlue 36 = true := by decide +kernel
theorem cb37 : chkBlue 37 = true := by decide +kernel
theorem cb38 : chkBlue 38 = true := by decide +kernel
theorem cb39 : chkBlue 39 = true := by decide +kernel
theorem cb40 : chkBlue 40 = true := by decide +kernel
theorem cb41 : chkBlue 41 = true := by decide +kernel
theorem cb42 : chkBlue 42 = true := by decide +kernel
theorem cb43 : chkBlue 43 = true := by decide +kernel
theorem cb44 : chkBlue 44 = true := by decide +kernel
theorem cb45 : chkBlue 45 = true := by decide +kernel
theorem cb46 : chkBlue 46 = true := by decide +kernel
theorem cb47 : chkBlue 47 = true := by decide +kernel
theorem cb48 : chkBlue 48 = true := by decide +kernel
theorem cb49 : chkBlue 49 = true := by decide +kernel
theorem cb50 : chkBlue 50 = true := by decide +kernel
theorem cb51 : chkBlue 51 = true := by decide +kernel
theorem cb52 : chkBlue 52 = true := by decide +kernel
theorem cb53 : chkBlue 53 = true := by decide +kernel
theorem cb54 : chkBlue 54 = true := by decide +kernel
theorem cb55 : chkBlue 55 = true := by decide +kernel
theorem cb56 : chkBlue 56 = true := by decide +kernel
theorem cb57 : chkBlue 57 = true := by decide +kernel
theorem cb58 : chkBlue 58 = true := by decide +kernel
theorem cb59 : chkBlue 59 = true := by decide +kernel
theorem cb60 : chkBlue 60 = true := by decide +kernel
theorem cb61 : chkBlue 61 = true := by decide +kernel
theorem cb62 : chkBlue 62 = true := by decide +kernel
theorem cb63 : chkBlue 63 = true := by decide +kernel
theorem cb64 : chkBlue 64 = true := by decide +kernel
theorem cb65 : chkBlue 65 = true := by decide +kernel
theorem cb66 : chkBlue 66 = true := by decide +kernel
theorem cb67 : chkBlue 67 = true := by decide +kernel
theorem cb68 : chkBlue 68 = true := by decide +kernel
theorem cb69 : chkBlue 69 = true := by decide +kernel
theorem cb70 : chkBlue 70 = true := by decide +kernel
theorem cb71 : chkBlue 71 = true := by decide +kernel
theorem cb72 : chkBlue 72 = true := by decide +kernel
theorem cb73 : chkBlue 73 = true := by decide +kernel
theorem cb74 : chkBlue 74 = true := by decide +kernel
theorem cb75 : chkBlue 75 = true := by decide +kernel
theorem cb76 : chkBlue 76 = true := by decide +kernel
theorem cb77 : chkBlue 77 = true := by decide +kernel
theorem cb78 : chkBlue 78 = true := by decide +kernel
theorem chkBlue_all (v : Nat) (h0 : 0 < v) (hv : v < 79) : chkBlue v = true :=
  match v, h0, hv with
  | 0, h, _ => absurd h (Nat.lt_irrefl 0)
  | 1, _, _ => cb1
  | 2, _, _ => cb2
  | 3, _, _ => cb3
  | 4, _, _ => cb4
  | 5, _, _ => cb5
  | 6, _, _ => cb6
  | 7, _, _ => cb7
  | 8, _, _ => cb8
  | 9, _, _ => cb9
  | 10, _, _ => cb10
  | 11, _, _ => cb11
  | 12, _, _ => cb12
  | 13, _, _ => cb13
  | 14, _, _ => cb14
  | 15, _, _ => cb15
  | 16, _, _ => cb16
  | 17, _, _ => cb17
  | 18, _, _ => cb18
  | 19, _, _ => cb19
  | 20, _, _ => cb20
  | 21, _, _ => cb21
  | 22, _, _ => cb22
  | 23, _, _ => cb23
  | 24, _, _ => cb24
  | 25, _, _ => cb25
  | 26, _, _ => cb26
  | 27, _, _ => cb27
  | 28, _, _ => cb28
  | 29, _, _ => cb29
  | 30, _, _ => cb30
  | 31, _, _ => cb31
  | 32, _, _ => cb32
  | 33, _, _ => cb33
  | 34, _, _ => cb34
  | 35, _, _ => cb35
  | 36, _, _ => cb36
  | 37, _, _ => cb37
  | 38, _, _ => cb38
  | 39, _, _ => cb39
  | 40, _, _ => cb40
  | 41, _, _ => cb41
  | 42, _, _ => cb42
  | 43, _, _ => cb43
  | 44, _, _ => cb44
  | 45, _, _ => cb45
  | 46, _, _ => cb46
  | 47, _, _ => cb47
  | 48, _, _ => cb48
  | 49, _, _ => cb49
  | 50, _, _ => cb50
  | 51, _, _ => cb51
  | 52, _, _ => cb52
  | 53, _, _ => cb53
  | 54, _, _ => cb54
  | 55, _, _ => cb55
  | 56, _, _ => cb56
  | 57, _, _ => cb57
  | 58, _, _ => cb58
  | 59, _, _ => cb59
  | 60, _, _ => cb60
  | 61, _, _ => cb61
  | 62, _, _ => cb62
  | 63, _, _ => cb63
  | 64, _, _ => cb64
  | 65, _, _ => cb65
  | 66, _, _ => cb66
  | 67, _, _ => cb67
  | 68, _, _ => cb68
  | 69, _, _ => cb69
  | 70, _, _ => cb70
  | 71, _, _ => cb71
  | 72, _, _ => cb72
  | 73, _, _ => cb73
  | 74, _, _ => cb74
  | 75, _, _ => cb75
  | 76, _, _ => cb76
  | 77, _, _ => cb77
  | 78, _, _ => cb78
  | v + 79, _, h => absurd h (by omega)


theorem noRed0 (x1 x2 x3 x4 : Nat) (h1 : 0 < x1) (h2 : x1 < x2) (h3 : x2 < x3) (h4 : x3 < x4) (hn : x4 < 79)
    (r0 : col 0 x1 x2 x3 = true) (r1 : col 0 x1 x2 x4 = true) (r2 : col 0 x1 x3 x4 = true) (r3 : col 0 x2 x3 x4 = true) (r4 : col x1 x2 x3 x4 = true) : False := by
  have h := chkRed_all x1 (by omega) (by omega)
  unfold chkRed at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
  rcases h x2 (by omega) with h | h
  · omega
  rcases h x3 (by omega) with h | h
  · simp_all
  rcases h x4 (by omega) with h | h
  all_goals simp_all

theorem noBlue0 (x1 x2 x3 x4 x5 : Nat) (h1 : 0 < x1) (h2 : x1 < x2) (h3 : x2 < x3) (h4 : x3 < x4) (h5 : x4 < x5) (hn : x5 < 79)
    (r0 : col 0 x1 x2 x3 = false) (r1 : col 0 x1 x2 x4 = false) (r2 : col 0 x1 x2 x5 = false) (r3 : col 0 x1 x3 x4 = false) (r4 : col 0 x1 x3 x5 = false) (r5 : col 0 x1 x4 x5 = false) (r6 : col 0 x2 x3 x4 = false) (r7 : col 0 x2 x3 x5 = false) (r8 : col 0 x2 x4 x5 = false) (r9 : col 0 x3 x4 x5 = false) (r10 : col x1 x2 x3 x4 = false) (r11 : col x1 x2 x3 x5 = false) (r12 : col x1 x2 x4 x5 = false) (r13 : col x1 x3 x4 x5 = false) (r14 : col x2 x3 x4 x5 = false) : False := by
  have h := chkBlue_all x1 (by omega) (by omega)
  unfold chkBlue at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
  rcases h x2 (by omega) with h | h
  · omega
  rcases h x3 (by omega) with h | h
  · simp_all
  rcases h x4 (by omega) with h | h
  · simp_all
  rcases h x5 (by omega) with h | h
  all_goals simp_all

/-- translation: the colour of `x<y<z<w` only depends on the differences to `x` -/
theorem col_shift (a x y z w : Nat) (hx : a ≤ x) (hxy : x < y) (hyz : y < z) (hzw : z < w) :
    col (x - a) (y - a) (z - a) (w - a) = col x y z w := by
  unfold col
  rw [show y - a - (x - a) = y - x by omega, show z - a - (x - a) = z - x by omega,
    show w - a - (x - a) = w - x by omega]

/-- `col` (a colouring of the 4-sets `x<y<z<w` of `{0,…,N-1}`) contains a `K_5^(4)` of colour `χ`. -/
def HasMonoK5 (N : Nat) (col : Nat → Nat → Nat → Nat → Bool) (χ : Bool) : Prop :=
  ∃ a b c d e : Nat, a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < N ∧ col a b c d = χ ∧ col a b c e = χ ∧ col a b d e = χ ∧ col a c d e = χ ∧ col b c d e = χ
/-- `col` (a colouring of the 4-sets `x<y<z<w` of `{0,…,N-1}`) contains a `K_6^(4)` of colour `χ`. -/
def HasMonoK6 (N : Nat) (col : Nat → Nat → Nat → Nat → Bool) (χ : Bool) : Prop :=
  ∃ a b c d e f : Nat, a < b ∧ b < c ∧ c < d ∧ d < e ∧ e < f ∧ f < N ∧ col a b c d = χ ∧ col a b c e = χ ∧ col a b c f = χ ∧ col a b d e = χ ∧ col a b d f = χ ∧ col a b e f = χ ∧ col a c d e = χ ∧ col a c d f = χ ∧ col a c e f = χ ∧ col a d e f = χ ∧ col b c d e = χ ∧ col b c d f = χ ∧ col b c e f = χ ∧ col b d e f = χ ∧ col c d e f = χ

theorem noRedK : ¬ HasMonoK5 79 col true := by
  rintro ⟨a, b, c, d, e, l0, l1, l2, l3, hn, h0, h1, h2, h3, h4⟩
  have s0 := col_shift a a b c d (by omega) (by omega) (by omega) (by omega)
  have s1 := col_shift a a b c e (by omega) (by omega) (by omega) (by omega)
  have s2 := col_shift a a b d e (by omega) (by omega) (by omega) (by omega)
  have s3 := col_shift a a c d e (by omega) (by omega) (by omega) (by omega)
  have s4 := col_shift a b c d e (by omega) (by omega) (by omega) (by omega)
  simp only [Nat.sub_self] at s0 s1 s2 s3 s4
  exact noRed0 (b - a) (c - a) (d - a) (e - a) (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [s0, h0]) (by rw [s1, h1]) (by rw [s2, h2]) (by rw [s3, h3]) (by rw [s4, h4])

theorem noBlueK : ¬ HasMonoK6 79 col false := by
  rintro ⟨a, b, c, d, e, f, l0, l1, l2, l3, l4, hn, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
  have s0 := col_shift a a b c d (by omega) (by omega) (by omega) (by omega)
  have s1 := col_shift a a b c e (by omega) (by omega) (by omega) (by omega)
  have s2 := col_shift a a b c f (by omega) (by omega) (by omega) (by omega)
  have s3 := col_shift a a b d e (by omega) (by omega) (by omega) (by omega)
  have s4 := col_shift a a b d f (by omega) (by omega) (by omega) (by omega)
  have s5 := col_shift a a b e f (by omega) (by omega) (by omega) (by omega)
  have s6 := col_shift a a c d e (by omega) (by omega) (by omega) (by omega)
  have s7 := col_shift a a c d f (by omega) (by omega) (by omega) (by omega)
  have s8 := col_shift a a c e f (by omega) (by omega) (by omega) (by omega)
  have s9 := col_shift a a d e f (by omega) (by omega) (by omega) (by omega)
  have s10 := col_shift a b c d e (by omega) (by omega) (by omega) (by omega)
  have s11 := col_shift a b c d f (by omega) (by omega) (by omega) (by omega)
  have s12 := col_shift a b c e f (by omega) (by omega) (by omega) (by omega)
  have s13 := col_shift a b d e f (by omega) (by omega) (by omega) (by omega)
  have s14 := col_shift a c d e f (by omega) (by omega) (by omega) (by omega)
  simp only [Nat.sub_self] at s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14
  exact noBlue0 (b - a) (c - a) (d - a) (e - a) (f - a) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [s0, h0]) (by rw [s1, h1]) (by rw [s2, h2]) (by rw [s3, h3]) (by rw [s4, h4]) (by rw [s5, h5]) (by rw [s6, h6]) (by rw [s7, h7]) (by rw [s8, h8]) (by rw [s9, h9]) (by rw [s10, h10]) (by rw [s11, h11]) (by rw [s12, h12]) (by rw [s13, h13]) (by rw [s14, h14])

/-- **R(5,6;4) ≥ 80**: a red/blue colouring of the 4-subsets of `{0,…,78}` with no red
`K_5^(4)` and no blue `K_6^(4)`. -/
theorem main : ∃ col : Nat → Nat → Nat → Nat → Bool, ¬ HasMonoK5 79 col true ∧ ¬ HasMonoK6 79 col false :=
  ⟨col, noRedK, noBlueK⟩

end R564

#print axioms R564.main

