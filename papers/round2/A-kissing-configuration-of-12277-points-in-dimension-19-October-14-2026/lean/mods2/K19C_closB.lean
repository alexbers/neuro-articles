import K19Defs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K19
def closF (b : Nat × List Nat) : Bool := grpM.all (fun gm => b.2.all (fun m => b.2.contains (m ^^^ (gm &&& b.1))))
theorem all_of_take_drop {α : Type} (f : α → Bool) (l : List α) (n : Nat) (h1 : (l.take n).all f = true)
    (h2 : (l.drop n).all f = true) : l.all f = true := by
  rw [← List.take_append_drop n l, List.all_append]; simp [h1, h2]
theorem cb0 : ((octBlocks.drop 0).take 8).all closF = true := by decide +kernel
theorem cb1 : ((octBlocks.drop 8).take 8).all closF = true := by decide +kernel
theorem cb2 : ((octBlocks.drop 16).take 8).all closF = true := by decide +kernel
theorem cb3 : ((octBlocks.drop 24).take 8).all closF = true := by decide +kernel
theorem cb4 : ((octBlocks.drop 32).take 8).all closF = true := by decide +kernel
theorem cb5 : ((octBlocks.drop 40).take 8).all closF = true := by decide +kernel
theorem cb6 : ((octBlocks.drop 48).take 8).all closF = true := by decide +kernel
theorem cb7 : ((octBlocks.drop 56).take 8).all closF = true := by decide +kernel
theorem cb8 : ((octBlocks.drop 64).take 8).all closF = true := by decide +kernel
theorem cb9 : ((octBlocks.drop 72).take 8).all closF = true := by decide +kernel
theorem cb10 : ((octBlocks.drop 80).take 8).all closF = true := by decide +kernel
theorem cb11 : ((octBlocks.drop 88).take 8).all closF = true := by decide +kernel
theorem cb12 : ((octBlocks.drop 96).take 8).all closF = true := by decide +kernel
theorem cb13 : ((octBlocks.drop 104).take 8).all closF = true := by decide +kernel
theorem cb14 : ((octBlocks.drop 112).take 8).all closF = true := by decide +kernel
theorem cb15 : ((octBlocks.drop 120).take 8).all closF = true := by decide +kernel
theorem cbT : (octBlocks.drop 128).all closF = true := by decide +kernel
theorem cd15 : (octBlocks.drop 120).all closF = true :=
  all_of_take_drop closF _ 8 cb15 (by simpa [List.drop_drop] using cbT)
theorem cd14 : (octBlocks.drop 112).all closF = true :=
  all_of_take_drop closF _ 8 cb14 (by simpa [List.drop_drop] using cd15)
theorem cd13 : (octBlocks.drop 104).all closF = true :=
  all_of_take_drop closF _ 8 cb13 (by simpa [List.drop_drop] using cd14)
theorem cd12 : (octBlocks.drop 96).all closF = true :=
  all_of_take_drop closF _ 8 cb12 (by simpa [List.drop_drop] using cd13)
theorem cd11 : (octBlocks.drop 88).all closF = true :=
  all_of_take_drop closF _ 8 cb11 (by simpa [List.drop_drop] using cd12)
theorem cd10 : (octBlocks.drop 80).all closF = true :=
  all_of_take_drop closF _ 8 cb10 (by simpa [List.drop_drop] using cd11)
theorem cd9 : (octBlocks.drop 72).all closF = true :=
  all_of_take_drop closF _ 8 cb9 (by simpa [List.drop_drop] using cd10)
theorem cd8 : (octBlocks.drop 64).all closF = true :=
  all_of_take_drop closF _ 8 cb8 (by simpa [List.drop_drop] using cd9)
theorem cd7 : (octBlocks.drop 56).all closF = true :=
  all_of_take_drop closF _ 8 cb7 (by simpa [List.drop_drop] using cd8)
theorem cd6 : (octBlocks.drop 48).all closF = true :=
  all_of_take_drop closF _ 8 cb6 (by simpa [List.drop_drop] using cd7)
theorem cd5 : (octBlocks.drop 40).all closF = true :=
  all_of_take_drop closF _ 8 cb5 (by simpa [List.drop_drop] using cd6)
theorem cd4 : (octBlocks.drop 32).all closF = true :=
  all_of_take_drop closF _ 8 cb4 (by simpa [List.drop_drop] using cd5)
theorem cd3 : (octBlocks.drop 24).all closF = true :=
  all_of_take_drop closF _ 8 cb3 (by simpa [List.drop_drop] using cd4)
theorem cd2 : (octBlocks.drop 16).all closF = true :=
  all_of_take_drop closF _ 8 cb2 (by simpa [List.drop_drop] using cd3)
theorem cd1 : (octBlocks.drop 8).all closF = true :=
  all_of_take_drop closF _ 8 cb1 (by simpa [List.drop_drop] using cd2)
theorem cd0 : (octBlocks.drop 0).all closF = true :=
  all_of_take_drop closF _ 8 cb0 (by simpa [List.drop_drop] using cd1)
theorem c_closB : (octBlocks.all (fun b => grpM.all (fun gm => b.2.all (fun m => b.2.contains (m ^^^ (gm &&& b.1)))))) = true := by
  have h := cd0; simpa [closF] using h
end K19
