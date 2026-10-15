import K19C_blocks
import K19C_octads
import K19C_octkey
import K19C_rootkey
import K19C_root
import K19C_closB
import K19C_closRB
import K19C_grp
import K19C_grpkey
import K19C_grpT
import K19C_repkey
import K19C_replen
import K19C_len
import K19CR
import K19Chk00
import K19Chk01
import K19Chk02
import K19Chk03
import K19Chk04
import K19Chk05
import K19Chk06
import K19Chk07
import K19Chk08
import K19Chk09
import K19Chk10
import K19Chk11
import K19Chk12
import K19Chk13
import K19Chk14
import K19Chk15
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K19
theorem all_k3 : reps.all k3B = true := by simp only [reps, List.all_cons, List.all_nil, k3_0, k3_1, k3_2, k3_3, k3_4, k3_5, k3_6, k3_7, k3_8, k3_9, k3_10, k3_11, k3_12, k3_13, k3_14, k3_15, k3_16, k3_17, k3_18, k3_19, k3_20, k3_21, k3_22, k3_23, k3_24, k3_25, k3_26, k3_27, k3_28, k3_29, k3_30, k3_31, k3_32, k3_33, k3_34, k3_35, k3_36, k3_37, k3_38, k3_39, k3_40, k3_41, k3_42, k3_43, k3_44, k3_45, k3_46, k3_47, k3_48, k3_49, k3_50, k3_51, k3_52, k3_53, k3_54, k3_55, k3_56, k3_57, k3_58, k3_59, k3_60, k3_61, k3_62, k3_63, k3_64, k3_65, k3_66, k3_67, k3_68, k3_69, k3_70, k3_71, k3_72, k3_73, k3_74, k3_75, k3_76, k3_77, k3_78, k3_79, k3_80, k3_81, k3_82, k3_83, k3_84, k3_85, k3_86, k3_87, k3_88, k3_89, k3_90, k3_91, k3_92, k3_93, k3_94, k3_95, k3_96, k3_97, k3_98, k3_99, k3_100, k3_101, k3_102, k3_103, k3_104, k3_105, k3_106, k3_107, k3_108, k3_109, k3_110, k3_111, Bool.and_true]
theorem all_k4 : reps.all k4B = true := by simp only [reps, List.all_cons, List.all_nil, k4_0, k4_1, k4_2, k4_3, k4_4, k4_5, k4_6, k4_7, k4_8, k4_9, k4_10, k4_11, k4_12, k4_13, k4_14, k4_15, k4_16, k4_17, k4_18, k4_19, k4_20, k4_21, k4_22, k4_23, k4_24, k4_25, k4_26, k4_27, k4_28, k4_29, k4_30, k4_31, k4_32, k4_33, k4_34, k4_35, k4_36, k4_37, k4_38, k4_39, k4_40, k4_41, k4_42, k4_43, k4_44, k4_45, k4_46, k4_47, k4_48, k4_49, k4_50, k4_51, k4_52, k4_53, k4_54, k4_55, k4_56, k4_57, k4_58, k4_59, k4_60, k4_61, k4_62, k4_63, k4_64, k4_65, k4_66, k4_67, k4_68, k4_69, k4_70, k4_71, k4_72, k4_73, k4_74, k4_75, k4_76, k4_77, k4_78, k4_79, k4_80, k4_81, k4_82, k4_83, k4_84, k4_85, k4_86, k4_87, k4_88, k4_89, k4_90, k4_91, k4_92, k4_93, k4_94, k4_95, k4_96, k4_97, k4_98, k4_99, k4_100, k4_101, k4_102, k4_103, k4_104, k4_105, k4_106, k4_107, k4_108, k4_109, k4_110, k4_111, Bool.and_true]
theorem all_rr : rootData.all rrB = true := by
  simp only [rootData, rootBlocks, List.flatMap_append, List.all_append, c_rr0, c_rr1, c_rr2, c_rr3, c_rr4, c_rr5, Bool.and_true]

/-- **Main theorem.** There are 12277 pairwise distinct integer vectors in ℤ²⁰, all nonzero and all in the
hyperplane `x₀ + x₃ + x₆ + x₈ = 0`, any two of which make an angle of at least 60°
(`Compat x y` ⇔ `⟨x,y⟩ ≤ 0 ∨ 4⟨x,y⟩² ≤ ⟨x,x⟩⟨y,y⟩`).  The hyperplane is a 19-dimensional real space,
so normalising gives a kissing configuration in ℝ¹⁹ and τ₁₉ ≥ 12277. -/
theorem kissing19 : ∃ L : List (List Int), L.length = 12277 ∧ L.Nodup ∧
    (∀ v ∈ L, v.length = 20 ∧ tsumT v = 0 ∧ 0 < dot v v) ∧ L.Pairwise Compat := by
  apply final_generic octBlocks rootData reps grpM 12277
  · intro b hb; have := List.all_eq_true.1 c_blocks b hb
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at this
    exact ⟨this.1, fun m hm => ⟨(this.2 m hm).1.1.1, (this.2 m hm).1.1.2, (this.2 m hm).1.2, (this.2 m hm).2⟩⟩
  · intro o ho o2 ho2 hne; have := List.all_eq_true.1 (List.all_eq_true.1 c_octads o ho) o2 ho2
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this; rcases this with h | h
    · exact absurd h hne
    · exact h
  · exact c_octkey
  · exact c_rootkey
  · intro r hr; have := List.all_eq_true.1 c_root r hr
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1.1.1.1, this.1.1.1.1.2, this.1.1.1.2, this.1.1.2, this.1.2, this.2⟩
  · intro r hr r2 hr2; have := List.all_eq_true.1 (List.all_eq_true.1 all_rr r hr) r2 hr2
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this; exact this
  · intro b hb gm hg m hm
    have := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 c_closB b hb) gm hg) m hm
    simpa [List.contains_iff_mem] using this
  · intro gm hg r hr
    simp only [rootData, List.mem_flatMap, rootOf, List.mem_map] at hr ⊢
    obtain ⟨b, hb, t, ht, rfl⟩ := hr
    have := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 c_closRB b hb) gm hg) t ht
    refine ⟨b, hb, (signF gm b.1.1 * t.1, signF gm b.1.2 * t.2), by simpa [List.contains_iff_mem] using this, ?_⟩
    rfl
  · intro a ha b hb; have := List.all_eq_true.1 (List.all_eq_true.1 c_grp a ha) b hb
    simpa [List.contains_iff_mem] using this
  · exact c_grpkey
  · intro gm hg; have := List.all_eq_true.1 c_grpT gm hg; simpa using this
  · exact nodup_of_strictInc_map encV reps c_repkey
  · intro r hr; have := List.all_eq_true.1 c_replen r hr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact ⟨this.1.1, this.1.2, this.2⟩
  · intro r hr; have := List.all_eq_true.1 all_k3 r hr
    simp only [k3B, okD, Bool.and_eq_true, List.all_eq_true] at this
    exact ⟨fun b hb m hm => this.1 b hb m hm, fun q hq => this.2 q hq⟩
  · intro r hr r2 hr2 gm hg; have := List.all_eq_true.1 (List.all_eq_true.1 (List.all_eq_true.1 all_k4 r hr) r2 hr2) gm hg
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this; exact this
  · exact c_len

end K19

#print axioms K19.kissing19
