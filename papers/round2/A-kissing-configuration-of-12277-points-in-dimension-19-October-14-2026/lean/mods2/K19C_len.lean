import K19Defs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K19
theorem c_len : (rootData.map rootV ++ (octBlocks.flatMap (fun b => b.2.map (fun m => (b.1, m)))).map octV ++ grpM.flatMap (fun gm => reps.map (sgn (vecOf (signF gm))))).length = 12277 := by decide +kernel
end K19
