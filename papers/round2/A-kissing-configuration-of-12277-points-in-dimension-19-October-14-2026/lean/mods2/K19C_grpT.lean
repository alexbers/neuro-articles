import K19Defs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K19
theorem c_grpT : (grpM.all (fun gm => decide (gm &&& 329 = 0))) = true := by decide +kernel
end K19
