import K19Defs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K19
theorem c_replen : (reps.all (fun r => decide (r.length = 20) && decide (0 < dot r r) && decide (tsumT r = 0))) = true := by decide +kernel
end K19
