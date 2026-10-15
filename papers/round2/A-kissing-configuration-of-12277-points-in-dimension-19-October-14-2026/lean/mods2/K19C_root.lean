import K19Defs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K19
theorem c_root : (rootData.all (fun r => decide (r.1 < 20) && decide (r.2.1 < 20) && decide (r.1 ≠ r.2.1) && (decide (r.2.2.1 = 2) || decide (r.2.2.1 = -2)) && (decide (r.2.2.2 = 2) || decide (r.2.2.2 = -2)) && decide (rootF r.1 r.2.1 r.2.2.1 r.2.2.2 0 + rootF r.1 r.2.1 r.2.2.1 r.2.2.2 3 + rootF r.1 r.2.1 r.2.2.1 r.2.2.2 6 + rootF r.1 r.2.1 r.2.2.1 r.2.2.2 8 = 0))) = true := by decide +kernel
end K19
