import K19Defs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K19
theorem c_octads : ((octBlocks.map (·.1)).all (fun o => (octBlocks.map (·.1)).all (fun o2 => decide (o = o2) || decide (cnt 20 (o &&& o2) ≤ 4)))) = true := by decide +kernel
end K19
