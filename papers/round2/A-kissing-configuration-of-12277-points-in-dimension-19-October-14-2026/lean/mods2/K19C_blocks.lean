import K19Defs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K19
theorem c_blocks : (octBlocks.all (fun b => decide (cnt 20 b.1 = 8) && b.2.all (fun m => decide (cnt 20 (b.1 &&& m) % 2 = 1) && decide (m &&& b.1 = m) && decide (m < 2 ^ 20) && decide (octF b.1 m 0 + octF b.1 m 3 + octF b.1 m 6 + octF b.1 m 8 = 0)))) = true := by decide +kernel
end K19
