import K19Defs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K19
theorem c_octkey : strictInc ((octBlocks.flatMap (fun b => b.2.map (fun m => (b.1, m)))).map keyO') = true := by decide +kernel
end K19
