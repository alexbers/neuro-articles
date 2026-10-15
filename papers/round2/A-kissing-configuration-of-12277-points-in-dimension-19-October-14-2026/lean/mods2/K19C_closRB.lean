import K19Defs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K19
theorem c_closRB : (rootBlocks.all (fun b => grpM.all (fun gm => b.2.all (fun t => b.2.contains (signF gm b.1.1 * t.1, signF gm b.1.2 * t.2))))) = true := by decide +kernel
end K19
