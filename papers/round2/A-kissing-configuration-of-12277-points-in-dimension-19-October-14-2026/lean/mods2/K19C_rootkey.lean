import K19Defs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K19
theorem c_rootkey : strictInc (rootData.map keyR) = true := by decide +kernel
end K19
