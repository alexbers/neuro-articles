import K19Defs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K19
theorem c_grp : (grpM.all (fun a => grpM.all (fun b => grpM.contains (a ^^^ b)))) = true := by decide +kernel
end K19
