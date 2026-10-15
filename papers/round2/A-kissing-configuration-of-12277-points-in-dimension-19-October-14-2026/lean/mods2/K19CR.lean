import K19Defs
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace K19
theorem c_rr0 : (rootB0.flatMap rootOf).all rrB = true := by decide +kernel
theorem c_rr1 : (rootB1.flatMap rootOf).all rrB = true := by decide +kernel
theorem c_rr2 : (rootB2.flatMap rootOf).all rrB = true := by decide +kernel
theorem c_rr3 : (rootB3.flatMap rootOf).all rrB = true := by decide +kernel
theorem c_rr4 : (rootB4.flatMap rootOf).all rrB = true := by decide +kernel
theorem c_rr5 : (rootB5.flatMap rootOf).all rrB = true := by decide +kernel
end K19
