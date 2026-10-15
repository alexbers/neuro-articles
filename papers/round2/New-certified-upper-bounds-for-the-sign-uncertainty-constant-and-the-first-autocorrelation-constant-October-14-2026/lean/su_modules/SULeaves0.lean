import SUCore

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace SU
open PolyPos

theorem hleaf0 : leaves0.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf1 : leaves1.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf2 : leaves2.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf3 : leaves3.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf4 : leaves4.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf5 : leaves5.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

end SU
