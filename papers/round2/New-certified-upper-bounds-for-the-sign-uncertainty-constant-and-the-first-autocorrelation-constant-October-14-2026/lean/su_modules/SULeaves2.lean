import SUCore

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace SU
open PolyPos

theorem hleaf12 : leaves12.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf13 : leaves13.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf14 : leaves14.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf15 : leaves15.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf16 : leaves16.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf17 : leaves17.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

end SU
