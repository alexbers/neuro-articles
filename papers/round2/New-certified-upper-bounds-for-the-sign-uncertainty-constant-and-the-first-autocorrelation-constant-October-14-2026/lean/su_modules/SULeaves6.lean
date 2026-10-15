import SUCore

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace SU
open PolyPos

theorem hleaf36 : leaves36.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf37 : leaves37.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf38 : leaves38.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf39 : leaves39.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf40 : leaves40.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

end SU
