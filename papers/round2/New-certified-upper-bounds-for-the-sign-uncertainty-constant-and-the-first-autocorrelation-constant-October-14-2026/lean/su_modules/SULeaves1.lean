import SUCore

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace SU
open PolyPos

theorem hleaf6 : leaves6.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf7 : leaves7.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf8 : leaves8.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf9 : leaves9.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf10 : leaves10.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf11 : leaves11.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

end SU
