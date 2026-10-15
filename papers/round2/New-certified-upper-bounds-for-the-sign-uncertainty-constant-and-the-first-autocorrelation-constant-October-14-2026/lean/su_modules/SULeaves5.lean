import SUCore

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace SU
open PolyPos

theorem hleaf30 : leaves30.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf31 : leaves31.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf32 : leaves32.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf33 : leaves33.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf34 : leaves34.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

theorem hleaf35 : leaves35.all (fun l => leafOK 16623 20 Pl l.1 l.2.1 l.2.2.1 l.2.2.2) = true := by decide +kernel

end SU
