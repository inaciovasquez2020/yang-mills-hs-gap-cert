import ALSTAR.Axioms.Basic
import ALSTAR.Axioms.Coercivity

namespace ALSTAR

/--
Two-bubble obstruction theorem target (axiomatized for now):
log-local growth bound forces failure of coercivity.
-/
axiom two_bubble_log_locality_incompatible
  {α : Type u}
  (A : Schema α)
  (hR : LogBound A) :
  TwoBubbleObstructed A

end ALSTAR
