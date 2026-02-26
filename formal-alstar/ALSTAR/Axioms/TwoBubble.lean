import ALSTAR.Specs.PulseBridgeSpec

namespace ALSTAR

theorem two_bubble_log_locality_incompatible
  {α : Type u}
  (A : Schema α)
  (H : PulseBridgeHyp A)
  (hBounded : logBound A) :
  False :=
by
  exact H.twoBubble hBounded

end ALSTAR
