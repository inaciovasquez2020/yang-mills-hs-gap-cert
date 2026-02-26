import ALSTAR.Specs.PulseBridgeSpec

namespace ALSTAR

open Nat

theorem dichotomy_applies_two_bubble
  {α : Type u}
  (A : Schema α)
  (H : PulseBridgeHyp A)
  (hBounded : ∀ n : Nat, A.R n ≤ log₂ n) :
  False :=
by
  exact H.twoBubble hBounded

end ALSTAR
