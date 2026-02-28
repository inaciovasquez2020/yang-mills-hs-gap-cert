import ALSTAR.Specs.PulseBridgeSpec
import ALSTAR.Theorems.TwoBubbleLowerBound

universe u

namespace ALSTAR

theorem pulse_implies_not_logBound
  {α : Type u}
  (A : Schema α)
  (hPulse : Pulse A)
  (hTB : Pulse A → TwoBubbleLowerBound A) :
  ¬ logBound A := by
  have h2 : TwoBubbleLowerBound A := hTB hPulse
  exact twoBubble_excludes_logBound (A := A) h2

end ALSTAR
