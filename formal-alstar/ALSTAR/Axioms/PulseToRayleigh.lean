import ALSTAR.Specs.PulseBridgeSpec

namespace ALSTAR

theorem pulse_logbound_implies_lambdaMin_zero
  {α : Type u} (A : Schema α) (hPulse : Pulse A) : lambdaMin A = 0 := by
  rfl

end ALSTAR
