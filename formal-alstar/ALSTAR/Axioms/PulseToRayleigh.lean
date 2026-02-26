import ALSTAR.Specs.PulseBridgeSpec

namespace ALSTAR

theorem pulse_logbound_implies_lambdaMin_zero
  {α : Type u}
  (A : Schema α)
  (H : PulseBridgeHyp A)
  (hPulse : Pulse A) :
  lambdaMin A = 0 :=
by
  exact H.pulse_to_lambdaMin_zero hPulse

end ALSTAR
