import ALSTAR.Specs.PulseBridgeSpec

namespace ALSTAR

theorem pulse_logbound_implies_noncoercive_target_bridge
  {α : Type u}
  (A : Schema α)
  (H : PulseBridgeHyp A)
  (hPulse : Pulse A) :
  NonCoercive A :=
by
  exact H.pulse_to_noncoercive hPulse

end ALSTAR
