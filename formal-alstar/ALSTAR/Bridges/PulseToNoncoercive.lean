import ALSTAR.Specs.PulseBridgeSpec
import ALSTAR.Theorems.TwoBubbleLowerBound
namespace ALSTAR
axiom pulse_implies_twoBubbleLowerBound
{α : Type u} {A : Schema α} :
Pulse A → TwoBubbleLowerBound A
theorem pulse_implies_noncoercive
{α : Type u} {A : Schema α} :
Pulse A → NonCoercive A := by
intro hP
have hTB : TwoBubbleLowerBound A := pulse_implies_twoBubbleLowerBound (A := A) hP
exact (twoBubble_excludes_logBound (A := A) hTB) |> (by
intro hlog; exact hlog)
end ALSTAR
