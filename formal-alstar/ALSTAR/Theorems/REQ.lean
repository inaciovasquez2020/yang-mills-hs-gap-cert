import Mathlib.Data.Real.Basic
import ALSTAR.Specs.PulseBridgeSpec
import ALSTAR.Theorems.TwoBubbleLowerBound
universe u
namespace ALSTAR
axiom ReflectionPositive {α : Type u} (A : Schema α) : Prop
axiom SelfAdjoint {α : Type u} (A : Schema α) : Prop
axiom GapOnPhys {α : Type u} (A : Schema α) : Prop
axiom BubblePackingLinear
{α : Type u} {A : Schema α} :
ReflectionPositive A →
SelfAdjoint A →
GapOnPhys A →
TwoBubbleLowerBound A
theorem REQ
{α : Type u} {A : Schema α} :
ReflectionPositive A →
SelfAdjoint A →
GapOnPhys A →
TwoBubbleLowerBound A :=
by
intro hRP hSA hG
exact BubblePackingLinear (A := A) hRP hSA hG
theorem Pulse_to_not_logBound_via_REQ
{α : Type u} (A : Schema α)
(hPulse : Pulse A)
(hRP : ReflectionPositive A)
(hSA : SelfAdjoint A)
(hG : GapOnPhys A)
(hPulse_to_REQ : Pulse A → (ReflectionPositive A ∧ SelfAdjoint A ∧ GapOnPhys A)) :
¬ logBound A :=
by
have hTrip : ReflectionPositive A ∧ SelfAdjoint A ∧ GapOnPhys A := hPulse_to_REQ hPulse
have hTB : TwoBubbleLowerBound A := REQ (A := A) hTrip.1 hTrip.2.1 hTrip.2.2
exact twoBubble_excludes_logBound (A := A) hTB
end ALSTAR
