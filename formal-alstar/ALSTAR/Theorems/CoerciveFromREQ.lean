import Mathlib.Data.Real.Basic
import ALSTAR.Specs.PulseBridgeSpec
import ALSTAR.Theorems.Dichotomy
import ALSTAR.Theorems.REQ
universe u
namespace ALSTAR
axiom NonCoercive {α : Type u} (A : Schema α) : Prop
axiom Coercive {α : Type u} (A : Schema α) : Prop
axiom TwoBubble_implies_NonCoercive
{α : Type u} (A : Schema α) :
TwoBubbleLowerBound A →
NonCoercive A
axiom NonCoercive_contra_Coercive
{α : Type u} (A : Schema α) :
NonCoercive A →
¬ Coercive A
theorem Coercive_from_REQ
{α : Type u} (A : Schema α) :
ReflectionPositive A →
SelfAdjoint A →
GapOnPhys A →
¬ Coercive A := by
intro hRP hSA hG
have h2 : TwoBubbleLowerBound A := REQ (A := A) hRP hSA hG
have hNC : NonCoercive A := TwoBubble_implies_NonCoercive (A := A) h2
exact NonCoercive_contra_Coercive (A := A) hNC
end ALSTAR
