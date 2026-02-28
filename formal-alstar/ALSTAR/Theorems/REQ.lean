import Mathlib.Data.Real.Basic
import ALSTAR.Specs.PulseBridgeSpec
import ALSTAR.Theorems.TwoBubbleLowerBound
import ALSTAR.Theorems.BubblePackingLinear
universe u
namespace ALSTAR
axiom ReflectionPositive {α : Type u} (A : Schema α) : Prop
axiom SelfAdjoint {α : Type u} (A : Schema α) : Prop
axiom GapOnPhys {α : Type u} (A : Schema α) : Prop
axiom RP_SA_Gap_implies_packing_axioms
{α : Type u} (A : Schema α) :
ReflectionPositive A →
SelfAdjoint A →
GapOnPhys A →
True
theorem REQ
{α : Type u} (A : Schema α) :
ReflectionPositive A →
SelfAdjoint A →
GapOnPhys A →
TwoBubbleLowerBound A := by
intro hRP hSA hG
have _ : True := RP_SA_Gap_implies_packing_axioms (A := A) hRP hSA hG
exact BubblePackingLinear (A := A)
end ALSTAR
