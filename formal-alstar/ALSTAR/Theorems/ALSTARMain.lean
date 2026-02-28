import Mathlib.Data.Real.Basic
import ALSTAR.Specs.PulseBridgeSpec
import ALSTAR.Theorems.REQ
import ALSTAR.Theorems.CoerciveFromREQ

universe u

namespace ALSTAR

theorem ALSTAR_Main
{α : Type u} (A : Schema α) :
ReflectionPositive A →
SelfAdjoint A →
GapOnPhys A →
¬ Coercive A :=
by
intro hRP hSA hG
exact Coercive_from_REQ (A := A) hRP hSA hG

end ALSTAR
