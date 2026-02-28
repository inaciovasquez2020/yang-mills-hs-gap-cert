import Mathlib.Data.Real.Basic
import ALSTAR.Axioms.Coercivity
import ALSTAR.Theorems.TwoBubbleLowerBound
universe u
namespace ALSTAR
abbrev Schema := TwoBubbleLowerBound.Schema
def logBound {α : Type u} (A : Schema α) : Prop :=
TwoBubbleLowerBound.logBound (A := A)
def NonCoercive {α : Type u} (A : Schema α) : Prop :=
¬ Coercive A
def Pulse {α : Type u} (A : Schema α) : Prop :=
logBound A
structure PulseBridgeHyp {α : Type u} (A : Schema α) : Prop where
pulse_to_twoBubble :
Pulse A → TwoBubbleLowerBound A
end ALSTAR
