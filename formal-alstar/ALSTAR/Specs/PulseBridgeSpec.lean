import ALSTAR.Axioms.Coercivity
universe u
namespace ALSTAR
structure Schema (α : Type u) where
R : ℕ → ℝ
def logBound {α : Type u} (A : Schema α) : Prop :=
∃ C : ℝ, ∀ n : ℕ, A.R n ≤ C * Real.log (n : ℝ)
def NonCoercive {α : Type u} (A : Schema α) : Prop :=
¬ Coercive A
def Pulse {α : Type u} (A : Schema α) : Prop :=
logBound A
structure PulseBridgeHyp {α : Type u} (A : Schema α) : Prop :=
(pulse_to_twoBubble : Pulse A → TwoBubbleLowerBound A)
end ALSTAR
