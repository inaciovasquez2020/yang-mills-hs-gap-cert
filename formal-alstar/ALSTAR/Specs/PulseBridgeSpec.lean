import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import ALSTAR.Axioms.Coercivity

universe u

namespace ALSTAR

def logBound {α : Type u} (A : Schema α) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, A.R n ≤ C * Real.log (n : ℝ)

def NonCoercive {α : Type u} (A : Schema α) : Prop :=
  ¬ Coercive A

def Pulse {α : Type u} (A : Schema α) : Prop :=
  logBound A

end ALSTAR
