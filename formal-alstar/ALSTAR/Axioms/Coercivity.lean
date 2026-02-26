import ALSTAR.Axioms.Basic

namespace ALSTAR

/--
Coercivity predicate (structured target).
You can later refine this to the exact Hilbert-space coercivity statement.
-/
def Coercive {α : Type u} (A : Schema α) : Prop :=
  ∃ c : ℕ, ∀ n : ℕ, c ≤ A.R n

/-- Named obstruction conclusion (structured target). -/
def TwoBubbleObstructed {α : Type u} (A : Schema α) : Prop :=
  ¬ Coercive A

end ALSTAR
