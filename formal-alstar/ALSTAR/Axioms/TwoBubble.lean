import ALSTAR.Axioms.Basic

namespace ALSTAR

/--
Two-bubble obstruction axiom:
Log-locality implies contradiction.
-/
axiom two_bubble_log_locality_incompatible
  {α : Type u}
  (A : Schema α)
  (hR : ∀ n : ℕ, A.R n ≤ log₂ n) :
  False

end ALSTAR
