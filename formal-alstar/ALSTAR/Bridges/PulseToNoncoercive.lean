import ALSTAR.Axioms.Basic
import ALSTAR.Axioms.Coercivity

namespace ALSTAR

theorem pulse_logbound_implies_noncoercive_target
  {α : Type u}
  (A : Schema α)
  (hLog : ∀ n : ℕ, A.R n ≤ Nat.log2 n) :
  TwoBubbleObstructed A :=
by
  classical
  sorry

end ALSTAR
