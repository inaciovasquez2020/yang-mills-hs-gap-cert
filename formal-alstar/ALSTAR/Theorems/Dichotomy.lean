import ALSTAR.Axioms.Basic
import ALSTAR.Axioms.Coercivity
import ALSTAR.Axioms.TwoBubble

namespace ALSTAR

/--
Dichotomy theorem (structured):
either R exceeds log₂ somewhere, or coercivity fails (two-bubble obstruction).
-/
theorem dichotomy_theorem
  {α : Type u}
  (A : Schema α) :
  (∃ n : ℕ, A.R n > log₂ n) ∨ TwoBubbleObstructed A :=
by
  classical
  by_cases h : LogBound A
  · right
    exact two_bubble_log_locality_incompatible A h
  · left
    -- ¬(∀ n, A.R n ≤ log₂ n)  ⇒  ∃ n, A.R n > log₂ n
    unfold LogBound at h
    push_neg at h
    exact h

end ALSTAR
