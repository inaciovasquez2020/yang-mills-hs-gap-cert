import ALSTAR.Axioms.Basic
import ALSTAR.Axioms.TwoBubble

namespace ALSTAR

/--
Dichotomy theorem:
Either growth exceeds log₂,
or contradiction follows.
-/
theorem dichotomy_theorem
  {α : Type u}
  (A : Schema α) :
  (∃ n : ℕ, A.R n > log₂ n) ∨ False :=
by
  classical
  by_cases h : ∀ n : ℕ, A.R n ≤ log₂ n
  · right
    exact two_bubble_log_locality_incompatible A h
  · left
    push_neg at h
    exact h

end ALSTAR
