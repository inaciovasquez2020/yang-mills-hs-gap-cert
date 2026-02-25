import Mathlib
import ALSTAR.Axioms.Basic
import ALSTAR.Axioms.TwoBubble

namespace ALSTAR

theorem no_log_locality
  {α : Type} (A : Schema α)
  (hR : ∀ n, A.R n ≤ Nat.log n)
  (hPrecise : True) :
  False :=
by
  -- mark hPrecise as intentionally used (semantic dependency)
  have _ := hPrecise
  exact two_bubble_log_locality_incompatible (A := A) hR

end ALSTAR
