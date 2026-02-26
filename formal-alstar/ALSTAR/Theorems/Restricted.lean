import ALSTAR.Axioms.Basic
import ALSTAR.Models.Toy

namespace ALSTAR

/--
Begin eliminating axioms: in the Toy model, the "two-bubble" consequence is provable,
so no axiom is needed in this restricted regime.
-/
theorem two_bubble_incompatible_in_restricted_regime
  {α : Type u} (A : Schema α) (h : LogBound A) :
  TwoBubbleObstructedToy A :=
two_bubble_log_locality_incompatible_toy A h

end ALSTAR
