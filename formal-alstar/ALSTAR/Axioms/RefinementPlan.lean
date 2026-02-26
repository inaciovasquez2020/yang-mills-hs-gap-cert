import ALSTAR.Axioms.Basic
import ALSTAR.Axioms.Coercivity

namespace ALSTAR

/-
Refinement targets (replace axioms by proofs progressively).

1) Strengthen Coercive:
   replace the toy lower-bound predicate by the true gauge-invariant coercivity
   statement (after quotienting zero modes) in your Hilbert-space model.

2) Prove the structured two-bubble statement:
   theorem two_bubble_log_locality_incompatible_proof
     (A : Schema α) (hR : LogBound A) : TwoBubbleObstructed A

3) Swap log₂ definition if desired:
   keep `log₂` as the single normalization point; if you later move to `Nat.log2`,
   change only `Basic.lean` and downstream stays stable.
-/

end ALSTAR
