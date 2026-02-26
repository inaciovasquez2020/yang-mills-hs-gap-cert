import ALSTAR.Axioms.PulseToRayleigh
import ALSTAR.Theorems.RayleighGap

namespace ALSTAR

section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (Q : H →ₗ[ℝ] H)
variable (Good : (H →L[ℝ] H) → Prop)
variable (H0 : (H →L[ℝ] H))

/--
(LogBound + PulseBound) ⇒ λ_min^phys = 0 ⇒ ¬GapOnPhys.

This is the end-to-end “mass-gap collapse” corollary from the bridge axiom.
-/
theorem pulse_logbound_implies_no_gap
  {α : Type u}
  (A : Schema α)
  (hLog : LogBound A)
  (hPulse : PulseBound (H := H) A H0 Good) :
  ¬ GapOnPhys (Q := Q) :=
by
  have h0 : lambdaMinPhys (Q := Q) = 0 :=
    pulse_logbound_implies_lambdaMin_zero (Q := Q) (Good := Good) (H0 := H0) A hLog hPulse
  exact lambdaMin_zero_implies_no_gap (Q := Q) h0

end

end ALSTAR
