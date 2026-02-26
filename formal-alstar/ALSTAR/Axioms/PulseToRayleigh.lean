import ALSTAR.Axioms.Basic
import ALSTAR.Axioms.Pulse
import ALSTAR.Axioms.Rayleigh

namespace ALSTAR

section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (Q : H →ₗ[ℝ] H)

-- Class of observables used in PulseBound (you will specialize this later).
variable (Good : (H →L[ℝ] H) → Prop)

-- Hamiltonian-like bounded operator driving the adjoint action (specialize later).
variable (H0 : (H →L[ℝ] H))

/--
FINAL BRIDGE TARGET (axiomatized):
(LogBound + PulseBound) forces the physical Rayleigh infimum to collapse to 0.

This is the analytic heart: once proved, it replaces the remaining “two-bubble” wall
by a scalar spectral statement.
-/
axiom pulse_logbound_implies_lambdaMin_zero
  {α : Type u}
  (A : Schema α)
  (hLog : LogBound A)
  (hPulse : PulseBound (H := H) A H0 Good) :
  lambdaMinPhys (Q := Q) = 0

end

end ALSTAR
