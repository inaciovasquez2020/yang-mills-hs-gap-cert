import Mathlib.Analysis.InnerProductSpace.OperatorNorm
import Mathlib/LinearAlgebra/OrthogonalProjection

namespace ALSTAR

/--
Gauge-invariant Hilbert-space coercivity after quotienting zero modes:

There exists c>0 such that for all x orthogonal to ker(Q),
    c * ‖x‖^2 ≤ ⟪x, Q x⟫.
This is the structured target you will later prove for YM.
-/
def CoerciveGI
  {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (Q : H →ₗ[ℝ] H) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ x : H, x ∈ (LinearMap.ker Q)ᗮ →
      c * ‖x‖^2 ≤ ⟪x, Q x⟫_ℝ

/-- Named failure predicate (structured obstruction form). -/
def NonCoerciveGI
  {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  (Q : H →ₗ[ℝ] H) : Prop :=
  ¬ CoerciveGI Q

end ALSTAR
