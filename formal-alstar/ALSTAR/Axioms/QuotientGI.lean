import Mathlib.Analysis.InnerProductSpace.OperatorNorm
import Mathlib/LinearAlgebra/OrthogonalProjection

namespace ALSTAR

section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (Q : H →ₗ[ℝ] H)

abbrev ZeroModes : Submodule ℝ H := LinearMap.ker Q
abbrev Phys : Submodule ℝ H := (ZeroModes (Q := Q))ᗮ

/-- Orthogonal projection onto the physical subspace (ker Q)ᗮ. -/
noncomputable def π : H →ₗ[ℝ] H :=
  (Submodule.orthogonalProjection (Phys (Q := Q)))

/--
Gauge-invariant coercivity *after quotienting zero modes*:
coercivity of Q restricted to the physical subspace (ker Q)ᗮ.
-/
def CoerciveGIQ : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ x : H, x ∈ Phys (Q := Q) →
      c * ‖x‖^2 ≤ ⟪x, Q x⟫_ℝ

/--
Equivalent “projected” form: it suffices to check coercivity on π x.
(Useful when you build physical representatives via projection.)
-/
def CoerciveGIQ_proj : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ x : H,
      c * ‖π (Q := Q) x‖^2 ≤ ⟪π (Q := Q) x, Q (π (Q := Q) x)⟫_ℝ

end

end ALSTAR
