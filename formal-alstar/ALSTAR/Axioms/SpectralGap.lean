import ALSTAR.Axioms.QuotientGI
import Mathlib.Analysis.InnerProductSpace.Spectrum

namespace ALSTAR

section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (Q : H →ₗ[ℝ] H)

/--
Spectral gap after quotienting zero modes:
There exists λ>0 such that Q ≥ λ on (ker Q)ᗮ.
-/
def SpectralGap : Prop :=
  ∃ λ : ℝ, 0 < λ ∧
    ∀ x : H, x ∈ (LinearMap.ker Q)ᗮ →
      λ * ‖x‖^2 ≤ ⟪x, Q x⟫_ℝ

/--
Spectral gap implies coercivity.
-/
theorem spectralGap_implies_coercive :
  SpectralGap (Q:=Q) → CoerciveGIQ (Q:=Q) :=
by
  intro h
  exact h

end

end ALSTAR
