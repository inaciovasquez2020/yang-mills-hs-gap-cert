import Mathlib.Analysis.InnerProductSpace.Adjoint
import ALSTAR.Axioms.QuotientGI
import ALSTAR.Axioms.SpectralGap

namespace ALSTAR

section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (Q : H →ₗ[ℝ] H)

/-- Self-adjointness predicate for the YM-relevant operator. -/
def SelfAdjointQ : Prop :=
  IsSelfAdjoint Q

/-- Positivity on the physical subspace (ker Q)ᗮ via Rayleigh form. -/
def PositiveOnPhys : Prop :=
  ∀ x : H, x ∈ (LinearMap.ker Q)ᗮ → 0 ≤ ⟪x, Q x⟫_ℝ

/--
Spectral-gap-style lower bound on the physical subspace (ker Q)ᗮ.
(Notation-aligned with `SpectralGap`.)
-/
def GapOnPhys : Prop :=
  SpectralGap (Q := Q)

end

end ALSTAR
