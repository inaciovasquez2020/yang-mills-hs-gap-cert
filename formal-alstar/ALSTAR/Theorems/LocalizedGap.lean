import ALSTAR.Axioms.SpectralGap
import ALSTAR.Specs.PulseBridgeSpec

universe u

namespace ALSTAR

variable {α : Type u}

/--
Localized spectral gap:
If A has a physical spectral gap γ > 0,
then any ψ supported in a bubble region
has energy ≥ γ.
-/
theorem localized_gap_lower_bound
  (A : Schema α)
  (γ : ℝ)
  (hgap : GapOnPhys A γ)
  (ψ : BubbleState α)
  (hsupp : SupportedInBubble ψ)
  (hnorm : ‖ψ‖ = 1) :
  Energy A ψ ≥ γ := by
  -- replace with actual restriction-to-bubble argument
  exact hgap ψ hnorm

end ALSTAR
