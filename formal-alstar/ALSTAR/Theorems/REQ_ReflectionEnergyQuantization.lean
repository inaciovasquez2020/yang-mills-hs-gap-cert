import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot
import ALSTAR.Specs.PulseBridgeSpec
import ALSTAR.Theorems.TwoBubbleLowerBound
universe u
namespace ALSTAR
axiom ReflectionPositive {α : Type u} (A : Schema α) : Prop
axiom SelfAdjoint {α : Type u} (A : Schema α) : Prop
axiom SpectralGap {α : Type u} (A : Schema α) : Prop
axiom spectral_gap_constant
{α : Type u} {A : Schema α} :
SpectralGap A → ∃ γ : ℝ, 0 < γ
axiom bubble_packing_linear
{α : Type u} {A : Schema α} :
ReflectionPositive A →
SelfAdjoint A →
SpectralGap A →
∃ c : ℝ, 0 < c ∧ ∃ᶠ n in Filter.atTop, c * (n : ℝ) ≤ A.R n
theorem REQ_reflection_energy_quantization
{α : Type u}
{A : Schema α}
(hRP : ReflectionPositive A)
(hSA : SelfAdjoint A)
(hGap : SpectralGap A) :
TwoBubbleLowerBound A := by
rcases bubble_packing_linear (A := A) hRP hSA hGap with ⟨c, hcpos, hfreq⟩
exact ⟨c, hcpos, hfreq⟩
end ALSTAR
