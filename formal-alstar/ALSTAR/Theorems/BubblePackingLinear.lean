import Mathlib.Data.Real.Basic
import ALSTAR.Specs.PulseBridgeSpec
import ALSTAR.Theorems.TwoBubbleLowerBound
import ALSTAR.Theorems.BubbleEnergy
universe u
namespace ALSTAR
variable {α : Type u}
axiom packing_count
{α : Type u} (A : Schema α) :
ℕ → ℕ
axiom packing_linear
{α : Type u} (A : Schema α) :
∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, ∀ n ≥ N, (packing_count (A := A) n : ℝ) ≥ a * (n : ℝ)
axiom per_bubble_energy_lb
{α : Type u} (A : Schema α) :
∃ γ : ℝ, 0 < γ
axiom R_lower_bounds_packed_energy
{α : Type u} (A : Schema α) :
∀ n : ℕ, (packing_count (A := A) n : ℝ) * (Classical.choose (per_bubble_energy_lb (A := A)) : ℝ) ≤ A.R n
theorem BubblePackingLinear
{α : Type u} (A : Schema α) :
TwoBubbleLowerBound A := by
classical
rcases packing_linear (A := A) with ⟨a, ha, N, hpack⟩
rcases per_bubble_energy_lb (A := A) with ⟨γ, hγ⟩
refine ⟨a * γ, mul_pos ha hγ, N, ?_⟩
intro n hn
have hk : (packing_count (A := A) n : ℝ) ≥ a * (n : ℝ) := hpack n hn
have hR : (packing_count (A := A) n : ℝ) * γ ≤ A.R n := by
have : (packing_count (A := A) n : ℝ) *
(Classical.choose (per_bubble_energy_lb (A := A)) : ℝ) ≤ A.R n :=
R_lower_bounds_packed_energy (A := A) n
simpa [Classical.choose_spec (per_bubble_energy_lb (A := A))] using this
have : (a * γ) * (n : ℝ) ≤ (packing_count (A := A) n : ℝ) * γ := by
have hγ' : 0 ≤ γ := le_of_lt hγ
have := mul_le_mul_of_nonneg_right (le_of_lt hk) hγ'
simpa [mul_assoc, mul_left_comm, mul_comm] using this
exact le_trans (by simpa [mul_assoc] using this) hR
end ALSTAR
