import Mathlib.Data.Real.Basic
import ALSTAR.Specs.PulseBridgeSpec
import ALSTAR.Theorems.TwoBubbleLowerBound
import ALSTAR.Theorems.BubbleEnergy
import ALSTAR.Theorems.LocalizedGap

universe u

namespace ALSTAR

variable {α : Type u}

/-- Packing count function (abstract) -/
axiom packing_count
  {α : Type u} (A : Schema α) :
  ℕ → ℕ

/-- Linear growth of packing count -/
axiom packing_linear
  {α : Type u} (A : Schema α) :
  ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ,
    ∀ n ≥ N,
      (packing_count (A := A) n : ℝ) ≥ a * (n : ℝ)

/-- Packed energy lower bound using LocalizedGap constant -/
axiom R_lower_bounds_packed_energy
  {α : Type u} (A : Schema α) :
  ∀ n : ℕ,
    (packing_count (A := A) n : ℝ)
      * (LocalizedGap.gap A)
      ≤ A.R n

/-- Linear energy lower bound derived from packing + LocalizedGap -/
theorem BubblePackingLinear
  {α : Type u} (A : Schema α) :
  TwoBubbleLowerBound A := by
  classical

  rcases packing_linear (A := A) with ⟨a, ha, N, hpack⟩

  let γ := LocalizedGap.gap A
  have hγ : 0 < γ := LocalizedGap.gap_pos A

  refine ⟨a * γ, mul_pos ha hγ, N, ?_⟩
  intro n hn

  have hk :
      (packing_count (A := A) n : ℝ)
        ≥ a * (n : ℝ) :=
    hpack n hn

  have hR :
      (packing_count (A := A) n : ℝ) * γ
        ≤ A.R n :=
    R_lower_bounds_packed_energy (A := A) n

  have :
      (a * γ) * (n : ℝ)
        ≤ (packing_count (A := A) n : ℝ) * γ := by
    have hγ' : 0 ≤ γ := le_of_lt hγ
    have :=
      mul_le_mul_of_nonneg_right (le_of_lt hk) hγ'
    simpa [mul_assoc, mul_left_comm, mul_comm] using this

  exact
    le_trans
      (by simpa [mul_assoc] using this)
      hR

end ALSTAR
