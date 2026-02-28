import Mathlib.Data.Real.Basic
import ALSTAR.Specs.PulseBridgeSpec
import ALSTAR.Theorems.TwoBubbleLowerBound
universe u
namespace ALSTAR
axiom logBound {α : Type u} (A : Schema α) : Prop
axiom logBound_upper
{α : Type u} (A : Schema α) :
logBound A →
∃ C : ℝ, ∀ n : ℕ, A.R n ≤ C * Real.log (n : ℝ)
theorem TwoBubble_excludes_logBound
{α : Type u} (A : Schema α) :
TwoBubbleLowerBound A →
¬ logBound A := by
intro h2 hlog
rcases h2 with ⟨c, hcpos, N, hlin⟩
rcases logBound_upper (A := A) hlog with ⟨C, hC⟩
have : False := by
have hbig := hlin (max N 1) (by
have : max N 1 ≥ N := le_max_left _ _
exact this)
have hsmall := hC (max N 1)
have hpos : (0 : ℝ) < (max N 1 : ℝ) := by
have : (1 : ℕ) ≤ max N 1 := le_max_right _ _
exact_mod_cast this
have hcontr :=
calc
c * (max N 1 : ℝ)
≤ A.R (max N 1) := hbig
_ ≤ C * Real.log (max N 1 : ℝ) := hsmall
have : c ≤ C * Real.log (max N 1 : ℝ) / (max N 1 : ℝ) := by
have := hcontr
have := (div_le_iff hpos).mpr this
simpa [mul_comm, mul_left_comm, mul_assoc] using this
exact False.elim (lt_irrefl _ (lt_of_le_of_lt this ?_))
exact this
end ALSTAR
