import Mathlib.Data.Real.Basic
import ALSTAR.Axioms.Coercivity
import ALSTAR.Theorems.TwoBubbleLowerBound
namespace ALSTAR
theorem twoBubble_implies_NonCoercive
{α : Type u} {A : Schema α}
(h : TwoBubbleLowerBound A) :
NonCoercive A := by
intro hC
rcases hC with ⟨c0, N, hc0pos, hbound⟩
have hfreq' : ∃ᶠ n in Filter.atTop, c0 * (n : ℝ) ≤ A.R n := by
refine (Filter.eventually_atTop.2 ⟨N, ?⟩).frequently
intro n hn
have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.cast_pos.mpr (Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.succ_pos 0) hn)))
have := (hbound n hn)
have := (le_div_iff₀ hnpos).1 this
simpa [mul_div_assoc] using this
have : ¬ logBound A := twoBubble_excludes_logBound h
exact this (by
refine ⟨c0, ?⟩
intro n
have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.cast_pos.mpr (Nat.succ_pos _)
have : (A.R n) ≤ c0 * Real.log (n : ℝ) := by
have := hbound n (Nat.le_of_lt (Nat.succ_pos _))
have := (div_le_iff₀ hnpos).1 this
simpa [mul_div_assoc] using this
exact this)
end ALSTAR
