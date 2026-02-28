import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Tactic
import ALSTAR.Specs.PulseBridgeSpec
namespace ALSTAR
def TwoBubbleLowerBound {α : Type u} (A : Schema α) : Prop :=
∃ (c : ℝ), 0 < c ∧ ∃ᶠ n in Filter.atTop, c * (n : ℝ) ≤ A.R n
theorem twoBubble_excludes_logBound
{α : Type u} {A : Schema α}
(h : TwoBubbleLowerBound A) :
¬ logBound A := by
classical
intro hlog
rcases h with ⟨c, hcpos, hfreq⟩
rcases hlog with ⟨C, hC⟩
have : ∃ᶠ n in Filter.atTop, c * (n : ℝ) ≤ C * Real.log (n : ℝ) := by
refine hfreq.filter_mono ?_
intro n hn
exact le_trans hn (hC n)
have hlim :
Filter.Tendsto
(fun n : ℕ => (C * Real.log (n : ℝ)) / (n : ℝ))
Filter.atTop
(Filter.nhds 0) := by
have h1 :
Filter.Tendsto
(fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
Filter.atTop
(Filter.nhds 0) :=
Real.tendsto_log_div_self_atTop
have h2 :
Filter.Tendsto
(fun x : ℝ => C * x)
(Filter.nhds 0)
(Filter.nhds (C * 0)) :=
Filter.tendsto_const_nhds.mul Filter.tendsto_id
simpa [mul_div_assoc] using h2.comp h1
have hpos :
∀ᶠ n in Filter.atTop,
(c : ℝ) ≤ (C * Real.log (n : ℝ)) / (n : ℝ) := by
refine this.mono ?_
intro n hn
have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.cast_pos.mpr (Nat.pos_of_gt (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le _) (Nat.succ_pos _))))
have := (le_div_iff₀ hnpos).mpr hn
simpa [mul_div_assoc] using this
have : c ≤ 0 := by
have := Filter.eventually_of_tendsto_of_eventually_le hlim hpos
simpa using this
exact (lt_irrefl 0 (lt_of_lt_of_le hcpos this))
end ALSTAR
