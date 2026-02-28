import Mathlib.Data.Real.Basic
import ALSTAR.Specs.PulseBridgeSpec

universe u

namespace ALSTAR

def TwoBubbleLowerBound {α : Type u} (A : Schema α) : Prop :=
  ∃ (c : ℝ), 0 < c ∧
    ∃ (N : ℕ), ∀ n ≥ N, c * (n : ℝ) ≤ A.R n

axiom log_vs_linear_contradiction :
  ∀ {c C : ℝ},
    0 < c →
    (∃ N : ℕ, ∀ n ≥ N, c * (n : ℝ) ≤ C * Real.log (n : ℝ)) →
    False

theorem twoBubble_excludes_logBound
  {α : Type u} {A : Schema α}
  (h : TwoBubbleLowerBound A) :
  ¬ logBound A := by
  classical
  intro hlog
  rcases h with ⟨c, hcpos, N, hlin⟩
  rcases hlog with ⟨C, hC⟩
  have hlin' :
    ∃ N : ℕ, ∀ n ≥ N, c * (n : ℝ) ≤ C * Real.log (n : ℝ) :=
  by
    refine ⟨N, ?_⟩
    intro n hn
    exact le_trans (hlin n hn) (hC n)
  exact log_vs_linear_contradiction hcpos hlin'

end ALSTAR
