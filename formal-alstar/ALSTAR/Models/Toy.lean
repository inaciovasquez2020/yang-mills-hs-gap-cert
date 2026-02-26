import ALSTAR.Axioms.Basic

namespace ALSTAR

/-- Toy coercivity: existence of a strictly positive uniform lower bound on R. -/
def CoerciveToy {α : Type u} (A : Schema α) : Prop :=
  ∃ c : ℕ, 0 < c ∧ ∀ n : ℕ, c ≤ A.R n

def TwoBubbleObstructedToy {α : Type u} (A : Schema α) : Prop :=
  ¬ CoerciveToy A

/--
Toy theorem (restricted regime):
If LogBound holds, then R(1)=0 hence no strictly positive uniform lower bound exists.
-/
theorem two_bubble_log_locality_incompatible_toy
  {α : Type u} (A : Schema α) (h : LogBound A) :
  TwoBubbleObstructedToy A :=
by
  intro hc
  rcases hc with ⟨c, hcpos, hcLB⟩
  have h1 : A.R 1 ≤ log₂ 1 := h 1
  have hlog1 : log₂ 1 = 0 := by
    simp [ALSTAR.log₂]
  have hR1 : A.R 1 = 0 := by
    have : A.R 1 ≤ 0 := by simpa [hlog1] using h1
    exact Nat.eq_zero_of_le_zero this
  have hc_le_R1 : c ≤ A.R 1 := hcLB 1
  have hc_le_0 : c ≤ 0 := by simpa [hR1] using hc_le_R1
  exact Nat.not_lt_zero c (Nat.lt_of_lt_of_le hcpos hc_le_0)

end ALSTAR
