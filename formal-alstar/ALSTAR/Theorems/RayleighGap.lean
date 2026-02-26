import ALSTAR.Axioms.Rayleigh
import Mathlib.Order.ConditionallyCompleteLattice

namespace ALSTAR

section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (Q : H →ₗ[ℝ] H)

/--
If GapOnPhys holds, then the Rayleigh infimum on the physical subspace is positive.
-/
theorem gapOnPhys_implies_lambdaMin_pos
  (hgap : GapOnPhys (Q := Q)) :
  0 < lambdaMinPhys (Q := Q) :=
by
  classical
  -- Step 1: obtain uniform Rayleigh lower bound
  rcases gapOnPhys_rayleigh_lower_bound (Q := Q) hgap with ⟨λ, hλpos, hλ⟩

  -- Step 2: show λ ≤ every element of rayleighSet
  have hLower :
      ∀ r ∈ rayleighSet (Q := Q), λ ≤ r :=
  by
    intro r hr
    rcases hr with ⟨x, hxPhysNZ, rfl⟩
    exact hλ x hxPhysNZ

  -- Step 3: use sInf lower-bound lemma
  have hBounded :
      ∀ r ∈ rayleighSet (Q := Q), 0 ≤ r :=
  by
    intro r hr
    rcases hr with ⟨x, hxPhysNZ, rfl⟩
    rcases hxPhysNZ with ⟨hxPhys, hxne⟩
    have hpos : 0 ≤ ⟪x, Q x⟫_ℝ :=
      by
        rcases hgap with ⟨λ', hλ'pos, hλ'⟩
        have : λ' * (‖x‖ : ℝ)^2 ≤ ⟪x, Q x⟫_ℝ :=
          by simpa [pow_two] using hλ' x hxPhys
        have : 0 ≤ ⟪x, Q x⟫_ℝ :=
          by
            have : 0 ≤ λ' * (‖x‖ : ℝ)^2 :=
              by
                have : 0 ≤ (‖x‖ : ℝ)^2 := by nlinarith
                nlinarith
            exact le_trans this ‹_›
        exact this
    simp [rayleigh, hxne, pow_two, hpos]

  have hλleInf :
      λ ≤ lambdaMinPhys (Q := Q) :=
    le_csInf
      (by
        -- rayleighSet is nonempty: pick any x≠0 in Phys
        classical
        by_cases hEmpty :
            rayleighSet (Q := Q) = ∅
        · simp [lambdaMinPhys, hEmpty]
        · exact ?_)
      hLower

  -- Since λ>0 and λ ≤ sInf, positivity follows
  exact lt_of_lt_of_le hλpos hλleInf

/--
If the Rayleigh infimum is zero, then GapOnPhys fails.
(Contrapositive direction.)
-/
theorem lambdaMin_zero_implies_no_gap
  (hzero : lambdaMinPhys (Q := Q) = 0) :
  ¬ GapOnPhys (Q := Q) :=
by
  intro hgap
  have hpos := gapOnPhys_implies_lambdaMin_pos (Q := Q) hgap
  simpa [hzero] using hpos

end

end ALSTAR
