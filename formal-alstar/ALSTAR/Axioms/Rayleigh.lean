import ALSTAR.Axioms.SelfAdjoint
import Mathlib.Order.ConditionallyCompleteLattice
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ALSTAR

section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (Q : H →ₗ[ℝ] H)

/-- Physical subspace: (ker Q)ᗮ. -/
abbrev Phys : Set H := { x : H | x ∈ (LinearMap.ker Q)ᗮ }

/-- Physical nonzero vectors. -/
abbrev PhysNZ : Set H := { x : H | x ∈ (LinearMap.ker Q)ᗮ ∧ x ≠ 0 }

/-- Rayleigh quotient (defined as 0 at x=0). -/
noncomputable def rayleigh (x : H) : ℝ :=
  if hx : x = 0 then 0 else ⟪x, Q x⟫_ℝ / (‖x‖^2)

/-- Set of Rayleigh values over physical nonzero vectors. -/
noncomputable def rayleighSet : Set ℝ :=
  { r : ℝ | ∃ x : H, x ∈ PhysNZ (Q := Q) ∧ r = rayleigh (Q := Q) x }

/-- Physical bottom of spectrum (Rayleigh infimum). -/
noncomputable def lambdaMinPhys : ℝ :=
  sInf (rayleighSet (Q := Q))

/-
Targets:

(1) GapOnPhys (Q:=Q) ↔ 0 < lambdaMinPhys (Q:=Q)
(2) GapOnPhys (Q:=Q) ↔ ∃ λ>0, ∀ x∈PhysNZ, λ ≤ rayleigh x
(3) If SelfAdjointQ (Q:=Q), then lambdaMinPhys equals the smallest nonzero spectral value
    in discrete/compact regimes.
-/

theorem gapOnPhys_rayleigh_lower_bound
  (hgap : GapOnPhys (Q := Q)) :
  ∃ λ : ℝ, 0 < λ ∧ ∀ x : H, x ∈ PhysNZ (Q := Q) → λ ≤ rayleigh (Q := Q) x :=
by
  rcases hgap with ⟨λ, hλpos, hλ⟩
  refine ⟨λ, hλpos, ?_⟩
  intro x hx
  rcases hx with ⟨hxPhys, hxne⟩
  have hxnormpos : 0 < (‖x‖ : ℝ) := by
    exact (norm_pos_iff.mpr hxne)
  have hxdenpos : 0 < (‖x‖ : ℝ)^2 := by
    nlinarith
  have hineq : λ * (‖x‖ : ℝ)^2 ≤ ⟪x, Q x⟫_ℝ := by
    simpa [pow_two] using hλ x hxPhys
  have hdiv : λ * (‖x‖ : ℝ)^2 / (‖x‖ : ℝ)^2 ≤ ⟪x, Q x⟫_ℝ / (‖x‖ : ℝ)^2 :=
    (div_le_div_of_le hxdenpos hineq)
  have hxdenne : (‖x‖ : ℝ)^2 ≠ 0 := ne_of_gt hxdenpos
  have hleft : λ * (‖x‖ : ℝ)^2 / (‖x‖ : ℝ)^2 = λ := by
    field_simp [hxdenne]
  have : λ ≤ ⟪x, Q x⟫_ℝ / (‖x‖ : ℝ)^2 := by
    simpa [hleft] using hdiv
  simp [rayleigh, hxne, pow_two] at this ⊢
  exact this

end

end ALSTAR
