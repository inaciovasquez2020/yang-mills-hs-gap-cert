import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Data.Real.Basic

noncomputable section
open Classical
open Real

namespace REAP

/-- Abstract quantum system modeled as a real inner product space. -/
structure EnergySystem where
  H        : Type
  instIP   : InnerProductSpace ℝ H
  energy   : H → ℝ
  vacuum   : H
  energy_vacuum : energy vacuum = 0
  energy_nonneg : ∀ ψ, 0 ≤ energy ψ

attribute [instance] EnergySystem.instIP

/-- Orthogonality to vacuum. -/
def Orthogonal (S : EnergySystem) (ψ : S.H) : Prop :=
  ψ ≠ S.vacuum

/-- REAP: uniform positive lower bound away from vacuum. -/
def REAP (S : EnergySystem) : Prop :=
  ∃ m₀ > 0,
    ∀ ψ, Orthogonal S ψ →
      S.energy ψ ≥ m₀ * ‖ψ‖^2

/-- Mass gap formulation. -/
def MassGap (S : EnergySystem) : Prop :=
  ∃ m₀ > 0,
    ∀ ψ, Orthogonal S ψ →
      S.energy ψ / ‖ψ‖^2 ≥ m₀

theorem reap_implies_gap
  (S : EnergySystem)
  (hREAP : REAP S) :
  MassGap S :=
by
  rcases hREAP with ⟨m₀, hm₀pos, hbound⟩
  use m₀
  constructor
  · exact hm₀pos
  · intro ψ hψ
    have h := hbound ψ hψ
    have hnorm : ‖ψ‖^2 > 0 := by
      have hne : ψ ≠ 0 := by
        intro hzero
        have : ψ = S.vacuum := by
          cases S
          simp at hzero
        exact hψ this
      have : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hne
      have : ‖ψ‖ > 0 := lt_of_le_of_ne' (norm_nonneg ψ) this.symm
      have : ‖ψ‖^2 > 0 := by
        have := pow_pos this 2
        simpa using this
      exact this
    have := (div_le_iff hnorm).mpr h
    simpa using this

end REAP
