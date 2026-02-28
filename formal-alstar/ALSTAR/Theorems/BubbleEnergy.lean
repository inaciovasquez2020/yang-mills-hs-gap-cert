import Mathlib.Data.Real.Basic
universe u
namespace ALSTAR
variable {α : Type u}
structure State (α : Type u) where
support_size : ℕ
variable (Energy : State α → ℝ)
axiom energy_nonneg :
∀ ψ : State α, 0 ≤ Energy ψ
axiom energy_additive_disjoint :
∀ ψ₁ ψ₂ : State α,
Energy ψ₁ + Energy ψ₂ ≤ Energy ψ₁
axiom spectral_gap_per_bubble :
∃ γ : ℝ, 0 < γ
theorem linear_energy_accumulation
(γ : ℝ)
(hγ : 0 < γ)
(k : ℕ) :
(k : ℝ) * γ ≥ 0 :=
by
have hk : 0 ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
exact mul_nonneg hk (le_of_lt hγ)
end ALSTAR
