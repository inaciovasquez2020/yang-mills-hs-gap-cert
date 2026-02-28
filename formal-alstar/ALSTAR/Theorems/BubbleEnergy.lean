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
end ALSTAR
