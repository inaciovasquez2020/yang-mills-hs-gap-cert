import Mathlib.Data.Nat.Log

namespace ALSTAR

/-- Base-2 logarithm used throughout ALSTAR. -/
def log₂ (n : ℕ) : ℕ := Nat.log 2 n

/-- Schema parameterized by α with a numeric growth functional R : ℕ → ℕ. -/
structure Schema (α : Type u) where
  R : ℕ → ℕ

/-- Log-bound predicate for a schema's growth functional. -/
def LogBound {α : Type u} (A : Schema α) : Prop :=
  ∀ n : ℕ, A.R n ≤ log₂ n

end ALSTAR
