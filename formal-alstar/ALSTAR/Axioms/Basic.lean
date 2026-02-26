import Mathlib.Data.Nat.Log

namespace ALSTAR

/-- Binary logarithm (base 2) used in ALSTAR. -/
def log₂ (n : ℕ) : ℕ :=
  Nat.log 2 n

/-- Schema parameterized by α with numeric growth function R. -/
structure Schema (α : Type u) where
  R : ℕ → ℕ

end ALSTAR
