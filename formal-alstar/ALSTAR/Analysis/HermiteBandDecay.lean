import Mathlib.Analysis.SpecialFunctions.Hermite
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian
import Mathlib.Analysis.InnerProductSpace.Basic

noncomputable section
open Real MeasureTheory

namespace ALSTAR

/--
Orthogonality of Hermite polynomials with Gaussian weight.

This is the exact analytic structure underlying the
numerical diagonal dominance observed in the GLE matrix.
-/
theorem hermite_gaussian_orthogonality
  (i j : ℕ) :
  ∫ x : ℝ,
    (hermite i x) *
    (hermite j x) *
    Real.exp (-x^2) =
  if i = j then
    (2^i * (Nat.factorial i) * Real.sqrt π)
  else
    0 := by
  classical
  simpa using
    Real.hermite_integral_mul_exp_neg_sq i j

end ALSTAR
