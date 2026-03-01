import Mathlib.Analysis.SpecialFunctions.Hermite
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian
import Mathlib.Analysis.InnerProductSpace.Basic
import ALSTAR.Analysis.HermiteBandDecay

noncomputable section
open Real MeasureTheory

namespace ALSTAR

/--
Define the Gaussian-weighted Hermite integral kernel matrix.
-/
def hermiteKernel (i j : ℕ) : ℝ :=
  ∫ x : ℝ,
    (hermite i x) *
    (hermite j x) *
    Real.exp (-x^2)

/--
The Hermite kernel is diagonal.
-/
theorem hermiteKernel_diagonal (i j : ℕ) :
  hermiteKernel i j =
  if i = j then
    (2^i * (Nat.factorial i) * Real.sqrt π)
  else
    0 := by
  unfold hermiteKernel
  simpa using hermite_gaussian_orthogonality i j

/--
Off-diagonal entries vanish.
-/
theorem hermiteKernel_offdiag (i j : ℕ) (h : i ≠ j) :
  hermiteKernel i j = 0 := by
  have := hermiteKernel_diagonal i j
  simp [h] at this
  exact this

end ALSTAR
