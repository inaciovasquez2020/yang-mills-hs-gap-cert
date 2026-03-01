import Mathlib.Analysis.SpecialFunctions.Hermite
import Mathlib.Analysis.SpecialFunctions.Gaussian
import ALSTAR.Analysis.HermiteDiagonalOperator

noncomputable section
open Real MeasureTheory

namespace ALSTAR

theorem hermiteKernel_diag_pos (i : ℕ) :
  0 < hermiteKernel i i := by
  have h := hermiteKernel_diagonal i i
  simp at h
  simpa [h] using
    mul_pos
      (mul_pos (pow_pos (show (0:ℝ) < 2 by norm_num) i) (by
        exact_mod_cast Nat.factorial_pos i))
      (Real.sqrt_pos.2 (by have : (0:ℝ) < π := Real.pi_pos; exact le_of_lt this))

theorem hermiteKernel_symm (i j : ℕ) :
  hermiteKernel i j = hermiteKernel j i := by
  unfold hermiteKernel
  simpa [mul_left_comm, mul_assoc, mul_comm]

end ALSTAR
