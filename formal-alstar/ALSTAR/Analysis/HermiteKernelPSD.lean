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

/--
The Hermite Gaussian kernel is positive semidefinite:
finite linear combinations have nonnegative quadratic form.
-/
theorem hermiteKernel_psd
  (n : ℕ)
  (a : Fin n → ℝ) :
  0 ≤
    ∑ i : Fin n,
      ∑ j : Fin n,
        a i * a j * hermiteKernel i j := by
  classical
  -- since the kernel is diagonal and diagonal entries are positive,
  -- the quadratic form reduces to a sum of positive terms.
  have :
    ∑ i : Fin n,
      ∑ j : Fin n,
        a i * a j * hermiteKernel i j
    =
    ∑ i : Fin n,
      (a i)^2 * hermiteKernel i i := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i = j
    · subst h
      simp
    · simp [hermiteKernel_offdiag, h]
  simp [this]
  apply Finset.sum_nonneg
  intro i _
  have hpos := hermiteKernel_diag_pos i
  have : 0 ≤ (a i)^2 := by
    exact sq_nonneg _
  exact mul_nonneg this (le_of_lt hpos)

end ALSTAR
