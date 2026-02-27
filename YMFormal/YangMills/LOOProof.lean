import Mathlib.Topology.ContinuousFunction.ZeroAtInfty
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order

namespace YangMillsGap

open scoped Real
open Topology

variable {n : ℕ}

def LOO (R : ℝ) (φ : C₀(ℝⁿ, ℝ)) : ℝ :=
  ⨆ x : ℝⁿ, |φ x| * Real.exp (R * ‖x‖)

theorem loo_excludes_ir_exp
  (R : ℝ) (hR : 0 < R) (φ : C₀(ℝⁿ, ℝ))
  (hlocal : tsupport φ ⊆ Metric.ball (0:ℝⁿ) (R⁻¹)) :
  LOO (n := n) R φ ≤ Real.exp 1 * ‖φ‖∞ := by
  classical
  refine iSup_le ?_
  intro x
  by_cases hx : x ∈ tsupport φ
  · have hxball : x ∈ Metric.ball (0:ℝⁿ) (R⁻¹) := hlocal hx
    have hnorm : ‖x‖ < R⁻¹ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hxball
    have hRx : R * ‖x‖ ≤ 1 := by
      have : R * ‖x‖ < R * R⁻¹ := (mul_lt_mul_of_pos_left hnorm hR)
      have : R * ‖x‖ < 1 := by simpa [mul_inv_cancel (ne_of_gt hR)] using this
      exact le_of_lt this
    have hexp : Real.exp (R * ‖x‖) ≤ Real.exp 1 := by
      exact Real.exp_monotone hRx
    have hphi : |φ x| ≤ ‖φ‖∞ := by
      simpa using (ContinuousMap.norm_coe_le_norm∞ φ x)
    have : |φ x| * Real.exp (R * ‖x‖) ≤ ‖φ‖∞ * Real.exp 1 := by
      exact mul_le_mul hphi hexp (by exact abs_nonneg _) (by exact le_trans (by exact Real.exp_pos _) (le_of_lt (Real.exp_pos _)))
    simpa [mul_assoc, mul_left_comm, mul_comm] using this
  · have : φ x = 0 := by
      exact (not_mem_tsupport_iff.1 hx)
    simp [LOO, this]

end YangMillsGap
