import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Analysis.InnerProductSpace.HilbertSchmidt
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Topology.ContinuousFunction.ZeroAtInfty
import Mathlib.Analysis.NormedSpace.Spectrum

namespace YangMillsGap

open scoped BigOperators
open MeasureTheory

variable {𝕜 : Type} [IsROrC 𝕜]
variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace 𝕜 ℋ]
variable [CompleteSpace ℋ] [SeparableSpace ℋ]

def FAD_TR (A : ℋ →L[𝕜] ℋ) : ℝ := ‖A‖ₕₛ ^ 2

lemma opNorm_le_fad_tr_sqrt (A : ℋ →L[𝕜] ℋ) :
  ‖A‖ ≤ Real.sqrt (FAD_TR (𝕜 := 𝕜) A) := by
  have h := ContinuousLinearMap.opNorm_le_hilbertSchmidtNorm A
  simpa [FAD_TR, Real.sqrt_sq_eq_abs, abs_of_nonneg (by exact sq_nonneg _)] using h

variable {X : Type} [MeasurableSpace X] (μ : Measure X)

def HR_FDK (k : ℕ) (f : X → ℝ) : ℝ :=
  Real.sqrt (∫ x, (f x)^2 ∂μ) + (1 / (k.succ : ℝ)) * ‖f‖∞

lemma hr_fdk_gap_of_L2norm_one (f : X → ℝ)
  (hL2 : Real.sqrt (∫ x, (f x)^2 ∂μ) = 1) :
  ∃ m > 0, ∀ k, HR_FDK (μ := μ) k f ≥ m := by
  refine ⟨1, by norm_num, ?_⟩
  intro k
  have hpos : 0 ≤ (1 / (k.succ : ℝ)) * ‖f‖∞ :=
    mul_nonneg (one_div_nonneg.mpr (by exact_mod_cast Nat.succ_pos k))
               (norm_nonneg _)
  have : HR_FDK (μ := μ) k f ≥ Real.sqrt (∫ x, (f x)^2 ∂μ) :=
    by simpa [HR_FDK] using le_add_of_nonneg_right hpos
  simpa [hL2] using this

variable {n : ℕ}

def LOO (R : ℝ) (φ : C₀(ℝⁿ, ℝ)) : ℝ :=
  ⨆ x : ℝⁿ, |φ x| * Real.exp (R * ‖x‖)

axiom loo_excludes_ir_exp
  (R : ℝ) (hR : 0 < R) (φ : C₀(ℝⁿ, ℝ))
  (hlocal : tsupport φ ⊆ Metric.ball (0:ℝⁿ) (R⁻¹)) :
  LOO (n := n) R φ ≤ Real.exp 1 * ‖φ‖∞

open scoped ComplexConjugate

variable {H : (L²(ℝⁿ) →L[𝕜] L²(ℝⁿ))}

def TCIu (H : (L²(ℝⁿ) →L[𝕜] L²(ℝⁿ))) (m : ℝ) : Prop :=
  ∀ (λ : ℝ), λ ∈ Set.Ioo (0:ℝ) m →
  ∀ ψ, ‖(H - (λ:𝕜) • 1) ψ‖ ≥ (m-λ) * ‖ψ‖

axiom tciu_implies_spectral_gap
  (m : ℝ) (hpos : 0 < m) (hSA : IsSelfAdjoint H)
  (h : TCIu (n := n) H m) :
  spectrum 𝕜 H ∩ Set.Ioo (0:ℝ) m = ∅

end YangMillsGap
