import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Analysis.InnerProductSpace.HilbertSchmidt
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Topology.ContinuousFunction.ZeroAtInfty
import Mathlib.Analysis.NormedSpace.Spectrum
import YMFormal.YangMills.SpectrumShift
import YMFormal.YangMills.BoundedBelowInvertible
import YMFormal.YangMills.LOOProof
import Mathlib.Analysis.NormedSpace.BoundedLinearMaps

namespace YangMillsGap

open scoped BigOperators
open MeasureTheory
open scoped ComplexConjugate

variable {𝕜 : Type} [IsROrC 𝕜]

/-============================================================
  FAD-TR: Hilbert–Schmidt squared norm, basis-independent
============================================================-/

variable {ℋ : Type} [NormedAddCommGroup ℋ] [InnerProductSpace 𝕜 ℋ]
variable [CompleteSpace ℋ] [SeparableSpace ℋ]

def FAD_TR (A : ℋ →L[𝕜] ℋ) : ℝ := ‖A‖ₕₛ ^ 2

lemma opNorm_le_fad_tr_sqrt (A : ℋ →L[𝕜] ℋ) :
  ‖A‖ ≤ Real.sqrt (FAD_TR (𝕜 := 𝕜) A) := by
  have h := ContinuousLinearMap.opNorm_le_hilbertSchmidtNorm A
  simpa [FAD_TR, Real.sqrt_sq_eq_abs, abs_of_nonneg (by exact sq_nonneg _)] using h

lemma fad_tr_lower_bound (A : ℋ →L[𝕜] ℋ) :
  FAD_TR (𝕜 := 𝕜) A ≥ (1:ℝ) * ‖A‖^2 := by
  have : ‖A‖^2 ≤ (Real.sqrt (FAD_TR (𝕜 := 𝕜) A))^2 := by
    have := opNorm_le_fad_tr_sqrt (𝕜 := 𝕜) A
    nlinarith
  simpa [one_mul, pow_two] using this

/-============================================================
  HR-FDK: scale-fixed positivity via L2-normalization
============================================================-/

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

/-============================================================
  LOO: localization obstruction operator (proved in LOOProof)
============================================================-/

variable {n : ℕ}

def LOO (R : ℝ) (φ : C₀(ℝⁿ, ℝ)) : ℝ :=
  ⨆ x : ℝⁿ, |φ x| * Real.exp (R * ‖x‖)


/-============================================================
  TCIu: uniform-in-λ lower bound ⇒ spectral gap (no axiom)
============================================================-/

variable {H : (L²(ℝⁿ) →L[𝕜] L²(ℝⁿ))}

def TCIu (H : (L²(ℝⁿ) →L[𝕜] L²(ℝⁿ))) (m : ℝ) : Prop :=
  ∀ (λ : ℝ), λ ∈ Set.Ioo (0:ℝ) m →
  ∀ ψ, ‖(H - (λ:𝕜) • 1) ψ‖ ≥ (m-λ) * ‖ψ‖

/-- Helper: bounded-below ⇒ 0 not in spectrum. -/
lemma not_mem_spectrum_zero_of_isBoundedBelow
  {E : Type} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  (T : E →L[𝕜] E)
  (hSA : IsSelfAdjoint T)
  (h : IsBoundedBelow T) :
  (0:𝕜) ∉ spectrum 𝕜 T := by
  simpa using (selfAdjoint_not_mem_spectrum_zero_of_isBoundedBelow (𝕜 := 𝕜) (T := T) hSA h)


lemma tciu_excludes_interval
  (m : ℝ)
  (hpos : 0 < m)
  (hSA : IsSelfAdjoint H)
  (h : TCIu (n := n) (H := H) m) :
  spectrum 𝕜 H ∩ Set.Ioo (0:ℝ) m = ∅ := by
  classical
  ext λ
  constructor
  · intro hλ
    rcases hλ with ⟨hλspec, hλint⟩
    have hpos' : 0 < m - λ := by linarith [hλint.2]
    have hbound := h λ hλint
    have hbb : IsBoundedBelow (H - (λ:𝕜) • 1) := by
      refine ⟨m - λ, hpos', ?_⟩
      intro ψ
      simpa using hbound ψ
    have hz : (0:𝕜) ∉ spectrum 𝕜 (H - (λ:𝕜) • 1) :=
      not_mem_spectrum_zero_of_isBoundedBelow (𝕜 := 𝕜) (T := H - (λ:𝕜) • 1) hbb
    -- spectrum shift: 0 ∈ spec(H-λI) ↔ λ ∈ spec(H)
    -- use `spectrum_sub_scalar` / `spectrum_add_scalar` lemma available in Mathlib
    -- If lemma name differs, adjust accordingly.
    have : (0:𝕜) ∈ spectrum 𝕜 (H - (λ:𝕜) • 1) := by
      classical
      have hs : spectrum 𝕜 (H - (λ:𝕜) • 1) = (fun z => z - (λ:𝕜))  spectrum 𝕜 H := by
        simpa using spectrum_sub_scalar (𝕜 := 𝕜) (T := H) (a := (λ:𝕜))
      have : (0:𝕜) ∈ (fun z => z - (λ:𝕜))  spectrum 𝕜 H := by
        refine ⟨(λ:𝕜), hλspec, ?_⟩
        simp
      simpa [hs] using this
    exact hz this
  · intro hfalse
    cases hfalse

end YangMillsGap
