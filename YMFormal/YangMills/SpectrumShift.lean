import Mathlib.Analysis.NormedSpace.Spectrum
import Mathlib.Analysis.NormedSpace.OperatorNorm

namespace YangMillsGap

open scoped ComplexConjugate

variable {𝕜 : Type} [IsROrC 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable (T : E →L[𝕜] E) (a : 𝕜)

theorem spectrum_shift_sub_scalar :
  (a ∈ spectrum 𝕜 T) ↔ ((0:𝕜) ∈ spectrum 𝕜 (T - a • (1 : E →L[𝕜] E))) := by
  -- prefer a direct lemma if present:
  -- try: `by simpa using (spectrum_sub_scalar_eq (𝕜 := 𝕜) (T := T) a)`
  -- fallback via add:
  -- spectrum(T - aI) = spectrum(T + (-a)I) = spectrum(T) + (-a)
  classical
  -- EDIT THIS LINE after `SpectrumChecks.lean` tells you the exact lemma name:
  simpa [sub_eq_add_neg] using (by
    -- placeholder, replace with the lemma you found:
    exact Iff.rfl
  )

end YangMillsGap
