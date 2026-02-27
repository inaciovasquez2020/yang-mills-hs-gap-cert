import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.NormedSpace.Spectrum
import Mathlib.Analysis.NormedSpace.OperatorNorm

namespace YangMillsGap

open scoped ComplexConjugate

variable {𝕜 : Type} [IsROrC 𝕜]
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

theorem selfAdjoint_not_mem_spectrum_zero_of_isBoundedBelow
  (T : E →L[𝕜] E)
  (hSA : IsSelfAdjoint T)
  (hbb : IsBoundedBelow T) :
  (0:𝕜) ∉ spectrum 𝕜 T := by
  classical
  -- After running scratch/BoundedBelowChecks.lean, replace the next 5 lines
  -- with the exact lemma names that exist in your Mathlib checkout.
  --
  -- Strategy:
  --   1) closed range from hbb
  --   2) ker(T) = ⊥ from hbb
  --   3) range(T) ⊥ = ker(T†), and for selfadjoint ker(T†)=ker(T)=⊥ ⇒ range dense
  --   4) dense + closed ⇒ range = ⊤ ⇒ surjective
  --   5) bounded below + surjective ⇒ isUnit ⇒ 0 ∉ spectrum
  --
  -- Keep this file as the single compilation target; fill names from #check output.
  admit

end YangMillsGap
