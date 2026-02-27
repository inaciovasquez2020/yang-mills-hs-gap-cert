import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.NormedSpace.OperatorNorm

open scoped ComplexConjugate

variable {𝕜 : Type} [IsROrC 𝕜]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable (T : E →L[𝕜] E) (a : 𝕜)

#check spectrum
#check spectrum_add
#check spectrum_sub
#check spectrum_add_scalar
#check spectrum_sub_scalar
#check spectrum_add_scalar_eq
#check spectrum_sub_scalar_eq
