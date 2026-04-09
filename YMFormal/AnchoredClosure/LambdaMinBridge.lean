import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import YMFormal.AnchoredClosure

namespace YMFormal
namespace AnchoredClosureBridge

variable {AnchoredPatch : Type*}
variable [HasPatchLE AnchoredPatch]
variable [HasVertices AnchoredPatch]
variable [HasHessian AnchoredPatch]
variable [HasLambdaMin AnchoredPatch]

axiom interiorHessian :
  (P : AnchoredPatch) ->
  Matrix (HasVertices.Vertices P) (HasVertices.Vertices P) ℝ

axiom boundaryHessian :
  (P : AnchoredPatch) ->
  Matrix (HasVertices.Vertices P) (HasVertices.Vertices P) ℝ

axiom hessian_decomposition :
  ∀ P : AnchoredPatch,
    HasHessian.hessian P = interiorHessian P + boundaryHessian P

axiom lambdaMin_def :
  (P : AnchoredPatch) -> Prop

axiom boundary_psd :
  (P : AnchoredPatch) -> Prop

end AnchoredClosureBridge
end YMFormal
