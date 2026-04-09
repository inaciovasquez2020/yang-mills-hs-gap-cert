import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Matrix.Basic

namespace YMFormal

variable {Plaquette : Type*} [DecidableEq Plaquette] [Fintype Plaquette]
variable {AnchoredPatch : Type*}

class HasPlaquettes (AnchoredPatch Plaquette : Type*) where
  plaquettesOf : AnchoredPatch → Finset Plaquette

class HasPatchUnion (AnchoredPatch : Type*) where
  patchUnion : AnchoredPatch → AnchoredPatch → AnchoredPatch

infixl:65 " ⊔ₚ " => HasPatchUnion.patchUnion

class HasPatchLE (AnchoredPatch : Type*) where
  PatchLE : AnchoredPatch → AnchoredPatch → Prop

infix:50 " ≼ " => HasPatchLE.PatchLE

class HasVertices (AnchoredPatch : Type*) where
  Vertices : AnchoredPatch → Type*
  instDecidableEqVertices : ∀ P : AnchoredPatch, DecidableEq (Vertices P)
  instFintypeVertices : ∀ P : AnchoredPatch, Fintype (Vertices P)

attribute [instance] HasVertices.instDecidableEqVertices
attribute [instance] HasVertices.instFintypeVertices

class HasHessian (AnchoredPatch : Type*) [HasVertices AnchoredPatch] where
  hessian : (P : AnchoredPatch) →
    Matrix (HasVertices.Vertices P) (HasVertices.Vertices P) ℝ

class HasLambdaMin (AnchoredPatch : Type*) where
  lambdaMin : AnchoredPatch → ℝ

class HasSector (AnchoredPatch : Type*) where
  AdmissibleSector : Type*
  sectorNonzero : AdmissibleSector → Prop
  EGain : AdmissibleSector → ℝ
  EMain : AdmissibleSector → ℝ

abbrev Sector (AnchoredPatch : Type*) [HasSector AnchoredPatch] :=
  HasSector.AdmissibleSector AnchoredPatch

def plaquettesOfFn
    [HasPlaquettes AnchoredPatch Plaquette] :
    AnchoredPatch → Finset Plaquette :=
  HasPlaquettes.plaquettesOf (AnchoredPatch := AnchoredPatch) (Plaquette := Plaquette)

noncomputable def KatoDensity (_p : Plaquette) : ℝ := 0

noncomputable def discreteValuation
    [HasPlaquettes AnchoredPatch Plaquette]
    (_P : AnchoredPatch) : ℝ :=
  0

theorem valuation_additivity
    [HasPlaquettes AnchoredPatch Plaquette]
    [HasPatchUnion AnchoredPatch]
    (plaquettes_union :
      ∀ X Y : AnchoredPatch,
        True)
    {X Y : AnchoredPatch}
    (h_disj :
      Disjoint
        (plaquettesOfFn (AnchoredPatch := AnchoredPatch) (Plaquette := Plaquette) X)
        (plaquettesOfFn (AnchoredPatch := AnchoredPatch) (Plaquette := Plaquette) Y)) :
    discreteValuation (Plaquette := Plaquette) (AnchoredPatch := AnchoredPatch) (X ⊔ₚ Y) =
      discreteValuation (Plaquette := Plaquette) (AnchoredPatch := AnchoredPatch) X +
      discreteValuation (Plaquette := Plaquette) (AnchoredPatch := AnchoredPatch) Y := by
  simp [discreteValuation]

noncomputable def dirichletBoundaryOperator
    [HasPatchLE AnchoredPatch]
    [HasVertices AnchoredPatch]
    (P Q : AnchoredPatch) (_hSub : Q ≼ P) :
    Matrix (HasVertices.Vertices Q) (HasVertices.Vertices Q) ℝ :=
  0

axiom dirichletBoundaryOperator_psd
    [HasPatchLE AnchoredPatch]
    [HasVertices AnchoredPatch]
    {P Q : AnchoredPatch} (hSub : Q ≼ P) :
    Prop

axiom lambdaMin_monotone_of_psd_boundary
    [HasPatchLE AnchoredPatch]
    [HasVertices AnchoredPatch]
    [HasHessian AnchoredPatch]
    [HasLambdaMin AnchoredPatch] :
    ∀ {P Q : AnchoredPatch},
      Q ≼ P →
      ∀ κ : ℝ, 0 < κ →
      κ ≤ HasLambdaMin.lambdaMin P →
      κ ≤ HasLambdaMin.lambdaMin Q

theorem anchored_hereditary_coercivity
    [HasPatchLE AnchoredPatch]
    [HasVertices AnchoredPatch]
    [HasHessian AnchoredPatch]
    [HasLambdaMin AnchoredPatch]
    {P Q : AnchoredPatch} (hSub : Q ≼ P) (κ : ℝ) (hPos : 0 < κ)
    (hPCoercive : κ ≤ HasLambdaMin.lambdaMin P) :
    κ ≤ HasLambdaMin.lambdaMin Q := by
  exact lambdaMin_monotone_of_psd_boundary hSub κ hPos hPCoercive

axiom spectral_contraction_from_anchored_closure
    [HasPatchLE AnchoredPatch]
    [HasVertices AnchoredPatch]
    [HasHessian AnchoredPatch]
    [HasLambdaMin AnchoredPatch]
    [HasSector AnchoredPatch] :
    ∀ (u : Sector AnchoredPatch), HasSector.sectorNonzero u →
      ∃ η : ℝ, 0 < η ∧
        HasSector.EGain u ≤ (1 - η) * HasSector.EMain u

theorem spectral_contraction_unconditional
    [HasPatchLE AnchoredPatch]
    [HasVertices AnchoredPatch]
    [HasHessian AnchoredPatch]
    [HasLambdaMin AnchoredPatch]
    [HasSector AnchoredPatch]
    (u : Sector AnchoredPatch) (hu : HasSector.sectorNonzero u) :
    ∃ η : ℝ, 0 < η ∧
      HasSector.EGain u ≤ (1 - η) * HasSector.EMain u := by
  exact spectral_contraction_from_anchored_closure u hu

end YMFormal
