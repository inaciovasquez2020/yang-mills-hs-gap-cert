namespace YMFormal
namespace AnchoredClosure

/-!
Conditional candidate proof bodies for unconditional anchored-closure closure.

These bodies are recorded under the explicit assumption that the following names
already exist with compatible types and imported theorems:

  carrier
  merge
  valuation
  merge_carrier_eq
  hessian
  interiorHessian
  boundaryHessian
  hessian_split
  boundaryHessian_posSemidef
  lambdaMin
  rayleigh_ge_lambdaMin
  lambdaMin_add_psd_mono
  mainEnergy
  mainEnergy_empty
  mainEnergy_insert
  StableOnAnchor
  stableOnAnchor_of_spectral_floor
  energy
  step
  stepN
  patchEnergy
  stableDecay
  contractionRate
  contractionRate_lt_one
  sum_step_energy_bound
  contractionRate_bound
  AnchoredCover
  AnchoredPatch
-/

theorem carrier_union_law (P Q : AnchoredPatch) (h : Disjoint (carrier P) (carrier Q)) :
    carrier (merge P Q) = carrier P ∪ carrier Q :=
  merge_carrier_eq P Q h

theorem valuation_on_disjoint_union (P Q : AnchoredPatch)
    (h : Disjoint (carrier P) (carrier Q)) :
    valuation (merge P Q) = valuation P + valuation Q := by
  simp only [valuation, carrier_union_law P Q h]
  exact Finset.sum_union h

theorem valuation_additivity (P Q : AnchoredPatch)
    (h : Disjoint (carrier P) (carrier Q)) :
    valuation (merge P Q) = valuation P + valuation Q :=
  valuation_on_disjoint_union P Q h

theorem hessian_decomposition (P : AnchoredPatch) :
    hessian P = interiorHessian P + boundaryHessian P :=
  hessian_split P

theorem dirichlet_psd (P : AnchoredPatch) :
    0 ≤ boundaryHessian P := by
  apply boundaryHessian_posSemidef

theorem lambdaMin_def (P : AnchoredPatch) (v : EuclideanSpace ℝ _) (hv : v ≠ 0) :
    lambdaMin (hessian P) ≤ inner (hessian P • v) v / inner v v :=
  rayleigh_ge_lambdaMin (hessian P) v hv

theorem lambdaMin_monotone_of_psd_boundary (P : AnchoredPatch) :
    lambdaMin (interiorHessian P) ≤ lambdaMin (hessian P) := by
  rw [hessian_decomposition]
  exact lambdaMin_add_psd_mono (interiorHessian P) (boundaryHessian P)
    (dirichlet_psd P)

theorem decompose_main_energy (cover : AnchoredCover) :
    mainEnergy cover = ∑ P ∈ cover.patches, valuation P := by
  induction cover.patches using Finset.induction with
  | empty => simp [mainEnergy_empty]
  | insert P s hP ih =>
    rw [Finset.sum_insert hP,
        ← ih,
        mainEnergy_insert _ _ hP,
        valuation_additivity _ _ (cover.disjoint_of_mem hP)]

theorem local_stability_from_coercivity (P : AnchoredPatch)
    (hcoer : 0 < lambdaMin (hessian P)) :
    StableOnAnchor P := by
  apply stableOnAnchor_of_spectral_floor
  exact hcoer

theorem spectral_contraction_estimate (cover : AnchoredCover)
    (hcoer : ∀ P ∈ cover.patches, 0 < lambdaMin (hessian P)) :
    ∃ ρ < 1, ∀ u, energy (step cover u) ≤ ρ * energy u := by
  refine ⟨contractionRate cover, contractionRate_lt_one cover hcoer, fun u => ?_⟩
  calc
    energy (step cover u)
        ≤ ∑ P ∈ cover.patches, stableDecay P * patchEnergy P u := by
            apply sum_step_energy_bound
            intro P hP
            exact local_stability_from_coercivity P (hcoer P hP)
    _ ≤ contractionRate cover * energy u := by
            rw [← decompose_main_energy]
            apply contractionRate_bound

theorem spectral_contraction_from_anchored_closure (cover : AnchoredCover)
    (hcoer : ∀ P ∈ cover.patches, 0 < lambdaMin (hessian P)) :
    ∃ ρ < 1, ∀ n u, energy (stepN cover n u) ≤ ρ ^ n * energy u := by
  obtain ⟨ρ, hρ, hstep⟩ := spectral_contraction_estimate cover hcoer
  refine ⟨ρ, hρ, ?_⟩
  intro n u
  induction n with
  | zero =>
      simp [stepN]
  | succ n ih =>
      simp only [stepN]
      calc
        energy (step cover (stepN cover n u))
            ≤ ρ * energy (stepN cover n u) := hstep (stepN cover n u)
        _ ≤ ρ * (ρ ^ n * energy u) := by
            linarith
        _ = ρ ^ (n + 1) * energy u := by
            ring

end AnchoredClosure
end YMFormal
