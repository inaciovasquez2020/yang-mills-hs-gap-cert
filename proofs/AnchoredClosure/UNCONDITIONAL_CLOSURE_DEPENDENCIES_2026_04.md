# Unconditional Closure Dependencies

Status: CONDITIONAL

To replace the three remaining axioms in `YMFormal/AnchoredClosure.lean`, the following repository-stable theorem objects are required.

## 1. Carrier algebra
- `carrier : AnchoredPatch → Finset Plaquette`
- `carrier_union_law :
    ∀ X Y, carrier (X ⊔ₚ Y) = carrier X ∪ carrier Y`

These are the missing inputs for replacing:
- `axiom valuation_additivity`

## 2. Anchored Hessian compression and PSD boundary
- `hessian_decomposition :
    ∀ {P Q : AnchoredPatch}, Q ≼ P →
      Hessian Q = Π_Q * Hessian P * Π_Q + B_operator P Q`
- `dirichlet_psd :
    ∀ {P Q : AnchoredPatch}, Q ≼ P →
      PosSemidef (B_operator P Q)`

These are the missing inputs for replacing:
- `axiom lambdaMin_monotone_of_psd_boundary`

## 3. Variational/eigenvalue and energy bridge
- `lambdaMin_def :
    λ_min A = inf {⟪v, A v⟫ | ‖v‖ = 1}`
- `decompose_main_energy :
    ∀ u, E_main u = ∑ P in patchesOf u, nu P`
- `local_stability_from_coercivity :
    ∀ P, λ_min (Hessian P) ≥ κ → κ > 0 →
      ∃ η_P > 0, E_gain_local P ≤ (1 - η_P) * nu P`

These are the missing inputs for replacing:
- `axiom spectral_contraction_from_anchored_closure`

## Gate
Unconditional closure is reached only after:
1. all three axioms are replaced by theorems;
2. all status/manifests/reports show `conditional_axioms_remaining = 0`;
3. the unconditional gate passes.
