# Spectral Contraction from Anchored Closure — Proof Shell

## Target
Replace `axiom spectral_contraction_from_anchored_closure` in `YMFormal/AnchoredClosure.lean` by a theorem.

## First missing lemma
```lean
lemma local_stability_from_coercivity
    (P : AnchoredPatch)
    (hcoer : 0 < lambdaMin (hessian P)) :
    StableOnAnchor P
Reduction chain
lambdaMin_monotone_of_psd_boundary
→ local_stability_from_coercivity
→ spectral_contraction_estimate
→ spectral_contraction_from_anchored_closure
Obligations
Define StableOnAnchor.
Convert positive spectral floor into anchored coercive decay.
Derive the one-step contraction estimate.
Iterate contraction along anchored closure.
Conclude spectral_contraction_from_anchored_closure.
