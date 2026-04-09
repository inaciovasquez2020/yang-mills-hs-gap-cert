# lambdaMin Monotonicity under PSD Boundary — Proof Shell

## Target
Replace `axiom lambdaMin_monotone_of_psd_boundary` in `YMFormal/AnchoredClosure.lean` by a theorem.

## First missing lemma
```lean
lemma hessian_decomposition
    (P : AnchoredPatch) :
    hessian P = interiorHessian P + boundaryHessian P
Reduction chain
hessian_decomposition
→ dirichlet_psd
→ lambdaMin_def
→ lambdaMin_monotone_of_psd_boundary
Obligations
Define interiorHessian and boundaryHessian.
Prove exact Hessian splitting.
Prove 0 ≤ boundaryHessian in PSD order.
Unfold lambdaMin through the Rayleigh quotient.
Conclude monotonicity under PSD boundary addition.
