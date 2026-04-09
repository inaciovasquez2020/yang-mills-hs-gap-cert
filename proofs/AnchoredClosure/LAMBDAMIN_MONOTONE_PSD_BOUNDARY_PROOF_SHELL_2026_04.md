# lambdaMin_monotone_of_psd_boundary

Status: CONDITIONAL

Target statement:
- Replace `axiom lambdaMin_monotone_of_psd_boundary` in
  `YMFormal/AnchoredClosure.lean` by a theorem proving hereditary coercivity
  under a precise PSD boundary perturbation/compression law.

Current weakest sufficient requirement:
- Formalize an explicit operator comparison/compression statement for the
  anchored Hessian layer.
- Then derive monotonicity of `HasLambdaMin.lambdaMin`.

Required replacement object:
- theorem lambdaMin_monotone_of_psd_boundary

Blocking object:
- no repository-stable theorem yet identifies the induced-subpatch Hessian as a
  compression plus PSD boundary correction.
