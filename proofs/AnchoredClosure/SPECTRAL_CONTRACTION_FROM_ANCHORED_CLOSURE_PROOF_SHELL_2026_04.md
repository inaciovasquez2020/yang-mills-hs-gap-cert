# spectral_contraction_from_anchored_closure

Status: CONDITIONAL

Target statement:
- Replace `axiom spectral_contraction_from_anchored_closure` in
  `YMFormal/AnchoredClosure.lean` by a theorem deriving spectral contraction
  from the anchored closure interface.

Current weakest sufficient requirement:
- Formalize a repository-stable bridge from anchored hereditary coercivity and
  anchored valuation control to the quantitative contraction inequality.
- Then instantiate that bridge for `HasSector.EGain` and `HasSector.EMain`.

Required replacement object:
- theorem spectral_contraction_from_anchored_closure

Blocking object:
- no repository-stable theorem yet derives the existence of
  `η > 0` with
  `HasSector.EGain u ≤ (1 - η) * HasSector.EMain u`
  from the current anchored closure scaffold.
