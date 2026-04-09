# valuation_additivity

Status: CONDITIONAL

Target statement:
- Replace `axiom valuation_additivity` in `YMFormal/AnchoredClosure.lean`
  by a theorem proving additivity of `discreteValuation` under the chosen
  patch-union semantics.

Current weakest sufficient requirement:
- Introduce an explicit union law for plaquette carriers compatible with the
  repository's available `Finset` interface.
- Then prove the theorem from that law.

Required replacement object:
- theorem valuation_additivity

Blocking object:
- no repository-stable explicit carrier law for
  `plaquettesOfFn (X ⊔ₚ Y)` has been formalized yet.
