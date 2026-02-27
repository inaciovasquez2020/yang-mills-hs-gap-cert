# Hybrid Solve (WIF + PSD + IRI)

Goal: obtain Mass Gap from three non-equivalent inputs.

Definitions (Λ = UV cutoff; H_Λ = physical Hamiltonian; P_{≤E} = 1_{[0,E]}(H_Λ)).

1) WIF (Weak IR Flow)
   || P_{≤E} (∂_{log Λ} H_Λ) P_{≤E} || ≤ C/(log Λ)^{1+ε} + η_Λ(E),
   with η_Λ(E) → 0 as E → 0 (uniformly in Λ on bounded ranges).

2) PSD (Polynomial Spectral Density near 0)
   ρ_Λ(E) ≤ C E^α for E small, with α>0 independent of Λ.
   Equivalently via Tauberian: Tr(e^{-t H_Λ}) ≤ C t^{-(α+1)} for t large.

3) IRI (IR Irreducibility of Interaction)
   There exist c>0, β>0 such that for all sufficiently small E>0,
   || P_{≤E} H_int(Λ) P_{≤E} || ≥ c E^β.
   (Meaning: low-energy sector cannot become asymptotically non-interacting.)

Claim (Hybrid Implication Target):
   WIF + PSD + IRI  ⇒  ∃ m>0 s.t. inf_{ψ ⟂ Ω} <ψ,H_Λ ψ>/||ψ||^2 ≥ m for all large Λ.

Counterexample sanity check:
   Free massless theory satisfies WIF + PSD but fails IRI, hence no contradiction.
