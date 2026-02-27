# Hybrid implication (Conditional)

Assume:
  WIF: || P_{≤E} (∂_{log Λ} H_Λ) P_{≤E} || ≤ C/(log Λ)^(1+ε) + η_Λ(E), with η_Λ(E)→0 as E→0.
  IRI: || P_{≤E} H_int(Λ) P_{≤E} || ≥ c E^β for E small.
  RIB: || P_{≤E} ( ∂_{log Λ} H_Λ + κ H_int(Λ) ) P_{≤E} || ≤ r_{Λ,E},
       r_{Λ,E} = O((log Λ)^-(1+ε)) + o(E^γ).

Then:
  ∃ m>0, Λ0 such that ∀ Λ≥Λ0,
    inf_{ψ ⟂ Ω} <ψ,H_Λ ψ>/||ψ||^2 ≥ m.

Proof (inequalities):
  κ||P_{≤E}H_intP_{≤E}|| ≤ ||P_{≤E}(∂_{logΛ}H_Λ)P_{≤E}|| + r_{Λ,E}
                        ≤ C/(logΛ)^(1+ε) + η_Λ(E) + r_{Λ,E}.
  Let Λ→∞ and then E→0: RHS→0, hence LHS→0.
  Contradicts IRI unless P_{≤E} is vacuum-only for all E≤m, giving the gap m.
