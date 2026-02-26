CAND2 UV–IR resonance scaling estimate for C2

Target condition
|<psi, i[V, A] psi>| <= a_A <psi, H0 psi> + b_A ||psi||^2
uniformly in cutoff.

Candidate structure

Construct psi_Λ with bimodal momentum support:

- One cluster of modes in IR region: |k| <= μ  with μ fixed independent of Λ.
- One cluster of modes in UV shell: |k| in [Λ(1-ε), Λ].

Momentum conservation in cubic vertex:
k1 + k2 + k3 = 0.

UV–IR mixing configuration:
k1 ~ Λ
k2 ~ -Λ + q
k3 ~ -q
with |q| <= μ.

Thus two high modes nearly cancel, leaving small IR residual.

Quadratic energy scaling

H0 contribution:

UV modes contribute ~ Λ^2 amplitude.
IR modes contribute ~ μ^2 amplitude.

Normalize psi_Λ so that:

<psi_Λ, H0 psi_Λ> ~ O(1)

This forces UV occupation amplitude ~ 1/Λ.

Interaction commutator numerator

Cubic vertex kernel in UV–IR channel:

K3(k1,k2,k3) homogeneous degree 1 in momenta.
Dominant contribution ~ O(Λ).

Under dilation generator A:

k·∇_k acting on K3 produces O(Λ).

Thus:

<psi_Λ, i[g V3, A] psi_Λ> ~ g Λ * (amplitude factors).

Amplitude structure

Each UV mode amplitude scales ~ 1/Λ.
IR mode amplitude independent of Λ (since μ fixed).

Cubic expectation roughly scales as:

g * Λ * (1/Λ)*(1/Λ)*(1)
= g / Λ.

Therefore numerator ~ g / Λ.

Denominator

<psi_Λ, H0 psi_Λ> ~ O(1).

Ratio

R(psi_Λ) ~ g / Λ.

As Λ -> infinity, R -> 0.

Quartic term

V4 has no derivative.
UV–IR mixing contributes at most:

g^2 * (1/Λ^2) scaling.

Thus quartic term also suppressed.

Conclusion

UV–IR resonance does not generate divergence in C2 ratio under:

- bounded coupling g,
- normalization fixing quadratic energy,
- absence of anomalous correlation growth.

Failure condition refinement

To violate C2 via CAND2 one would need:

1. Coherent phase alignment producing enhancement ~ Λ.
2. Breakdown of H0 control in mixed-scale states.
3. Nonperturbative growth of effective vertex beyond naive homogeneity.

None of these arise at naive scaling level.

Status

CAND2 UV–IR resonance does not immediately break C2 under bounded coupling.

Remaining dangerous candidate:
Long spatial support / flux-tube type states (CAND3),
where denominator may scale differently than numerator.
