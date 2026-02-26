CAND3 Flux-tube / long-support scaling estimate for C2

Target condition
|<psi, i[V, A] psi>| <= a_A <psi, H0 psi> + b_A ||psi||^2
uniformly in cutoff.

Candidate family

Let psi_R be a gauge-invariant state representing a flux tube
of fixed transverse radius r0 and length R.

Assume:
- Energy density per unit length = σ (string tension scale)
- Total quadratic energy:
  <psi_R, H0 psi_R> ~ σ R

Normalize so that:
<psi_R, H0 psi_R> ~ 1

Thus field amplitudes scale as:
A ~ R^{-1/2}

Magnetic field gradients localized transversely,
longitudinal variation negligible.

Interaction structure

Cubic term V3 contains one derivative.
For flux tube:
- Transverse derivatives O(1/r0)
- Longitudinal derivatives O(1/R)

Dominant derivative scale fixed by transverse size.

Thus cubic expectation scaling:

<psi_R, g V3 psi_R>
~ g * (field amplitude)^3 * Volume_support
~ g * (R^{-3/2}) * (R)
= g / sqrt(R)

Commutator with A

A acts as generator of scaling.
On spatially extended configuration,
dominant action comes from longitudinal coordinate scaling.

Heuristic:
i[V3, A] scales same as V3 in magnitude.

Thus:

<psi_R, i[g V3, A] psi_R>
~ g / sqrt(R)

Quartic term:

<psi_R, g^2 V4 psi_R>
~ g^2 * (R^{-2}) * R
= g^2 / R

Denominator

<psi_R, H0 psi_R> ~ 1 (by normalization)

Ratio

R(psi_R)
~ g / sqrt(R) + g^2 / R

As R -> infinity:

R(psi_R) -> 0.

Preliminary conclusion

Long spatial support with fixed energy density
does NOT break C2 under naive scaling.

Potential loopholes

1. Nonlocal Coulomb contributions
   If Gauss-law projection induces long-range interaction terms,
   numerator may acquire R-independent contribution.

2. Infrared enhancement of effective coupling
   If g_eff(R) grows with R (confinement regime),
   scaling estimate changes.

3. Collective coherent enhancement
   If cubic correlations align coherently along length,
   amplitude may scale like R^0 instead of R^{-1/2}.

Refined failure condition

To violate C2 via CAND3 one needs:

g_eff(R) ~ sqrt(R)
or
correlation growth ~ R^{1/2}

Neither arises from naive dimensional analysis.

Status

Under bounded effective coupling and absence of IR coupling blow-up,
flux-tube states do not violate C2.

Therefore C2 appears dimensionally consistent
in UV, mixed-scale, and long-support regimes.

Remaining obstruction reduces to:

Nonperturbative control of effective coupling growth
in the infrared confinement regime.
