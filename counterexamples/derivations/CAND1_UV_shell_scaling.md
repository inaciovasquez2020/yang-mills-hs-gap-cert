CAND1 UV shell packet scaling estimate for C2

Target condition
|<psi, i[V, A] psi>| <= a_A <psi, H0 psi> + b_A ||psi||^2
with a_A < 1 uniform in cutoff.

Model assumptions
Momentum-space representation on a 3D torus or periodic box.
A is momentum dilation generator acting as (k·∇_k + ∇_k·k)/2 on mode variables.
H0 = H_E + H_B_quadratic controls one derivative in space through the magnetic term.

Candidate family CAND1
psi_Λ is a normalized state concentrated on a thin UV shell:
support of modes satisfies |k| in [Λ(1-ε), Λ] with 0 < ε << 1 fixed.

Define UV shell width
ΔΛ = ε Λ
Shell volume in 3D scales as Vol_shell ~ Λ^2 ΔΛ ~ ε Λ^3.

Heuristic scaling for quadratic energy
On the UV shell, the quadratic Hamiltonian density scales like:
H0 mode weight ~ |E(k)|^2 + |k|^2 |A(k)|^2.

If psi_Λ is chosen so that its spectral weight is concentrated at |k| ~ Λ, then:
<psi_Λ, H0 psi_Λ> ~ Λ^2 <psi_Λ, N_A psi_Λ> + <psi_Λ, N_E psi_Λ>
where N_A, N_E are mode occupation weights.
For packets with comparable electric and magnetic contributions, treat:
<psi_Λ, H0 psi_Λ> ~ c0 Λ^2

This normalization is consistent with fixing L(psi_Λ)=1 by rescaling amplitude, in which case c0 is O(1).

Interaction term and commutator structure
Write V = g V3 + g^2 V4.
V3 carries one derivative in position space, hence one factor of momentum in Fourier kernels.
V4 carries no derivative factor.

Under A, commutator acts on momentum dependence of kernels and on fields.
Dominant UV scaling comes from k·∇_k acting on kernels.

Cubic term scaling
Represent V3 schematically as:
V3 ~ sum_{k1+k2+k3=0} K3(k1,k2,k3) A(k1) A(k2) A(k3)
with K3 homogeneous of degree 1 in momenta at high frequency.

Then k·∇_k applied to K3 yields:
(k·∇)K3 ~ K3 in UV, up to constants.

Thus i[V3, A] is expected to be of the same scaling degree as V3.

Assume UV shell support enforces |k_i| ~ Λ whenever contributing, so:
K3 ~ O(Λ)

Hence magnitude estimate:
|<psi_Λ, i[g V3, A] psi_Λ>| ~ g Λ T3(psi_Λ)

where T3(psi_Λ) is a dimensionless triple-mode correlation amplitude.

Quartic term scaling
V4 schematically:
V4 ~ sum_{k1+...+k4=0} K4(k1,...,k4) A A A A
with K4 homogeneous degree 0 in UV.

Then:
|<psi_Λ, i[g^2 V4, A] psi_Λ>| ~ g^2 T4(psi_Λ)
dimensionless.

Ratio diagnostic
Define
R(psi_Λ) = |<psi_Λ, i[V, A] psi_Λ>| / <psi_Λ, H0 psi_Λ>.

Using <H0> ~ c0 Λ^2:

R(psi_Λ) ~ (g Λ T3 + g^2 T4) / (c0 Λ^2)
= (g T3)/(c0 Λ) + (g^2 T4)/(c0 Λ^2)

Conclusion from UV scaling alone
If g is bounded independently of Λ and T3, T4 remain O(1) uniformly for this family,
then
R(psi_Λ) -> 0 as Λ -> infinity.

Therefore CAND1 does not break C2 purely by UV scaling.

Failure mode refinement
To violate C2 via CAND1, one would need T3(psi_Λ) or T4(psi_Λ) to grow with Λ fast enough to offset 1/Λ or 1/Λ^2 decay.
That would require:
either large occupation growth in UV shell with fixed <H0>,
or coherent amplification in triple correlations incompatible with the chosen normalization.

Checklist for a real violation attempt
1. Construct psi_Λ with fixed <H0> and growing UV occupation number.
2. Show cubic correlation T3 grows at least like Λ.
3. Verify gauge-invariant constraint does not suppress such states.

Status
CAND1 UV shell packet is not an immediate obstruction to C2 under bounded coupling and controlled correlations.
