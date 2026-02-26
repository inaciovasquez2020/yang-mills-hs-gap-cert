Stress tests for C2 commutator form boundedness

Target condition C2
|<ψ, i[V, A] ψ>| <= a_A <ψ, H0 ψ> + b_A ||ψ||^2
with a_A < 1 uniform in cutoff.

Conjugate operator
A is momentum-space dilation generator.

Interaction structure
V = g V3 + g^2 V4
V3 is cubic term with one derivative
V4 is quartic term without derivatives

Failure modes to target

F1 High-frequency concentration
Choose ψ localized near |k| = Λ_UV.
Then A amplifies derivatives in k.
Test whether <ψ, i[V, A] ψ> grows faster than <ψ, H0 ψ>.

F2 Mixed-scale resonance
Choose ψ supported on k1 small, k2,k3 near cutoff with momentum conservation.
Test whether cubic vertex creates large commutator contribution from k·∇_k acting on the vertex kernel.

F3 Infrared delocalization
Choose ψ supported near k = 0 with large spatial support.
Test whether commutator fails due to IR growth of effective coupling.

F4 Coupling drift amplification
Assume g(Λ) increases along flow.
Test whether i[V, A] picks up explicit g'(Λ) terms under RG-transported A.

Candidate families

CAND1 UV shell packet
ψ_Λ with support on |k| in [Λ(1-ε), Λ].

CAND2 UV-IR pair packet
ψ with two-scale support: one mode at k ~ 0 and one mode at k ~ Λ.

CAND3 Flux-tube proxy
ψ_R corresponding to long tube length R, fixed cross section, normalized L(ψ_R)=1.

Diagnostics

D1 Ratio test
R(ψ) = |<ψ, i[V, A] ψ>| / <ψ, H0 ψ>

C2 requires:
R(ψ) <= a_A + b_A / <ψ, H0 ψ>

If there exists sequence ψ_n with R(ψ_n) -> ∞, C2 fails.

Deliverable
For each candidate, attempt to estimate scaling of numerator and denominator in Λ and R.
