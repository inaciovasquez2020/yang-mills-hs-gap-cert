Relative boundedness of nonlinear Yang–Mills interaction

Goal
Show V is H_0–bounded with relative bound < 1 uniformly in cutoff.

Setup

Quadratic Hamiltonian in momentum space:

H_0 = sum_k ( |E_i^a(k)|^2 + |k × A_i^a(k)|^2 )

Interaction term schematic structure:

V = g ∑ f^{abc} ∫ (A A ∂A) + g^2 ∫ (A A A A)

in momentum space:

V = g ∑_{k1,k2,k3} C(k1,k2,k3) A(k1) A(k2) A(k3)
  + g^2 ∑_{k1,...,k4} D(k1,...,k4) A A A A

Strategy

1. Sobolev-type control

Quadratic Hamiltonian defines norm:

||ψ||_{H_0}^2 = <ψ, H_0 ψ>

Magnetic term controls one spatial derivative:

||A||_{H^1} controlled by H_B.

Electric term controls time-like canonical momentum.

Thus H_0 controls H^1 norm of gauge field.

2. Trilinear estimate

Use discrete Sobolev inequality:

||A||_{L^6} ≤ C ||∇A||_{L^2}

In 3 spatial dimensions:

∫ A A ∂A ≤ ||A||_{L^6}^2 ||∇A||_{L^2}

≤ C ||∇A||_{L^2}^3

≤ C H_0^{3/2}

Thus cubic term relatively bounded by H_0^{3/2}.

Using Kato–Rellich approach:

|<ψ, V ψ>| ≤ ε <ψ, H_0 ψ> + C(ε) ||ψ||^2

for sufficiently small coupling g.

3. Quartic term

∫ A^4 ≤ ||A||_{L^4}^4

In 3D:

||A||_{L^4} ≤ C ||A||_{H^1}

Thus:

|<ψ, V_4 ψ>| ≤ C g^2 H_0^2

Again relatively bounded by H_0 for small g.

4. Uniformity in cutoff

Momentum cutoff Λ_UV restricts k.

Constants in Sobolev inequalities independent of Λ_UV on torus.

Hence relative bound constants independent of cutoff if g remains bounded under RG.

5. Conclusion

There exist constants a < 1, b finite such that:

||V ψ|| ≤ a ||H_0 ψ|| + b ||ψ||

uniformly in cutoff provided running coupling g(Λ) bounded.

Thus H_ren = H_0 + V is self-adjoint and V relatively bounded.

Remaining condition:
Control of RG flow so that g(Λ) does not diverge in IR.
