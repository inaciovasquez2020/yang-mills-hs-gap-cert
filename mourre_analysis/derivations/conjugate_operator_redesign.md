Redesign of conjugate operator A

Goal
Construct A such that i[H_E + H_B, A] >= c L_bulk - error

1. Momentum-space generator

Define lattice Fourier transform for electric field:

E_i^a(k) = sum_x e^{-i k·x} E_i^a(x)

Then

H_E = sum_k |E_i^a(k)|^2

Define conjugate operator:

A = 1/2 sum_k (k · ∇_k + ∇_k · k)

acting on Fourier modes.

Then formally:

i[H_E, A] = 2 H_E

since H_E is quadratic and homogeneous of degree 2 in k-space variables.

2. Magnetic term

Magnetic Hamiltonian:

H_B = sum_x B_i^a(x)^2

In Fourier space:

H_B = sum_k |k × A(k)|^2 + nonlinear terms

Quadratic part homogeneous of degree 2 in k.

Thus:

i[H_B_quadratic, A] = 2 H_B_quadratic

Interaction terms produce bounded commutator corrections.

3. Combined bulk term

For quadratic (free) part:

H_0 = H_E + H_B_quadratic

We obtain:

i[H_0, A] = 2 H_0

4. Interaction corrections

Nonlinear magnetic self-interaction and Gauss-law constraint terms:

i[V, A] bounded by C0 uniformly in cutoff if renormalization keeps couplings bounded.

5. Resulting candidate Mourre estimate

i[H_ren, A] = 2 H_ren - i[V, A]

Thus:

i[H_ren, A] >= 2 H_ren - C0

On spectral window I bounded away from 0:

>= c0 H_ren - C0

6. Cutoff dependence

k ∈ [-π/a, π/a]^3

Generator A acts locally in k-space.

No boundary term in real space; finite-volume introduces discrete k grid.

Constants independent of UV cutoff if coupling flow controlled.

Conclusion

Momentum-space dilation avoids real-space boundary divergence and restores positive commutator for quadratic bulk Hamiltonian.

Remaining obstruction:
Control of nonlinear commutator term i[V, A] nonperturbatively.
