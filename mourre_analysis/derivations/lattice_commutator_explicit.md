Lattice Electric Hamiltonian and Dilation Commutator

1. Lattice setup

Let Λ ⊂ ℤ^3 be a finite cubic lattice with spacing a.
Gauge group SU(N).

On each oriented link (x,i):

U_i(x) ∈ SU(N)
E_i^a(x) are electric field operators satisfying:

[E_i^a(x), U_j(y)] = δ_{ij} δ_{xy} (T^a U_i(x))
[E_i^a(x), E_j^b(y)] = i f^{abc} δ_{ij} δ_{xy} E_i^c(x)

The electric Hamiltonian is

H_E = ∑_{x ∈ Λ} ∑_{i=1}^3 ∑_{a} E_i^a(x)^2

2. Dilation generator

Define a lattice dilation derivation acting on link variables:

Formally, for a smooth embedding x ↦ λx,

(A · U_i)(x) = (x · ∇_x) U_i(x)

Since lattice points are discrete, define A via its action on fields:

[A, E_i^a(x)] = i (x · ∇_x E_i^a(x)) + i E_i^a(x)

Interpret ∇_x as forward finite difference:

∇_x^k E_i^a(x) = (E_i^a(x + e_k) - E_i^a(x)) / a

Thus A acts as generator of scaling on electric fields.

3. Commutator computation

Compute i[H_E, A].

First compute for a single site:

i[E_i^a(x)^2, A]
= i E_i^a(x) [E_i^a(x), A] + i [E_i^a(x), A] E_i^a(x)

Using

[E_i^a(x), A] = - i (x · ∇_x E_i^a(x)) - i E_i^a(x)

we get

i[E_i^a(x)^2, A]
= 2 E_i^a(x)^2
+ 2 E_i^a(x) (x · ∇_x E_i^a(x))

Summing over x,i,a:

i[H_E, A]
= 2 H_E
+ 2 ∑_{x,i,a} E_i^a(x) (x · ∇_x E_i^a(x))

4. Discrete divergence identity

Using summation by parts on lattice:

∑_x E(x) (x · ∇ E(x))
= - 1/2 ∑_x |E(x)|^2 div(x)
+ boundary terms

In 3D:

div(x) = 3

Therefore:

2 ∑_x E(x) (x · ∇ E(x))
= - 3 H_E
+ boundary

Thus:

i[H_E, A]
= 2 H_E - 3 H_E + boundary
= - H_E + boundary

5. Boundary error terms

Boundary terms arise from summation by parts:

Boundary ≈ ∑_{x ∈ ∂Λ} x · n(x) |E(x)|^2

Estimate:

|Boundary| ≤ C (|∂Λ| / |Λ|) H_E

For cubic box of side L:

|∂Λ| / |Λ| ≈ O(1/L)

Thus:

i[H_E, A]
= - H_E + O(1/L) H_E

6. Interpretation

In finite volume:

i[H_E, A] ≥ - H_E - C/L H_E

This does not produce positive coercivity.

To obtain positivity, one must instead choose A with opposite sign convention or modify dilation definition.

7. Cutoff dependence

Constants depend on:

a (lattice spacing)
L (box size)

Bulk term independent of a.
Boundary term scales as 1/L.
No UV divergence appears in this commutator.

Conclusion

The naive dilation generator produces

i[H_E, A] ≈ - H_E

not +2 H_E.

Therefore the free electric part alone does not generate a positive Mourre estimate under this choice of A.

A modified conjugate operator must be constructed to obtain positivity.
