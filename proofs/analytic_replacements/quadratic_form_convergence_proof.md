# Analytic Quadratic Form Convergence Skeleton

## Statement

Let

q_L(f) = <f, \widetilde H_L f>

with

\widetilde H_L = L^2 H_L.

For cylinder functions f in a common dense domain D_fin, prove

q_L(f) -> q_infty(f)

and

sup_L q_L(f) < infinity.

## Proof skeleton

1. Let D_fin be finitely supported cylinder functions on lattice gauge fields.
2. For fixed f in D_fin, there exists L_0(f) such that the support of f is
   contained in every block decomposition for L >= L_0(f).
3. For L >= L_0(f), the local action of \widetilde H_L on f stabilizes.
4. Hence

   \widetilde H_L f = H_loc f

   for all sufficiently large L.

5. Define

   q_infty(f) = <f, H_loc f>.

6. Then pointwise convergence follows:

   q_L(f) -> q_infty(f).

7. Uniform boundedness follows because the local operator H_loc depends only on
   the finite support of f, hence

   q_L(f) <= C(f)

   for all large L, and finitely many small L are absorbed into the constant.

8. Apply Kato form convergence to deduce

   \widetilde H_L -> H_infty

   in strong resolvent sense.

## Remaining obligation

Identify H_loc with the physical Yang-Mills Hamiltonian on D_fin.
