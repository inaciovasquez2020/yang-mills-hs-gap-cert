# Analytic Localization Theorem Skeleton

## Statement

Assume admissible cycle supports project to coordinate interval families
I_i^{(k)} on each axis k = 1,...,d and these interval families have pairwise
overlap.

Then there exists v in the lattice such that

supp(Phi(gamma)) subset B_R(v).

## Proof skeleton

1. For each coordinate k, project each local support S_i onto the kth axis.
2. Obtain intervals I_i^{(k)}.
3. Pairwise overlap of supports implies pairwise overlap of all projected intervals.
4. By the 1D Helly property for intervals,

   intersection_i I_i^{(k)} != emptyset

   for each k.

5. Choose c_k in intersection_i I_i^{(k)}.
6. Set v = (c_1,...,c_d).
7. Since every support coordinate lies within distance R of c_k in each axis,
   every support point lies in B_R(v).
8. Therefore

   supp(Phi(gamma)) subset B_R(v).

## Remaining obligation

Make precise the projection step from block-intersection supports to interval
families and verify the required overlap hypotheses.
