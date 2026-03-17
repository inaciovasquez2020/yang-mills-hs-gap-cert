# Analytic Block Poincare Proof Skeleton

## Statement

For every block B of side length L and every function g on B,

||g - g_B||_{L^2(B)}^2 <= C L^2 sum_{ell subset B} ||∇_ell g||^2

where

g_B = (1 / |B|) sum_{x in B} g(x).

## Proof skeleton

1. Write B as a finite induced subgraph of the lattice.
2. Let -Delta_B be the graph Laplacian on B with Neumann boundary convention.
3. Expand g - g_B in an orthonormal eigenbasis of -Delta_B.
4. The zero mode is removed by subtracting g_B.
5. Bound

   <g-g_B,(-Delta_B)(g-g_B)> >= lambda_1(B) ||g-g_B||^2.

6. Use the standard lattice estimate

   lambda_1(B) >= c L^{-2}.

7. Rearranging gives

   ||g-g_B||^2 <= c^{-1} L^2 <g,(-Delta_B)g>.

8. Identify

   <g,(-Delta_B)g> = sum_{ell subset B} ||∇_ell g||^2.

## Remaining obligation

Provide a self-contained proof that

lambda_1(B) >= c L^{-2}

for lattice cubes B.
