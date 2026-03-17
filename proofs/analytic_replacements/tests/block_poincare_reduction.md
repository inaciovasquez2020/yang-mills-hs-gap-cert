# Block Poincare Reduction

For a lattice cube B of side length L:

1. Let -Delta_B be the Neumann graph Laplacian on B.
2. For h = g - g_B, one has h orthogonal to constants.
3. By the spectral theorem,

   <h,(-Delta_B)h> >= lambda_1(B) ||h||^2.

4. If lambda_1(B) >= c L^{-2}, then

   ||g-g_B||^2 <= c^{-1} L^2 <g,(-Delta_B)g>.

5. Since

   <g,(-Delta_B)g> = sum_{ell subset B} ||∇_ell g||^2,

   the block Poincare inequality follows.

Remaining sublemma:
lambda_1(B) >= c L^{-2}.
