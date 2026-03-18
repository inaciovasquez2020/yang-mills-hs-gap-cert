# Block-Poincaré Scaling

## Objective
Empirically test the scaling
\[
\frac{\|f-\bar f\|_2^2}{\|\nabla f\|_2^2} \asymp L^2
\]
for one-dimensional block functions.

## Artifact
- `results/block_poincare/block_poincare_scaling.json`

## Acceptance
For tested block sizes \(L\), the normalized quantity
\[
\frac{1}{L^2}\frac{\|f-\bar f\|_2^2}{\|\nabla f\|_2^2}
\]
remains bounded away from \(0\) and \(\infty\).
